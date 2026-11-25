/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.GenericPoint
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.Leray
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.Support
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.ProjectiveLine

/-!
# The affine Artin bound for affine space

Let `K` be an algebraically closed field, `c ≥ 1`, and assume the affine Artin bound in all
dimensions `≤ c` (`AlgebraicGeometry.Scheme.ArtinBound`). Then the affine space
`𝔸ᶜ⁺¹_K = 𝔸¹_B`, `B = 𝔸ᶜ_K`, has torsion cohomological dimension at most `c + 1`
(`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_affineLine_mvPolynomial`).

## Implementation details

This is the inductive step of the affine Artin vanishing theorem. For a sheaf `M` killed by an
integer, the Leray spectral sequence of `f : 𝔸¹_B ⟶ B` reduces the claim to
`Hᵖ(B, Rᵠf_* M) = 0` for `p + q > c + 1`. For `q ≤ 1` this is the bound on `B`. For `q ≥ 2` the
geometric stalks of `Rᵠf_* M` vanish at points of transcendence degree `> c + 1 - q`: for
`q = 2` by the computation at the generic point
(`AlgebraicGeometry.AffineSpace.isZero_upperStar_rightDerived_lowerStar_of_generic`), and for
`q ≥ 3` by the Grothendieck spectral sequence of `f = g ∘ j`, `j : 𝔸¹_B ⟶ ℙ¹_B`,
`g : ℙ¹_B ⟶ B`, together with proper base change for `g` and the stalks at infinity of the
`Rᵠj_* M`
(`AlgebraicGeometry.ProjectiveLine.isZero_upperStar_infinity_rightDerived_lowerStar_affineChart`).
Sheaves with this property have no cohomology above degree `c + 1 - q`
(`AlgebraicGeometry.Etale.subsingleton_H_of_isZero_upperStar_of_lt_residueFieldTrdeg`). A
general torsion sheaf is the filtered union of its subsheaves killed by an integer.
-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

namespace AlgebraicGeometry

open Scheme Etale

/-- An additive functor preserves the property of being killed by an integer. -/
lemma _root_.CategoryTheory.Functor.nsmul_id_obj_eq_zero {C D : Type*} [Category* C]
    [Category* D] [Preadditive C] [Preadditive D] (G : C ⥤ D) [G.Additive] {X : C} {n : ℕ}
    (h : n • 𝟙 X = 0) : n • 𝟙 (G.obj X) = 0 := by
  rw [← G.map_id, ← G.map_nsmul, h, G.map_zero]

/-- A sheaf which is a zero object has no cohomology. -/
lemma Etale.subsingleton_sheafH_of_isZero {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u + 1}] [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    {N : Sheaf J AddCommGrpCat.{u + 1}} (hN : IsZero N) (p : ℕ) : Subsingleton (Sheaf.H N p) :=
  ⟨fun x y ↦ by
    rw [← Abelian.Ext.comp_mk₀_id x, ← Abelian.Ext.comp_mk₀_id y, hN.eq_of_src (𝟙 N) 0,
      Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero, Abelian.Ext.comp_zero]⟩

/-- An abelian étale sheaf whose stalks at all geometric points vanish is zero. -/
lemma Etale.isZero_of_forall_isZero_upperStar_algClosurePoint_addCommGrp {T : Scheme.{u}}
    (N : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (H : ∀ t : T, IsZero ((T.algClosurePoint t)^*[AddCommGrpCat.{u + 1}].obj N)) :
    IsZero N := by
  have hz : IsZero (0 : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) := isZero_zero _
  have : IsIso (hz.from_ N) := by
    refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective AddCommGrpCat.{u + 1}
      (fun t ↦ T.algClosurePoint t)
      (fun t ↦ ⟨t, IsLocalRing.closedPoint _, Scheme.algClosurePoint_base _ _ _⟩) _
      fun t ↦ ?_
    have hz' : IsZero ((T.algClosurePoint t)^*[AddCommGrpCat.{u + 1}].obj 0) :=
      Functor.map_isZero _ hz
    exact ⟨⟨hz'.to_ _, (H t).eq_of_src _ _, hz'.eq_of_src _ _⟩⟩
  exact IsZero.of_iso hz (asIso (hz.from_ N))

/-- If `a < t` then `q + a < q + t`, for natural `q, a` and a cardinal `t`. -/
lemma _root_.Cardinal.natCast_add_lt_add {q a : ℕ} {t : Cardinal} (h : (a : Cardinal) < t) :
    ((q + a : ℕ) : Cardinal) < q + t := by
  rcases lt_or_ge t Cardinal.aleph0 with ht | ht
  · obtain ⟨m, rfl⟩ := Cardinal.lt_aleph0.1 ht
    norm_cast at h ⊢
    omega
  · exact (Cardinal.natCast_lt_aleph0).trans_le (ht.trans le_add_self)

/-- **Stalks of the higher direct images of the affine line.** Let `K` be a field,
`B = Spec K[y₁, …, y_c]`, `f : 𝔸¹_B ⟶ B` the projection, and assume the affine Artin bound in
dimensions `≤ c`. Let `M` be an abelian étale sheaf on `𝔸¹_B` killed by `n > 0` and `q ≥ 2`.
Then the stalk of `Rᵠf_* M` at a geometric point `s` of `B` vanishes as soon as
`c + 1 < q + trdeg_K κ(s)`. -/
theorem isZero_upperStar_rightDerived_lowerStar_affineLine {K : Type u} [Field K] {c : ℕ}
    (IH : ∀ e < c + 1, ArtinBound.{u} e)
    (M : Sheaf 𝔸(PUnit.{u + 1}; Spec (.of (MvPolynomial (Fin c) K))).smallEtaleTopology
      AddCommGrpCat.{u + 1}) {n : ℕ} (hn : 0 < n) (hM : n • 𝟙 M = 0) (q : ℕ) (hq : 2 ≤ q)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin c) K)))
    (hs : ((c + 1 : ℕ) : Cardinal.{u}) < q + residueFieldTrdeg
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin c) K))))
      (s (IsLocalRing.closedPoint Ω))) :
    IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj
      ((((𝔸(PUnit.{u + 1}; Spec (.of (MvPolynomial (Fin c) K))) ↘
        Spec (.of (MvPolynomial (Fin c) K)))_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj M)) := by
  let B : Scheme.{u} := Spec (.of (MvPolynomial (Fin c) K))
  have hMt : M.IsTorsion := isTorsion_of_nsmul_id_eq_zero hn hM
  obtain rfl | hq3 := eq_or_lt_of_le hq
  · refine AffineSpace.isZero_upperStar_rightDerived_lowerStar_of_generic M hMt 2 le_rfl s ?_
    set t := residueFieldTrdeg (Spec.map (CommRingCat.ofHom
      (algebraMap K (MvPolynomial (Fin c) K)))) (s (IsLocalRing.closedPoint Ω))
    rcases lt_or_ge t Cardinal.aleph0 with ht | ht
    · obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 ht
      rw [hm] at hs ⊢
      norm_cast at hs ⊢
      omega
    · exact (Cardinal.natCast_lt_aleph0).le.trans ht
  rw [← ProjectiveLine.affineChart_over]
  refine isZero_upperStar_rightDerived_lowerStar_comp_of_forall_add_eq _ _ s M q
    fun p q' hpq ↦ ?_
  let j := ProjectiveLine.affineChart B
  let g := ProjectiveLine B ↘ B
  let i := ProjectiveLine.infinity B
  rcases q' with _ | q'
  · exact ProjectiveLine.isZero_upperStar_rightDerived_lowerStar_of_two_lt B _
      (isTorsion_of_nsmul_id_eq_zero hn
        ((((j)_*[AddCommGrpCat.{u + 1}]).rightDerived 0).nsmul_id_obj_eq_zero hM)) s p
      (by omega)
  have := ProjectiveLine.isIso_unit_app_rightDerived_lowerStar_affineChart B M (q' + 1)
    (by omega)
  let Y := (((j)_*[AddCommGrpCat.{u + 1}]).rightDerived (q' + 1)).obj M
  let e : Y ≅ ((i)_*[AddCommGrpCat.{u + 1}]).obj ((i)^*[AddCommGrpCat.{u + 1}].obj Y) :=
    asIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit.app Y)
  rcases p with _ | p
  · have e' : (((g)_*[AddCommGrpCat.{u + 1}]).rightDerived 0).obj Y ≅
        (i)^*[AddCommGrpCat.{u + 1}].obj Y :=
      (Functor.rightDerivedZeroIsoSelf _).app Y ≪≫ ((g)_*[AddCommGrpCat.{u + 1}]).mapIso e ≪≫
        (lowerStarComp AddCommGrpCat.{u + 1} i g (𝟙 B) (by simp [i, g])).app _ ≪≫
        (lowerStarId AddCommGrpCat.{u + 1} B).app _
    refine IsZero.of_iso ?_ ((s)^*[AddCommGrpCat.{u + 1}].mapIso e' ≪≫
      (upperStarComp AddCommGrpCat.{u + 1} s i).symm.app Y)
    exact ProjectiveLine.isZero_upperStar_infinity_rightDerived_lowerStar_affineChart IH M hMt
      (q' + 1) (by omega) s (by rwa [show q' + 1 = q by omega])
  · refine Functor.map_isZero _ (IsZero.of_iso ?_
      ((((g)_*[AddCommGrpCat.{u + 1}]).rightDerived (p + 1)).mapIso e))
    exact ProjectiveLine.isZero_rightDerived_lowerStar_obj_lowerStar_infinity B _ (p + 1)
      (by omega)

/-- A torsion cohomological dimension bound for sheaves killed by an integer implies the bound
for all torsion sheaves, on a quasi-compact quasi-separated scheme: a torsion sheaf is the
filtered union of its subsheaves killed by an integer, and cohomology commutes with filtered
colimits. -/
lemma Scheme.hasTorsionCohomologicalDimensionLE_of_nsmul {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {d : ℕ}
    (h : ∀ (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ), 0 < n →
      n • 𝟙 M = 0 → ∀ m : ℕ, d < m → Subsingleton (Sheaf.H M m)) :
    X.HasTorsionCohomologicalDimensionLE d := by
  intro F hF m hm
  obtain ⟨D, cc, hcc, hpt, hD⟩ := hF.exists_isColimit_nsmul_eq_zero F
  subst hpt
  refine ⟨fun x y ↦ ?_⟩
  have hzero (z : Sheaf.H cc.pt m) : z = 0 := by
    obtain ⟨j, z', rfl⟩ := (Scheme.H_map_isColimit_of_isFiltered_of_large X hcc m).1 z
    obtain ⟨n, hn, hDn⟩ := hD j
    have := h (D.obj j) n hn hDn m hm
    rw [Subsingleton.elim z' 0, map_zero]
  rw [hzero x, hzero y]

/-- **The affine Artin bound for affine space.** Let `K` be an algebraically closed field and
assume the affine Artin bound in all dimensions `≤ c`. Then `cd_tor(𝔸¹_B) ≤ c + 1` for
`B = Spec K[y₁, …, y_c]`. -/
theorem Scheme.hasTorsionCohomologicalDimensionLE_affineLine_mvPolynomial {K : Type u}
    [Field K] [IsAlgClosed K] {c : ℕ} (IH : ∀ e < c + 1, ArtinBound.{u} e) :
    (𝔸(PUnit.{u + 1}; Spec (.of (MvPolynomial (Fin c) K)))).HasTorsionCohomologicalDimensionLE
      (c + 1) := by
  let A := MvPolynomial (Fin c) K
  let B : Scheme.{u} := Spec (.of A)
  let b : B ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K A))
  have hb : LocallyOfFiniteType b := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have hK0 := hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed K
  have hdimB : topologicalKrullDim B ≤ (c : WithBot ℕ∞) := by
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans_le ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp
  have hcdB : B.HasTorsionCohomologicalDimensionLE c := by
    simpa using IH c (by omega) K 0 hK0 B b hb inferInstance hdimB
  refine hasTorsionCohomologicalDimensionLE_of_nsmul fun M n hn hM m hm ↦ ?_
  refine subsingleton_H_of_forall_add_eq (𝔸(PUnit.{u + 1}; B) ↘ B) M m fun p q hpq ↦ ?_
  let N := (((𝔸(PUnit.{u + 1}; B) ↘ B)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj M
  have hNn : n • 𝟙 N = 0 := Functor.nsmul_id_obj_eq_zero _ hM
  have hNt : N.IsTorsion := isTorsion_of_nsmul_id_eq_zero hn hNn
  by_cases hq1 : q ≤ 1
  · exact hcdB N hNt p (by omega)
  by_cases hqc : q ≤ c + 1
  · refine subsingleton_H_of_isZero_upperStar_of_lt_residueFieldTrdeg b (c + 1 - q)
      (fun Z i hi hZ ↦ ?_) N hNt (fun Ω _ _ s hs ↦ ?_) p (by omega)
    · have : IsAffine Z := isAffine_of_isAffineHom i
      simpa using IH (c + 1 - q) (by omega) K 0 hK0 Z (i ≫ b) inferInstance inferInstance hZ
    · refine isZero_upperStar_rightDerived_lowerStar_affineLine IH M hn hM q (by omega) s ?_
      have := Cardinal.natCast_add_lt_add (q := q) hs
      rwa [show q + (c + 1 - q) = c + 1 by omega] at this
  · refine Etale.subsingleton_sheafH_of_isZero
      (isZero_of_forall_isZero_upperStar_algClosurePoint_addCommGrp N fun t ↦ ?_) p
    refine isZero_upperStar_rightDerived_lowerStar_affineLine IH M hn hM q (by omega) _ ?_
    exact (show ((c + 1 : ℕ) : Cardinal.{u}) < q by norm_cast; omega).trans_le le_self_add

end AlgebraicGeometry
