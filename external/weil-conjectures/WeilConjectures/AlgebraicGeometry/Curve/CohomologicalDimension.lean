/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.AffineGeneric
public import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimensionReduction
public import WeilConjectures.AlgebraicGeometry.Curve.GenericComparison
public import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The étale cohomological dimension of a curve

The étale cohomological dimension of a curve over an algebraically closed field is at most two,
and at most one if the curve is affine: `H^q(C_ét, F) = 0` for every torsion abelian sheaf `F`
(`CategoryTheory.Sheaf.IsTorsion`: every section is locally torsion, equivalently every
geometric stalk is a torsion group) and `q ≥ 3`, resp. `q ≥ 2`.

Neither statement needs smoothness, connectedness, or `char k` to be prime to the torsion of
`F`. The affine bound is first proved for smooth connected curves
(`AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_of_two_le_of_isAffine_of_smooth`), by
comparing a torsion sheaf with its pushforward from the generic point; the general case reduces
to it (`AlgebraicGeometry.IsCurve.subsingleton_sheafH_two_of_isAffine_of_forall`).

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`: `H^q(C, F) = 0` for `q ≥ 3`.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine`: `H^q(C, F) = 0` for
  `q ≥ 2` on an affine curve.
- `AlgebraicGeometry.IsConnectedCurve.sheafH_constantZMod_of_isAffine`: the Kummer computation
  of `H^q(C, ℤ/n)` on a smooth affine connected curve, for `n` prime to `char k`.
- `AlgebraicGeometry.subsingleton_sheafH_constantZMod_and_nonempty_addEquiv_sheafH_zero`: the
  cohomology of the constant sheaf `ℤ/d` on a smooth affine curve.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Etale TopologicalSpace Limits

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- An irreducible `T₀` space of dimension at most zero is a single point. -/
lemma subsingleton_of_topologicalKrullDim_le_zero {X : Type*} [TopologicalSpace X]
    [IrreducibleSpace X] [QuasiSober X] [T0Space X] (h : topologicalKrullDim X ≤ 0) :
    Subsingleton X := by
  refine ⟨fun x y ↦ ?_⟩
  have key (z : X) : closure {z} = (Set.univ : Set X) := by
    let A : IrreducibleCloseds X := ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
    let B : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    exact congr(($(IrreducibleCloseds.eq_of_le_of_topologicalKrullDim_le_zero h
      (show A ≤ B from Set.subset_univ _)) : Set X))
  refine (inseparable_iff_closure_eq.mpr ((key x).trans (key y).symm)).eq

/-- **One component of the reduction to smooth curves.** Let `Z` be an integral affine curve
over an algebraically closed field `k`, and assume that `H²` of torsion sheaves vanishes on
smooth affine connected curves over `k`. Then every torsion sheaf `G` on `Z` admits a finite
morphism `n : Y ⟶ Z`, an isomorphism over a nonempty open `W`, with `H²(Y, n^* G) = 0`: the
normalization if `Z` has dimension one, the identity if `Z` is a point. -/
lemma IsCurve.exists_isFinite_isIso_subsingleton_sheafH_two {Z : Scheme.{u}} [IsIntegral Z]
    [IsAffine Z] (g : Z ⟶ Spec (.of k)) [IsCurve g]
    (H : ∀ (C' : Scheme.{u}) (f' : C' ⟶ Spec (.of k)), IsConnectedCurve f' → Smooth f' →
      IsAffine C' → ∀ F' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1}, F'.IsTorsion →
        Subsingleton (Sheaf.H F' 2))
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion) :
    ∃ (Y : Scheme.{u}) (n : Y ⟶ Z) (_ : IsFinite n) (W : Z.Opens), (W : Set Z).Nonempty ∧
      IsIso (n ∣_ W) ∧ Subsingleton (Sheaf.H ((n)^*[AddCommGrpCat.{u + 1}].obj G) 2) := by
  by_cases hdim : topologicalKrullDim Z = 1
  · have := Z.isFinite_fromNormalization_of_locallyOfFiniteType g
    obtain ⟨W, hW, hiso⟩ := Z.exists_isIso_fromNormalization_restrict g
    refine ⟨Z.normalization, Z.fromNormalization, this, W, hW, hiso, ?_⟩
    have : Smooth (Z.fromNormalization ≫ g) := Scheme.smooth_fromNormalization_comp g hdim
    have : IsAffine Z.normalization := isAffine_of_isAffineHom Z.fromNormalization
    have : IsIntegral Z.normalization :=
      inferInstanceAs (IsIntegral Z.fromSpecFunctionField.normalization)
    have hdim' : topologicalKrullDim Z.normalization = 1 :=
      (Z.topologicalKrullDim_normalization g).trans hdim
    have : IsConnectedCurve (Z.fromNormalization ≫ g) :=
      { krullDim_le_one := hdim'.le
        connectedSpace := inferInstance
        krullDim_eq_one := hdim' }
    exact H _ _ this inferInstance inferInstance _ (isTorsion_upperStar _ hG)
  · refine ⟨Z, 𝟙 Z, inferInstance, ⊤, ⟨Classical.arbitrary Z, trivial⟩, ?_, ?_⟩
    · rw [morphismRestrict_id]
      exact IsIso.id _
    have h0 : topologicalKrullDim Z ≤ 0 := by
      have h1 : topologicalKrullDim Z < ((0 : ℕ) : WithBot ℕ∞) + 1 :=
        lt_of_le_of_ne (IsCurve.krullDim_le_one (f := g)) hdim
      exact ENat.WithBot.lt_add_one_iff.1 h1
    have : Subsingleton Z := subsingleton_of_topologicalKrullDim_le_zero h0
    let x : Z := Classical.arbitrary Z
    have hx : IsClosed ({x} : Set Z) := by
      rw [show ({x} : Set Z) = Set.univ from Set.eq_univ_of_forall fun y ↦ Subsingleton.elim y x]
      exact isClosed_univ
    have := Scheme.isAlgClosed_residueField_of_isClosed g x hx
    have := isClosed_singleton_iff_isClosedImmersion.mp hx
    have : Surjective (Z.fromSpecResidueField x) :=
      ⟨fun y ↦ ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
    have : IsIso (Z.fromSpecResidueField x) := isIso_of_isClosedImmersion_of_surjective _
    have hb := cohomologyMap_bijective (Z.fromSpecResidueField x)
      ((𝟙 Z)^*[AddCommGrpCat.{u + 1}].obj G) 2
    have := Scheme.subsingleton_H_of_isSepClosed (Z.residueField x)
      ((Z.fromSpecResidueField x)^*[AddCommGrpCat.{u + 1}].obj
        ((𝟙 Z)^*[AddCommGrpCat.{u + 1}].obj G)) 1
    exact hb.injective.subsingleton

/-- **Reduction to smooth connected curves, affine case `Spec R`.** This is
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_two_of_isAffine_of_forall` for `C = Spec R`.

Let `Zₚ = Spec (R ⧸ p)` be the irreducible components, for the finitely many minimal primes
`p`, and `νₚ : Yₚ ⟶ Spec R` their normalizations (or `Zₚ` itself if it is a point,
`AlgebraicGeometry.IsCurve.exists_isFinite_isIso_subsingleton_sheafH_two`). Away from the
finite set `S` of closed points where two components meet or where some `Yₚ ⟶ Zₚ` is not an
isomorphism, `Spec R` is the disjoint union of the open pieces `Vₚ` of the components, over which
`νₚ` is a universal homeomorphism. So the units assemble to a map `F ⟶ ⨁ₚ νₚ_* νₚ^* F` which is
an isomorphism away from `S`, hence bijective on `H²`
(`AlgebraicGeometry.Etale.bijective_H_map_of_isIso_upperStar_map`), and
`H²(Spec R, νₚ_* νₚ^* F) = H²(Yₚ, νₚ^* F) = 0`. -/
theorem IsCurve.subsingleton_sheafH_two_spec_of_forall {R : CommRingCat.{u}}
    (g : Spec R ⟶ Spec (.of k)) [IsCurve g]
    (F : Sheaf (Spec R).smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (H : ∀ (C' : Scheme.{u}) (f' : C' ⟶ Spec (.of k)), IsConnectedCurve f' → Smooth f' →
      IsAffine C' → ∀ F' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1}, F'.IsTorsion →
        Subsingleton (Sheaf.H F' 2)) :
    Subsingleton (Sheaf.H F 2) := by
  classical
  have : IsLocallyNoetherian (Spec R) := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.1 inferInstance
  let ι := ↥(minimalPrimes R)
  have : Finite ι := (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  have := Fintype.ofFinite ι
  have hprime (p : ι) : p.1.IsPrime := Ideal.IsMinimalPrime.isPrime p.2
  -- the irreducible components `Z p = Spec (R ⧸ p)`
  let Z (p : ι) : Scheme.{u} := Spec (.of (R ⧸ p.1))
  let c (p : ι) : Z p ⟶ Spec R := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.1))
  have hint (p : ι) : IsIntegral (Z p) := by
    have := hprime p
    exact inferInstanceAs (IsIntegral (Spec (.of (R ⧸ p.1))))
  have hcurve (p : ι) : IsCurve (c p ≫ g) :=
    { krullDim_le_one := ((c p).isClosedEmbedding.isInducing.topologicalKrullDim_le).trans
        (IsCurve.krullDim_le_one (f := g)) }
  have hrange (p : ι) : Set.range (c p).base = PrimeSpectrum.zeroLocus p.1 := by
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk p.1)) = _
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
  -- every point lies on a component
  have hcov (x : Spec R) : ∃ p : ι, x ∈ PrimeSpectrum.zeroLocus p.1 := by
    have := x.isPrime
    obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le
    exact ⟨⟨p, hp⟩, hpx⟩
  -- the components and their finite modifications
  choose Y n hn W hW hiso hY using fun p ↦ IsCurve.exists_isFinite_isIso_subsingleton_sheafH_two
    (c p ≫ g) H ((c p)^*[AddCommGrpCat.{u + 1}].obj F) (isTorsion_upperStar _ hF)
  -- the good locus of each component: where it meets no other component and `n p` is an iso
  let O (p : ι) : Set (Z p) := (W p : Set (Z p)) ∩
    ⋂ q ∈ Finset.univ.filter (· ≠ p), ((c p).base ⁻¹' PrimeSpectrum.zeroLocus q.1)ᶜ
  have hOopen (p : ι) : IsOpen (O p) := by
    refine (W p).isOpen.inter (isOpen_biInter_finset fun q _ ↦ ?_)
    exact ((PrimeSpectrum.isClosed_zeroLocus _).preimage (c p).continuous).isOpen_compl
  have hOne (p : ι) : (O p).Nonempty := by
    have := hprime p
    -- the generic point `(0)` of `Spec (R ⧸ p)`, lying over `p`
    let z₀ : Z p := ⟨⊥, Ideal.isPrime_bot⟩
    have hz₀ : ((c p).base z₀).asIdeal = p.1 := by
      change Ideal.comap (Ideal.Quotient.mk p.1) ⊥ = p.1
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    obtain ⟨w, hw⟩ := hW p
    refine ⟨z₀, ?_, ?_⟩
    · exact ((PrimeSpectrum.le_iff_specializes z₀ w).1 bot_le).mem_open (W p).isOpen hw
    · simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and]
      intro q hqp hmem
      have hle : q.1 ≤ p.1 := hz₀ ▸ hmem
      exact hqp (Subtype.ext (le_antisymm hle (p.2.2 ⟨hprime q, bot_le⟩ hle)))
  have hdimZ (p : ι) : topologicalKrullDim (Z p) ≤ 1 := IsCurve.krullDim_le_one (f := c p ≫ g)
  have hOfin (p : ι) : (O p)ᶜ.Finite :=
    (hOopen p).finite_compl_of_topologicalKrullDim_le_one (hdimZ p) (hOne p)
  have hOcl (p : ι) (z : Z p) (hz : z ∉ O p) : IsClosed ({z} : Set (Z p)) :=
    (hOopen p).isClosed_singleton_of_mem_compl (hdimZ p) (hOne p) hz
  -- the bad set `S`
  let S : Set (Spec R) := ⋃ p, (c p).base '' (O p)ᶜ
  have hSfin : S.Finite := Set.finite_iUnion fun p ↦ (hOfin p).image _
  have hScl (x : Spec R) (hx : x ∈ S) : IsClosed ({x} : Set (Spec R)) := by
    obtain ⟨p, z, hz, rfl⟩ := Set.mem_iUnion.1 hx
    simpa using (c p).isClosedEmbedding.isClosedMap _ (hOcl p z hz)
  have hSclosed : IsClosed S := by
    rw [← Set.biUnion_of_singleton S]
    exact hSfin.isClosed_biUnion hScl
  let U : (Spec R).Opens := ⟨Sᶜ, hSclosed.isOpen_compl⟩
  -- the pieces `V p` of `U`, away from the other components
  let V (p : ι) : (Spec R).Opens := ⟨Sᶜ ∩ ⋂ q ∈ Finset.univ.filter (· ≠ p),
    (PrimeSpectrum.zeroLocus q.1)ᶜ, hSclosed.isOpen_compl.inter
      (isOpen_biInter_finset fun q _ ↦ (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl)⟩
  have hVU (p : ι) : V p ≤ U := fun _ hx ↦ hx.1
  have hVZ (p : ι) (x : Spec R) (hx : x ∈ V p) : x ∈ Set.range (c p).base := by
    obtain ⟨q, hq⟩ := hcov x
    by_cases hqp : q = p
    · exact hqp ▸ (hrange q).symm ▸ hq
    · refine absurd hq ?_
      have := hx.2
      simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this q hqp
  have hVO (p : ι) (z : Z p) (hz : (c p).base z ∈ V p) : z ∈ O p := by
    by_contra h
    exact hz.1 (Set.mem_iUnion.2 ⟨p, z, h, rfl⟩)
  have hUV (x : Spec R) (hx : x ∈ U) : ∃ p, x ∈ V p := by
    obtain ⟨p, hp⟩ := hcov x
    refine ⟨p, hx, ?_⟩
    simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and]
    intro q hqp hxq
    obtain ⟨z, rfl⟩ : x ∈ Set.range (c p).base := (hrange p).symm ▸ hp
    refine hx (Set.mem_iUnion.2 ⟨p, z, fun hz ↦ ?_, rfl⟩)
    have := hz.2
    simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this q hqp hxq
  have hdisj (p q : ι) (hqp : q ≠ p) :
      Disjoint (Set.range (V p).ι.base) (Set.range (n q ≫ c q).base) := by
    rw [Scheme.Opens.range_ι, Set.disjoint_right]
    rintro _ ⟨y, rfl⟩ hy
    have := hy.2
    simp only [Set.mem_iInter, Finset.mem_filter, Finset.mem_univ, true_and] at this
    refine this q hqp ?_
    rw [← hrange q]
    exact ⟨(n q).base y, rfl⟩
  have huh (p : ι) : IsUniversalHomeomorphism ((n p ≫ c p) ∣_ V p) := by
    rw [morphismRestrict_comp]
    have : IsIso (n p ∣_ (c p ⁻¹ᵁ V p)) :=
      isIso_morphismRestrict_of_le (n p) (fun z hz ↦ (hVO p z hz).1) (hiso p)
    have : Surjective (c p ∣_ V p) := by
      refine ⟨fun y ↦ ?_⟩
      obtain ⟨z, hz⟩ := hVZ p y.1 y.2
      refine ⟨⟨z, show (c p).base z ∈ V p from hz ▸ y.2⟩, Subtype.ext ?_⟩
      exact (morphismRestrict_base_coe _ _ _).trans hz
    have : IsClosedImmersion (c p ∣_ V p) :=
      IsZariskiLocalAtTarget.restrict (inferInstanceAs (IsClosedImmersion (c p))) _
    have h1 : IsUniversalHomeomorphism (n p ∣_ (c p ⁻¹ᵁ V p)) := { }
    have h2 : IsUniversalHomeomorphism (c p ∣_ V p) := inferInstance
    exact @IsUniversalHomeomorphism.comp _ _ _ _ _ h1 h2
  -- the comparison map `F ⟶ ⨁ₚ νₚ_* νₚ^* F`
  have : HasFiniteBiproducts (Sheaf (Spec R).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let ν (p : ι) : Y p ⟶ Spec R := n p ≫ c p
  let adj (p : ι) := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (ν p)
  let G (p : ι) : Sheaf (Spec R).smallEtaleTopology AddCommGrpCat.{u + 1} :=
    (ν p)_*[AddCommGrpCat.{u + 1}].obj ((ν p)^*[AddCommGrpCat.{u + 1}].obj F)
  let φ : F ⟶ ⨁ G := biproduct.lift fun p ↦ (adj p).unit.app F
  have hG (p : ι) : Subsingleton (Sheaf.H (G p) 2) := by
    have : Subsingleton ((Sheaf.functorH (Y p).smallEtaleTopology 2).obj
      (((c p)^*[AddCommGrpCat.{u + 1}] ⋙ (n p)^*[AddCommGrpCat.{u + 1}]).obj F)) := hY p
    have : Subsingleton (Sheaf.H ((ν p)^*[AddCommGrpCat.{u + 1}].obj F) 2) :=
      ((Sheaf.functorH _ 2).mapIso ((upperStarComp AddCommGrpCat.{u + 1} (n p) (c p)).app
        F)).addCommGroupIsoToAddEquiv.toEquiv.subsingleton
    have : Subsingleton (Sheaf.H ((𝟭 (Sheaf (Y p).smallEtaleTopology AddCommGrpCat.{u + 1})).obj
        ((ν p)^*[AddCommGrpCat.{u + 1}].obj F)) 2) := this
    exact (bijective_edgeMap_of_isFinite (ν p) _ 2).injective.subsingleton
  have hφ : IsIso ((U.ι)^*[AddCommGrpCat.{u + 1}].map φ) := by
    refine isIso_of_isIso_upperStar_map_of_jointlySurjective AddCommGrpCat.{u + 1}
      (fun p ↦ (Spec R).homOfLE (hVU p)) (fun x ↦ ?_) _ fun p ↦ ?_
    · obtain ⟨p, hp⟩ := hUV x.1 x.2
      exact ⟨p, ⟨x.1, hp⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
    have e := upperStarComp AddCommGrpCat.{u + 1} ((Spec R).homOfLE (hVU p)) U.ι (V p).ι
      (Scheme.homOfLE_ι _ _).symm
    change IsIso (((U.ι)^*[AddCommGrpCat.{u + 1}] ⋙
      ((Spec R).homOfLE (hVU p))^*[AddCommGrpCat.{u + 1}]).map φ)
    rw [← NatIso.isIso_map_iff e φ]
    let P := ((V p).ι)^*[AddCommGrpCat.{u + 1}]
    have hz (q : ι) (hqp : q ≠ p) : IsZero (P.obj (G q)) :=
      isZero_upperStar_lowerStar_of_disjoint_range _ (V p).ι (ν q) (hdisj p q hqp) _
    have hπ : IsIso (P.map (biproduct.π G p)) := by
      refine ⟨P.map (biproduct.ι G p), ?_, ?_⟩
      · rw [← P.map_comp, ← P.map_id, ← IsBilimit.total (biproduct.isBilimit G), P.map_sum,
          Finset.sum_eq_single p (fun q _ hqp ↦ ?_) (by simp)]
        rw [P.map_comp, (hz q hqp).eq_zero_of_tgt (P.map (biproduct.π G q)), zero_comp]
      · rw [← P.map_comp, biproduct.ι_π_self, P.map_id]
    have : IsUniversalHomeomorphism (ν p ∣_ V p) := huh p
    have hunit : IsIso (P.map ((adj p).unit.app F)) :=
      isIso_upperStar_map_unit_of_isUniversalHomeomorphism (ν p) (V p) F
    have : IsIso (P.map φ ≫ P.map (biproduct.π G p)) := by
      rw [← P.map_comp, biproduct.lift_π]
      exact hunit
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hπ this
  have hSU : (U : Set (Spec R))ᶜ = S := compl_compl S
  have hsep (x : Spec R) (hx : x ∉ U) : IsSepClosed ((Spec R).residueField x) := by
    have := Scheme.isAlgClosed_residueField_of_isClosed g x (hScl x (hSU ▸ hx))
    infer_instance
  have hb := bijective_H_map_of_isIso_upperStar_map U (hSU ▸ hSfin)
    (fun x hx ↦ hScl x (hSU ▸ hx)) hsep φ hφ 0
  have : Subsingleton (Sheaf.H (⨁ G) 2) :=
    (Abelian.Ext.addEquivBiproduct _ (biproduct.isBilimit G) 2).toEquiv.subsingleton
  exact hb.injective.subsingleton

end AlgebraicGeometry

namespace AlgebraicGeometry.IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Generic replacement in degrees at least two.** Let `C` be a smooth integral curve over an
algebraically closed field `k`, with generic point `η : Spec k(C) ⟶ C`, and `F` a torsion étale
sheaf on `C`. Then the unit `F ⟶ η_* η^* F` induces isomorphisms `Hᵠ(C, F) ≅ Hᵠ(C, η_* η^* F)` for
`q ≥ 2`: its kernel and cokernel have zero generic restriction, hence are supported on finitely
many closed points and have no cohomology in positive degrees.
(blueprint: `theorem-cohomology-curves`) -/
theorem isIso_functorH_map_unit_fromSpecFunctionField (f : C ⟶ Spec (.of k)) [IsCurve f]
    [Smooth f] [IsIntegral C] (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (_hF : F.IsTorsion) (q : ℕ) (hq : 2 ≤ q) :
    IsIso ((Sheaf.functorH _ q).map
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        C.fromSpecFunctionField).unit.app F)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hq
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_H_map_unit_fromSpecFunctionField f F n)

/-- **Reduction to smooth connected curves.** Let `C` be an affine curve over an algebraically
closed field `k`. If `H²(C', F') = 0` for every smooth affine connected curve `C'` over `k` and
every torsion sheaf `F'` on `C'`, then `H²(C, F) = 0` for every torsion sheaf `F` on `C`.

Cohomology of the quasi-compact quasi-separated scheme `C` commutes with filtered colimits, so
`F` may be taken constructible. A constructible sheaf embeds into a finite sum of sheaves
`π_* M` with `π : C' ⟶ C` finite and `M` a finite constant sheaf, with constructible cokernel;
since `π_*` is exact, a dimension shift reduces the claim to `F = ℤ/n`. Passing to the reduced
connected components and then to the normalization, which changes `F` only by a sheaf supported
on finitely many closed points, reduces it to smooth affine connected `C`.
(blueprint: `theorem-cohomology-curves`, the reduction step) -/
theorem subsingleton_sheafH_two_of_isAffine_of_forall (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsAffine C] (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (H : ∀ (C' : Scheme.{u}) (f' : C' ⟶ Spec (.of k)), IsConnectedCurve f' → Smooth f' →
      IsAffine C' → ∀ F' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1}, F'.IsTorsion →
        Subsingleton (Sheaf.H F' 2)) :
    Subsingleton (Sheaf.H F 2) := by
  have : IsCurve (C.isoSpec.inv ≫ f) :=
    { krullDim_le_one := C.isoSpec.inv.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans
        (IsCurve.krullDim_le_one (f := f)) }
  have := subsingleton_sheafH_two_spec_of_forall (C.isoSpec.inv ≫ f)
    ((Etale.upperStar AddCommGrpCat.{u + 1} C.isoSpec.inv).obj F) (Etale.isTorsion_upperStar _ hF) H
  exact (Etale.cohomologyMap_bijective C.isoSpec.inv F 2).injective.subsingleton

end IsCurve

namespace IsConnectedCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Second cohomology of a smooth affine curve.** Let `C` be a smooth affine connected curve
over an algebraically closed field `k`. Then `H²(C_ét, F) = 0` for every torsion abelian sheaf
`F` on `C_ét`: `H²(C, F) ≅ H²(C, η_* η^* F)` for the generic point `η` of `C`
(`AlgebraicGeometry.IsCurve.isIso_functorH_map_unit_fromSpecFunctionField`), and the latter
vanishes by `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar`. -/
theorem subsingleton_sheafH_two_of_isAffine_of_smooth (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) :
    Subsingleton (Sheaf.H F 2) := by
  have := IsConnectedCurve.connectedSpace (f := f)
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : IsReduced C := isReduced_of_isReduced_stalk C
  have : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced C
  have := IsCurve.isIso_functorH_map_unit_fromSpecFunctionField f F hF 2 le_rfl
  let ε := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} C.fromSpecFunctionField).unit
  have : Subsingleton ((Sheaf.functorH _ 2).obj ((Etale.upperStar AddCommGrpCat.{u + 1}
      C.fromSpecFunctionField ⋙ Etale.lowerStar AddCommGrpCat.{u + 1}
        C.fromSpecFunctionField).obj F)) :=
    subsingleton_sheafH_two_lowerStar f _ (Etale.isTorsion_upperStar C.fromSpecFunctionField hF)
  exact (asIso ((Sheaf.functorH _ 2).map (ε.app F))).addCommGroupIsoToAddEquiv.subsingleton

end IsConnectedCurve

namespace IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Second cohomology of an affine curve.** Let `C` be an affine curve over an algebraically
closed field `k`. Then `H²(C_ét, F) = 0` for every torsion abelian sheaf `F`: this reduces
(`AlgebraicGeometry.IsCurve.subsingleton_sheafH_two_of_isAffine_of_forall`) to smooth affine
connected curves, where it is
`AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_of_isAffine_of_smooth`. -/
theorem subsingleton_sheafH_two_of_isAffine (f : C ⟶ Spec (.of k)) [IsCurve f] [IsAffine C]
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) :
    Subsingleton (Sheaf.H F 2) :=
  subsingleton_sheafH_two_of_isAffine_of_forall f F hF fun _ f' _ _ _ F' hF' ↦
    IsConnectedCurve.subsingleton_sheafH_two_of_isAffine_of_smooth f' F' hF'

/-- **Vanishing in high degrees.** Let `C` be a curve over an algebraically closed field `k`.
Then `H^q(C_ét, F) = 0` for `q ≥ 3` and every torsion abelian sheaf `F` on `C_ét`: the étale
cohomological dimension of a curve over an algebraically closed field is at most two. The
sharper bound for affine `C` is
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine`.

The proof reduces to integral curves
(`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le_generic`, blueprint
`theorem-cohomology-curves`, Step 1): the units `F ⟶ cₚ_* cₚ^* F` for the irreducible components
`cₚ : Zₚ ⟶ C` with their reduced structure assemble to a map `F ⟶ ⨁ₚ cₚ_* cₚ^* F` which is an
isomorphism away from finitely many closed points, hence bijective on `Hᵠ` for `q ≥ 2`. On an
integral curve the vanishing is the generic-point argument of
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le_of_isIntegral`: `Hᵠ(C, F)` agrees
with `Hᵠ(C, η_* η^* F)` for the generic point `η`, and the function field has cohomological
dimension at most one. (blueprint: `theorem-cohomology-curves`) -/
@[stacks 03SC "(1)"]
theorem subsingleton_sheafH_of_three_le (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 3 ≤ q) : Subsingleton (Sheaf.H F q) :=
  subsingleton_sheafH_of_three_le_generic f F hF q hq

end IsCurve

namespace IsConnectedCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Cohomological dimension of a smooth affine curve.** Let `C` be a smooth affine connected
curve over an algebraically closed field `k`. Then `H^q(C_ét, F) = 0` for `q ≥ 2` and every
torsion abelian sheaf `F` on `C_ét`.

Degrees `q ≥ 3` are `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`. In degree two,
`H²(C, F) ≅ H²(C, η_* η^* F)` for the generic point `η` of `C`
(`AlgebraicGeometry.IsCurve.isIso_functorH_map_unit_fromSpecFunctionField`), and the latter
vanishes by `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar`.
(blueprint: `theorem-cohomology-curves--2`) -/
theorem subsingleton_sheafH_of_two_le_of_isAffine_of_smooth (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 2 ≤ q) : Subsingleton (Sheaf.H F q) := by
  obtain rfl | hq := hq.eq_or_lt
  · exact subsingleton_sheafH_two_of_isAffine_of_smooth f F hF
  · exact IsCurve.subsingleton_sheafH_of_three_le f F hF q hq

end IsConnectedCurve

namespace IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Cohomological dimension of an affine curve.** Let `C` be an affine curve over an
algebraically closed field `k`. Then `H^q(C_ét, F) = 0` for `q ≥ 2` and every torsion abelian
sheaf `F` on `C_ét`: the étale cohomological dimension of an affine curve over an
algebraically closed field is at most one.

Degrees `q ≥ 3` are `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`. Degree two
reduces (`AlgebraicGeometry.IsCurve.subsingleton_sheafH_two_of_isAffine_of_forall`) to smooth
affine connected curves, where it is
`AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_of_two_le_of_isAffine_of_smooth`.
(blueprint: `theorem-cohomology-curves`) -/
@[stacks 03SC "(2)"]
theorem subsingleton_sheafH_of_two_le_of_isAffine (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsAffine C] (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (q : ℕ) (hq : 2 ≤ q) : Subsingleton (Sheaf.H F q) := by
  obtain rfl | hq := hq.eq_or_lt
  · exact subsingleton_sheafH_two_of_isAffine f F hF
  · exact subsingleton_sheafH_of_three_le f F hF q hq

end IsCurve

/-- The constant sheaf `ℤ/d` with `d ≠ 0` is a torsion sheaf: its sections are killed by
`d`. -/
lemma Scheme.isTorsion_constantZMod (X : Scheme.{u}) {d : ℕ} (hd : d ≠ 0) :
    (X.constantZMod d).IsTorsion := by
  refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U s ↦ ?_
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨d, Nat.pos_of_ne_zero hd, ?_⟩
  have h₀ : d • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))) = 0 := by
    ext x
    simp
  have h₁ : d • 𝟙 (X.constantZMod d) = 0 := by
    rw [← (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_id,
      ← Functor.map_nsmul, h₀, Functor.map_zero]
  have h₂ := congrArg (fun φ ↦ ((sheafToPresheaf _ _).map φ).app U) h₁
  simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, NatTrans.app_zero] at h₂
  simpa using congrArg (fun g ↦ g.hom s) h₂

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- Blueprint `theorem-cohomology-curves--2`: Affine-curve cohomological
dimension.

Let `k` be algebraically closed, let `C` be a smooth affine curve over `k` and let `d ≥ 1`.
Then `H^q(C_ét, ℤ/d) = 0` for `q > 1`, and `H^0(C_ét, ℤ/d) = ℤ/d` when `C` is connected.

The vanishing is the case of the torsion sheaf `ℤ/d` of
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine` (blueprint
`theorem-cohomology-curves`), which does not need `d` to be prime to the characteristic; the degree
zero statement is `AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_zero_constantZMod`. -/
@[stacks 03SC "(2)"]
theorem subsingleton_sheafH_constantZMod_and_nonempty_addEquiv_sheafH_zero
    (f : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [IsAffine C] {d : ℕ} (hd : d ≠ 0) :
    (∀ q, 1 < q → Subsingleton (Sheaf.H (C.constantZMod d) q)) ∧
      (ConnectedSpace C → Nonempty (Sheaf.H (C.constantZMod d) 0 ≃+ ZMod d)) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsCurve f :=
    { toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      krullDim_le_one := by
        simpa using topologicalKrullDim_le_of_smoothOfRelativeDimension f 1 }
  exact ⟨fun q hq ↦ IsCurve.subsingleton_sheafH_of_two_le_of_isAffine f _
    (C.isTorsion_constantZMod hd) q hq, fun _ ↦ C.nonempty_addEquiv_sheafH_zero_constantZMod d⟩

/-- **Kummer computation on an affine curve.** Let `C` be a smooth affine connected curve over an
algebraically closed field `k` and `n ≥ 1` prime to `char k`. Then

* `H⁰(C_ét, ℤ/n) ≅ ℤ/n`;
* `𝒪(C)ˣ / 𝒪(C)ˣⁿ` is finite;
* there is a short exact sequence `0 → 𝒪(C)ˣ / 𝒪(C)ˣⁿ → H¹(C_ét, ℤ/n) → Pic(C)[n] → 0`, with
  `Pic(C) = H¹(C_ét, 𝔾ₘ)`;
* `Pic(C)[n]` is finite;
* `H^q(C_ét, ℤ/n) = 0` for `q > 1`.

A primitive `n`-th root of unity identifies `ℤ/n` with `μₙ`
(`AlgebraicGeometry.Scheme.constantZModIsoRootsOfUnitySheaf`), and the Kummer sequence together
with `Br(C) = 0`
(`AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_of_connectedSpace`)
gives the sequence for `H¹` (`AlgebraicGeometry.IsCurve.sheafH_rootsOfUnitySheaf_of_subsingleton`).
The finiteness statements are `AlgebraicGeometry.IsConnectedCurve.finite_units_quotient` and
`AlgebraicGeometry.IsConnectedCurve.surjective_zsmul_pic_and_finite_torsionBy`, and the vanishing
is `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine`.
(blueprint: `proposition-cohomology-smooth-affine-curve--2`) -/
theorem IsConnectedCurve.sheafH_constantZMod_of_isAffine (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsAffine C] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 0 ≃+ ZMod n) ∧
      Finite (Additive Γ(C, ⊤)ˣ ⧸ (zsmulAddGroupHom (α := Additive Γ(C, ⊤)ˣ) n).range) ∧
      (∃ (α : Additive Γ(C, ⊤)ˣ →+ Sheaf.H (C.constantZMod n) 1)
        (β : Sheaf.H (C.constantZMod n) 1 →+ C.CohomologicalPicardGroup),
        α.ker = (zsmulAddGroupHom (α := Additive Γ(C, ⊤)ˣ) (n : ℤ)).range ∧
          Function.Exact α β ∧ β.range = AddSubgroup.torsionBy C.CohomologicalPicardGroup n) ∧
      Finite (AddSubgroup.torsionBy C.CohomologicalPicardGroup n) ∧
      ∀ q, 1 < q → Subsingleton (Sheaf.H (C.constantZMod n) q) := by
  have := IsConnectedCurve.connectedSpace (f := f)
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have : NeZero (n : k) := ⟨hn⟩
  have : NeZero n := ⟨hn0⟩
  obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k n
  have e := ((Sheaf.functorH _ 1).mapIso
    (C.constantZModIsoRootsOfUnitySheaf n f hζ)).addCommGroupIsoToAddEquiv
  have hBr := IsCurve.subsingleton_cohomologicalBrauerGroup_of_connectedSpace f
  obtain ⟨⟨α, β, hα, hαβ, hβ⟩, -⟩ := IsCurve.sheafH_rootsOfUnitySheaf_of_subsingleton f n hn hBr
  obtain ⟨ePic⟩ := C.nonempty_addEquiv_cohomologicalPicardGroup
  have hfin := (surjective_zsmul_pic_and_finite_torsionBy f hn).2
  refine ⟨C.nonempty_addEquiv_sheafH_zero_constantZMod n,
    finite_units_quotient f n (Nat.pos_of_ne_zero hn0),
    ⟨e.symm.toAddMonoidHom.comp α, β.comp e.toAddMonoidHom, ?_, ?_, ?_⟩, ?_,
    fun q hq ↦ IsCurve.subsingleton_sheafH_of_two_le_of_isAffine f _
      (C.isTorsion_constantZMod hn0) q hq⟩
  · rw [← hα]
    ext x
    exact e.symm.map_eq_zero_iff
  · intro y
    refine (hαβ (e y)).trans ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩⟩
    · change e.symm (α x) = y
      rw [hx]
      exact e.symm_apply_apply y
    · change e.symm (α x) = y at hx
      rw [← hx]
      exact (e.apply_symm_apply _).symm
  · rw [← hβ]
    ext y
    refine ⟨fun ⟨x, hx⟩ ↦ ⟨e x, hx⟩, fun ⟨x, hx⟩ ↦ ⟨e.symm x, ?_⟩⟩
    change β (e (e.symm x)) = y
    rw [e.apply_symm_apply x, hx]
  · refine Finite.of_injective (β := AddSubgroup.torsionBy (Additive C.Pic) n)
      (fun x ↦ ⟨ePic.symm x, (Submodule.mem_torsionBy_iff _ _).2 ?_⟩) fun x y hxy ↦ ?_
    · rw [← map_zsmul, (Submodule.mem_torsionBy_iff _ _).1 x.2, map_zero]
    · exact Subtype.ext (ePic.symm.injective (congrArg Subtype.val hxy))

end AlgebraicGeometry
