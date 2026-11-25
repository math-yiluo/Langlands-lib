/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinVanishing.StalkFormula
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
public import WeilConjectures.AlgebraicGeometry.Sites.LerayVanishing
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationField
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDevissage
public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Torsion cohomological dimension and the ground field

The vanishing `Hᵠ(Spec K, F) = 0` for `q > 0` over a separably closed field `K`
(`AlgebraicGeometry.Scheme.subsingleton_H_of_pos_of_isSepClosed`) says that `cd(Spec K) = 0`
(`AlgebraicGeometry.Scheme.torsionCohomologicalDimension_spec_of_isSepClosed`). If `X` is of
finite type over a field `K` with `cd_tor(K) ≤ c` and
`cd_tor(X_K̄) ≤ e` for an algebraic closure `K̄` of `K`, then `cd_tor(X) ≤ c + e`
(`AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure`).

## Implementation details

The bound `cd_tor(X) ≤ c + e` uses the Leray spectral sequence of the structure morphism `a`:
the geometric stalk of `Rᵠa_* F` is `Hᵠ(X_{K^sep}, F)`, which agrees with `Hᵠ(X_K̄, F)` since
`X_K̄ ⟶ X_{K^sep}` is a universal homeomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale


namespace AlgebraicGeometry.Scheme

/-- `cd_tor` is invariant under isomorphisms; more generally it descends along universal
homeomorphisms: if `f : X ⟶ Y` is a universal homeomorphism and `cd_tor(X) ≤ c`, then
`cd_tor(Y) ≤ c`. -/
lemma HasTorsionCohomologicalDimensionLE.of_isUniversalHomeomorphism {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsUniversalHomeomorphism f] {c : ℕ}
    (h : X.HasTorsionCohomologicalDimensionLE c) :
    Y.HasTorsionCohomologicalDimensionLE c := fun F hF q hq ↦
  have := h _ (Etale.isTorsion_upperStar f hF) q hq
  (Etale.cohomologyMap_bijective f F q).injective.subsingleton

/-- Vanishing on a separably closed point.

If `K` is separably closed and `F` is an abelian sheaf on `Spec(K)_ét`, then
`Hᵠ(Spec(K)_ét, F) = 0` for every `q > 0`. -/
theorem subsingleton_H_of_pos_of_isSepClosed (K : Type u) [Field K] [IsSepClosed K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H F q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hq
  simpa using subsingleton_H_of_isSepClosed K F n

/-- The spectrum of a separably closed field has torsion étale cohomological dimension at most
zero. -/
lemma hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed (K : Type u) [Field K]
    [IsSepClosed K] : (Spec (.of K)).HasTorsionCohomologicalDimensionLE 0 :=
  fun F _ q hq ↦ subsingleton_H_of_pos_of_isSepClosed K F q hq

/-- **Cohomological dimension of a separably closed point.** If `K` is a separably closed field,
then its torsion étale cohomological dimension `cd(Spec K)` is `0`. -/
theorem torsionCohomologicalDimension_spec_of_isSepClosed (K : Type u) [Field K]
    [IsSepClosed K] : (Spec (.of K)).torsionCohomologicalDimension = 0 :=
  le_antisymm (torsionCohomologicalDimension_le_iff.2
    (hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed K)) bot_le

open ZeroObject in
/-- An abelian étale sheaf on `X` whose pullback along a surjective morphism `s : S ⟶ X`
vanishes is zero. -/
lemma isZero_of_isZero_upperStar_of_surjective {X S : Scheme.{u}} (s : S ⟶ X)
    (hs : Function.Surjective s)
    (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj M)) : IsZero M := by
  have hz : IsZero (0 : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := isZero_zero _
  have : IsIso (hz.from_ M) := by
    refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective AddCommGrpCat.{u + 1}
      (fun _ : PUnit.{u + 1} ↦ s) (fun x ↦ ⟨⟨⟩, hs x⟩) _ fun _ ↦ ?_
    have hz' : IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj 0) := Functor.map_isZero _ hz
    exact ⟨⟨hz'.to_ _, h.eq_of_src _ _, hz'.eq_of_src _ _⟩⟩
  exact IsZero.of_iso hz (asIso (hz.from_ M))

/-- Descent of a geometric cohomological dimension bound.

Let `X` be a scheme of finite type over a field `K` (structure morphism `a`), and let `K̄` be an
algebraic closure of `K`. If `cd_tor(K) ≤ c` and `cd_tor(X_K̄) ≤ e`, then `cd_tor(X) ≤ c + e`. -/
theorem hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure {K : Type u} [Field K]
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosure K L] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] {c e : ℕ}
    (hK : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c)
    (hX : HasTorsionCohomologicalDimensionLE
      (pullback a (Spec.map (CommRingCat.ofHom (algebraMap K L)))) e) :
    X.HasTorsionCohomologicalDimensionLE (c + e) := by
  have := LocallyOfFiniteType.isLocallyNoetherian a
  have := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian X := {}
  have : QuasiSeparated a := inferInstance
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  let s₀ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  -- the higher direct images vanish above `e`
  have hvan (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
      (hq : e < q) : IsZero ((((a)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj F) := by
    let T := strictLocalizationToBase s₀ ≫ 𝟙 (Spec (.of K))
    let u := Spec.map (strictHenselizationEval s₀)
    have hu : IsUniversalHomeomorphism u := isUniversalHomeomorphism_spec_strictHenselizationEval
    have hs : s₀ = u ≫ T := by
      simp only [T, Category.comp_id]
      exact (spec_map_strictHenselizationEval_comp_strictLocalizationToBase s₀).symm
    let φ : pullback a s₀ ⟶ pullback a T :=
      (pullback.congrHom rfl hs).hom ≫ (pullbackLeftPullbackSndIso a T u).inv ≫ pullback.fst _ _
    have hP := hX.of_isUniversalHomeomorphism φ
    refine isZero_of_isZero_upperStar_of_surjective (s₀ ≫ 𝟙 _) ?_ _
      (Etale.isZero_upperStar_rightDerived_lowerStar_of_subsingleton_H a (𝟙 _) F s₀ q (by lia)
        (hP _ (Etale.isTorsion_upperStar _ hF) q hq))
    exact fun x ↦ ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩
  intro F hF n hn
  obtain ⟨D, c', hc, rfl, hD⟩ := hF.exists_isColimit_nsmul_eq_zero
  suffices h0 : ∀ x : Sheaf.H c'.pt n, x = 0 by
    exact ⟨fun x y ↦ (h0 x).trans (h0 y).symm⟩
  intro x
  obtain ⟨j, y, rfl⟩ := (H_map_isColimit_of_isFiltered X hc n).1 x
  obtain ⟨m, hm, hmD⟩ := hD j
  have hDj : (D.obj j).IsTorsion := isTorsion_of_nsmul_id_eq_zero hm hmD
  have : Subsingleton (Sheaf.H (D.obj j) n) :=
    Etale.subsingleton_H_of_rightDerived_lowerStar a (D.obj j) (c := c) (e := e)
      (fun q hq ↦ hvan _ hDj q hq)
      (fun p q hp ↦ hK _ (isTorsion_of_nsmul_id_eq_zero hm (by
        rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hmD, Functor.map_zero])) p hp)
      n hn
  rw [Subsingleton.elim y 0, map_zero]

end AlgebraicGeometry.Scheme
