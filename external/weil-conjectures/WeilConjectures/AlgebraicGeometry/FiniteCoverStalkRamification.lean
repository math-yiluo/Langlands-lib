/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CurveCoverRamificationAlgebra
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber

/-!
# Ramification indices of a finite morphism in terms of stalks

Let `p : C ⟶ Y` be an affine morphism and `Y₀ ⊆ Y` an affine open, with `A = Γ(Y, Y₀)` and
`B = Γ(C, p⁻¹ Y₀)`. For a point `c ∈ p⁻¹ Y₀` with prime `q ⊆ B`, the ramification index
`e(q | A)` is the length of `𝒪_{C,c} / 𝔪_{Y,p c} 𝒪_{C,c}`
(`AlgebraicGeometry.Scheme.Hom.ramificationIdx_primeIdealOf_eq_length`). In particular it is `1`
at points where `p` is unramified.

This is used in the covering step of blueprint `lemma-tangent-cones-on-cover`.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

/-- A point of an affine open is determined by its prime ideal: `primeIdealOf x = q` if and
only if `fromSpec q = x`. -/
lemma IsAffineOpen.primeIdealOf_eq_iff {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : U) (q : PrimeSpectrum Γ(X, U)) : hU.primeIdealOf x = q ↔ hU.fromSpec q = x.1 := by
  refine ⟨fun h ↦ h ▸ hU.fromSpec_primeIdealOf x, fun h ↦ ?_⟩
  apply hU.fromSpec.isOpenEmbedding.injective
  rw [hU.fromSpec_primeIdealOf x, h]

namespace Scheme.Hom

attribute [local instance] affineAlgebra

variable {C Y : Scheme.{u}} (p : C ⟶ Y) [IsAffineHom p] {Y₀ : Y.Opens} (hY₀ : IsAffineOpen Y₀)

/-- The ramification index of the prime of `c ∈ p⁻¹ Y₀` over `Γ(Y, Y₀)` is the length of
`𝒪_{C,c} / 𝔪_{Y,p c} 𝒪_{C,c}` (blueprint `lemma-tangent-cones-on-cover`). -/
theorem ramificationIdx_primeIdealOf_eq_length (c : C) (hc : c ∈ p ⁻¹ᵁ Y₀) :
    ((hY₀.preimage p).primeIdealOf ⟨c, hc⟩).asIdeal.ramificationIdx Γ(Y, Y₀) =
      (Module.length (C.presheaf.stalk c) (C.presheaf.stalk c ⧸
        (maximalIdeal (Y.presheaf.stalk (p c))).map (p.stalkMap c).hom)).toNat := by
  let St := C.presheaf.stalk c
  let : Algebra Γ(C, p ⁻¹ᵁ Y₀) St := TopCat.Presheaf.algebra_section_stalk C.presheaf ⟨c, hc⟩
  have := (hY₀.preimage p).isLocalization_stalk ⟨c, hc⟩
  let : Algebra Γ(Y, Y₀) St := ((algebraMap Γ(C, p ⁻¹ᵁ Y₀) St).comp
    (algebraMap Γ(Y, Y₀) Γ(C, p ⁻¹ᵁ Y₀))).toAlgebra
  have : IsScalarTower Γ(Y, Y₀) Γ(C, p ⁻¹ᵁ Y₀) St := .of_algebraMap_eq fun _ ↦ rfl
  rw [Ideal.ramificationIdx_eq_length_of_isLocalization _ St]
  let x : Y₀ := ⟨p c, hc⟩
  let : Algebra Γ(Y, Y₀) (Y.presheaf.stalk (p c)) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf x
  have := hY₀.isLocalization_stalk x
  have hunder : ((hY₀.preimage p).primeIdealOf ⟨c, hc⟩).asIdeal.under Γ(Y, Y₀) =
      (hY₀.primeIdealOf x).asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := p) Y₀ hY₀ (p ⁻¹ᵁ Y₀)
      (hY₀.preimage p) le_rfl hc
    rw [← app_eq_appLE] at h
    exact congrArg PrimeSpectrum.asIdeal h
  have hφ : algebraMap Γ(Y, Y₀) St =
      (p.stalkMap c).hom.comp (algebraMap Γ(Y, Y₀) (Y.presheaf.stalk (p c))) :=
    congrArg CommRingCat.Hom.hom (p.germ_stalkMap Y₀ c hc).symm
  rw [hunder, ← IsLocalization.AtPrime.map_eq_maximalIdeal (hY₀.primeIdealOf x).asIdeal
    (Y.presheaf.stalk (p c)), Ideal.map_map, hφ]

/-- At a point `c` where `𝔪_{Y,p c} 𝒪_{C,c} = 𝔪_{C,c}` (e.g. where `p` is unramified), the
ramification index of the prime of `c` over `Γ(Y, Y₀)` is `1`. -/
theorem ramificationIdx_primeIdealOf_eq_one (c : C) (hc : c ∈ p ⁻¹ᵁ Y₀)
    (h : (maximalIdeal (Y.presheaf.stalk (p c))).map (p.stalkMap c).hom =
      maximalIdeal (C.presheaf.stalk c)) :
    ((hY₀.preimage p).primeIdealOf ⟨c, hc⟩).asIdeal.ramificationIdx Γ(Y, Y₀) = 1 := by
  rw [p.ramificationIdx_primeIdealOf_eq_length hY₀ c hc, h, ENat.toNat_eq_iff_eq_natCast,
    Nat.cast_one, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
  exact maximalIdeal.isMaximal _

/-- **Ramification index as the valuation of a uniformizer.** Let `p : C ⟶ Y` be an affine morphism
with `Γ(C, p⁻¹ Y₀)` finite over `Γ(Y, Y₀)`, and `c ∈ p⁻¹ Y₀` a point at which `𝒪_{C,c}` is a
discrete valuation ring. If `u` generates the maximal ideal of `𝒪_{Y,p c}`, then its image in
`𝒪_{C,c}` is `w * ξ ^ e` with `w` a unit, `ξ` a uniformizer and `e` the ramification index of the
prime of `c` (blueprint `lemma-tangent-cones-on-cover`). -/
theorem exists_stalkMap_eq_unit_mul_pow_ramificationIdx
    [Module.Finite Γ(Y, Y₀) Γ(C, p ⁻¹ᵁ Y₀)] (c : C) (hc : c ∈ p ⁻¹ᵁ Y₀)
    [IsDomain (C.presheaf.stalk c)] [IsDiscreteValuationRing (C.presheaf.stalk c)]
    {u : Y.presheaf.stalk (p c)} (hu : Ideal.span {u} = maximalIdeal (Y.presheaf.stalk (p c))) :
    ∃ w ξ : C.presheaf.stalk c, IsUnit w ∧ Ideal.span {ξ} = maximalIdeal (C.presheaf.stalk c) ∧
      (p.stalkMap c).hom u = w * ξ ^
        ((hY₀.preimage p).primeIdealOf ⟨c, hc⟩).asIdeal.ramificationIdx Γ(Y, Y₀) := by
  rw [p.ramificationIdx_primeIdealOf_eq_length hY₀ c hc]
  refine IsDiscreteValuationRing.exists_eq_unit_mul_pow_length _ hu ?_
  rw [← p.ramificationIdx_primeIdealOf_eq_length hY₀ c hc]
  exact (Ideal.ramificationIdx_pos _ _).ne'

end Scheme.Hom

end AlgebraicGeometry
