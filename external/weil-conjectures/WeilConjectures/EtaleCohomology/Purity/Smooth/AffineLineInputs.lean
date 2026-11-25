/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologyHom
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator

/-!
# The cohomology of `𝔸¹` and `𝔾ₘ` over an algebraically closed field, in the form used

This file packages the Kummer computations of
`WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator` (blueprint
`thm-pur-kummer-affine-line`) in the form in which the relative statements over a base consume
them: the model `𝔾_{m,k}` is the basic open of the coordinate
(`AlgebraicGeometry.Etale.multiplicativeGroupModel`), and `H¹(𝔾_{m,k}, Λ) ≅ Λ` as a
`Λ`-module (`AlgebraicGeometry.Etale.nonempty_iso_cohomology_one_multiplicativeGroup`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The characteristic of a finite ring is nonzero. -/
theorem neZero_ringChar_of_finite : NeZero (ringChar Λ) :=
  ⟨CharP.char_ne_zero_of_finite Λ (ringChar Λ)⟩

attribute [local instance] neZero_ringChar_of_finite

variable (k : Type u) [Field k] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]

/-- The model `𝔾_{m,k}` of the multiplicative group: the basic open of the coordinate of
`𝔸¹_k`. -/
noncomputable abbrev multiplicativeGroupModel : 𝔸(ULift.{u} (Fin 1); Spec (.of k)).Opens :=
  𝔸(ULift.{u} (Fin 1); Spec (.of k)).basicOpen (AffineSpace.coord (Spec (.of k)) (ULift.up 0))

omit [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))] in
lemma range_multiplicativeGroupModel_ι :
    Set.range (𝔸(ULift.{u} (Fin 1); Spec (.of k)).basicOpen
      (AffineSpace.coord (Spec (.of k)) (ULift.up 0))).ι.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).base)ᶜ :=
  AffineSpace.range_basicOpen_ι_coord _

omit [HasInvertibleExponent Λ (Spec (.of k))] in
variable {k} in
/-- `H¹(𝔾_{m,k}, Λ) ≅ Λ` as a `Λ`-module, for the constant coefficients. -/
theorem nonempty_iso_cohomology_one_multiplicativeGroup {G : Scheme.{u}}
    (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1))
      (Spec (.of k))).base)ᶜ) [HasInvertibleExponent Λ G]
    [HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); Spec (.of k))] :
    Nonempty ((cohomology (ModuleCat.{u + 1} Λ) G 1).obj (constantComplex Λ G) ≅
      ModuleCat.of Λ Λ) := by
  obtain ⟨y₀, hy₀⟩ := exists_bijective_smul_constantComplex_shift_one Λ j hj
  let e : Λ ≃ₗ[Λ] (constantComplex Λ G ⟶ (constantComplex Λ G)⟦(1 : ℤ)⟧) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton Λ _ y₀) hy₀
  exact ⟨(e ≪≫ₗ homConstantComplexLinearEquivCohomology Λ G _ 1).toModuleIso.symm⟩

end Etale

end AlgebraicGeometry
