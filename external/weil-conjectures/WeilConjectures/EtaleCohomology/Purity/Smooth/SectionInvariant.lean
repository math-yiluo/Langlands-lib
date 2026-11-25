/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness
public import WeilConjectures.SixFunctors.Etale.Derived.InvertiblePullback

/-!
# The section invariant and the family object of the deformation to the normal cone

For a morphism `g : V ⟶ B` smooth of pure relative dimension `d` with a section `s`, the
*section invariant* `𝒞(g, s) = Ls^* ω_g` (`AlgebraicGeometry.Etale.sectionInvariant`) is an
invertible object of `D(B_ét, Λ)`, since `ω_g` is
(`proposition-exceptional-inverse-image-smooth-morphism` (a)).

For a closed section `s`, the deformation to the normal cone of the section is the scheme
`D_s V = Spec_V 𝒪_V[t, I t⁻¹]` (`AlgebraicGeometry.Scheme.IdealSheafData.deformationSpace`), the
Rees-algebra form of `Bl_{s(B) × 0} (V ×_B 𝔸¹_B) ∖ (strict transform of V × 0)`, with
`g̃ : D_s V ⟶ 𝔸¹_B` (`AlgebraicGeometry.Scheme.Hom.deformationSpaceProj`) and its section
`s̃ : 𝔸¹_B ⟶ D_s V` (`AlgebraicGeometry.Scheme.Hom.deformationSpaceSection`). Its *family object*
is `F = Ls̃^* ω_{g̃}` (`AlgebraicGeometry.Etale.deformationFamilyObject`), again invertible.

## Main definitions

- `AlgebraicGeometry.Etale.deformationFamilyObject`: `F = Ls̃^* ω_{g̃}`.

## Main statements

- `AlgebraicGeometry.Etale.isInvertible_sectionInvariant`
- `AlgebraicGeometry.Etale.isInvertible_deformationFamilyObject`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {V B : Scheme.{u}} (d : ℕ)

/-- Blueprint `lemma-section-normal-bundle--1`: Section invariant

For `g : V ⟶ B` smooth of pure relative dimension `d` and a section `s` of `g`, the section
invariant `𝒞(g, s) = Ls^* ω_g = Ls^* Rg^! Λ_B` is an invertible object of `D(B_ét, Λ)`: the
dualizing complex `ω_g` is invertible by cohomological smoothness
(`proposition-exceptional-inverse-image-smooth-morphism`,
`proposition-exceptional-inverse-image-smooth-morphism` (a)), and derived pullback preserves
invertible objects. -/
theorem isInvertible_sectionInvariant (g : V ⟶ B) [SmoothOfRelativeDimension d g]
    [HasCompactification g] [HasInvertibleExponent Λ V] (s : B ⟶ V) :
    DerivedCategory.isInvertible Λ B (sectionInvariant Λ g s) :=
  DerivedCategory.isInvertible.leftDerivedUpperStar s (isInvertible_dualizingComplex Λ (d := d) g)

/-- Blueprint `definition-deformation-normal-bundle`: Deformation space of a closed section

The *family object* `F = Ls̃^* ω_{g̃} ∈ D(𝔸¹_B, Λ)` of the deformation to the normal cone of a
section `s` of `g : V ⟶ B`: the section invariant (`lemma-section-normal-bundle--1`) of the
deformation `g̃ : D_s V ⟶ 𝔸¹_B` (`AlgebraicGeometry.Scheme.Hom.deformationSpaceProj`) and its
section `s̃ : 𝔸¹_B ⟶ D_s V` (`AlgebraicGeometry.Scheme.Hom.deformationSpaceSection`). Here
`D_s V = Spec_V 𝒪_V[t, I t⁻¹]` is the extended Rees algebra form of
`Bl_{s(B) × 0} (V ×_B 𝔸¹_B) ∖ (strict transform of V ×_B 0)`.

In the purity conventions `g̃` is compactifiable
(`AlgebraicGeometry.Scheme.Hom.hasCompactification_deformationSpaceProj`). This is the concrete
counterpart of `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData.familyObject`, which is
the same section invariant for an abstract deformation datum; a concrete datum with this
deformation space is not yet constructed. -/
noncomputable def deformationFamilyObject (g : V ⟶ B) (s : B ⟶ V)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] :
    _root_.DerivedCategory
      (Sheaf 𝔸(ULift.{u} (Fin 1); B).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  sectionInvariant Λ (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection

/-- Blueprint `definition-deformation-normal-bundle`: Deformation space of a closed section

The family object `F = Ls̃^* ω_{g̃}` of the deformation to the normal cone of a closed section `s`
of a morphism `g` smooth of pure relative dimension `d` is an invertible object of
`D(𝔸¹_B, Λ)`: `g̃` is again smooth of relative dimension `d`
(`AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj`). -/
theorem isInvertible_deformationFamilyObject (g : V ⟶ B) [SmoothOfRelativeDimension d g]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] [HasInvertibleExponent Λ B] :
    DerivedCategory.isInvertible Λ 𝔸(ULift.{u} (Fin 1); B) (deformationFamilyObject Λ g s) :=
  have := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have : HasInvertibleExponent Λ s.ker.deformationSpace :=
    .of_hom (Scheme.Hom.deformationSpaceProj g s ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)
  isInvertible_sectionInvariant Λ d _ _

end Etale

end AlgebraicGeometry
