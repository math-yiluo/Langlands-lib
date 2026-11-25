/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitPresentation
import WeilConjectures.AlgebraicGeometry.Picard.UnionBoundedAboveModel
import WeilConjectures.AlgebraicGeometry.BoundedAboveModelFlatReplacement

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The Mayer--Vietoris construction supplies the bounded flat complex and its
base direct-image identification.  This is the construction part of the
relative Mayer--Vietoris gluing argument (Stacks Project, Tag 0DJ9).
(blueprint: new-pc-standard-single-flat-counit-union-core).

Proof: Restrict N to the two opens and their intersection; quasi-coherence and
relative flatness are preserved by open restriction. Apply the three supplied
presentation properties to obtain bounded-above complexes representing the
three direct images on B. In particular their cohomology vanishes above three
integer bounds. The relative Mayer--Vietoris triangle for this two-open cover
identifies the direct image from the union with the homotopy fibre of the
restriction-difference arrow from the sum of the first two direct images to
the third. Its long exact cohomology sequence shows that the union direct image
has no cohomology above the maximum of the first two bounds and one plus the
third bound. Take any complex representative of this derived object and its
good truncation at that bound. The truncation inclusion is a quasi-isomorphism,
since the cohomology above the bound vanishes. Apply the bounded-above flat
replacement theorem for sheaves of modules (Stacks Project, Tag 077J) to this
truncation. Its augmentation is a quasi-isomorphism, its terms are flat, and
it is zero above the bound. After localization the augmentation, truncation
inclusion and representative identification give e. This uses only the
sheaf-module Mayer--Vietoris triangle, so no quasi-compactness of U or V is
needed; the quasi-coherent refinement of that triangle is not used. -/
theorem standardSingleFlatCounitUnionCore
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    [IsAffine B] [IsAffine A] (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) [N.IsQuasicoherent]
    (hN : N.IsFlatOver ((U ⊔ V).ι ≫ p))
    (hPU : StandardSingleFlatCounitOnOpen p g U)
    (hPV : StandardSingleFlatCounitOnOpen p g V)
    (hPUV : StandardSingleFlatCounitOnOpen p g (U ⊓ V)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    letI := HasDerivedCategory.standard A.Modules
    letI := HasDerivedCategory.standard B.Modules
    ∃ K : CochainComplex (SheafOfModules.{u} (moduleRings B.toRingedSpace)) ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) ∧
      Nonempty (((schemeDerivedDirectImage ((U ⊔ V).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N) ≅
          DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) := by
  letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  letI := HasDerivedCategory.standard A.Modules
  letI := HasDerivedCategory.standard B.Modules
  obtain ⟨K, hbound, hiso⟩ := exists_boundedAbove_union_model p g U V N hN hPU hPV hPUV
  obtain ⟨K', hbound', hflat', hiso'⟩ :=
    exists_flat_model_of_boundedAbove_model
      ((schemeDerivedDirectImage ((U ⊔ V).ι ≫ p)).obj
        ((DerivedCategory.singleFunctor _ 0).obj N)) ⟨K, hbound, hiso⟩
  exact ⟨K', hbound', hflat', hiso'⟩

end AlgebraicGeometry
