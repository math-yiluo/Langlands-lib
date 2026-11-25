/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Derived tensor descent on a ringed site

The site object and morphism universes remain independent; coefficients live in their maximum.
This is the same K-flat localization and tensor comparison as the recorded interface.

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 0G7D, 06YT and 06YU;
Categories, Tags 04VI, 04VJ and 04VK
(blueprint: lem-weil-pbc-site-derived-tensor-descent).

## Main statements

- `wf_site_derived_tensor_descent`: localization, tensor representative comparison,
  and unique extension of arbitrary natural transformations.
-/

@[expose] public section

universe u v w e z

open CategoryTheory

namespace SheafOfModules

set_option autoImplicit false
set_option synthInstance.maxSize 4096
/-- K-flat complexes with flat terms present the derived category and its tensor bifunctor.
The existential predicate `P` specifies the full subcategory by its precise membership
condition; `B` is total tensor on homotopy categories, specified by a natural comparison
with total tensor on complexes. The comparison for `T` is natural in both homotopy variables.
Naturality also gives the inverse-denominator equations by multiplying the naturality square
by the inverses of the denominator images. The final bijection includes arbitrary natural
transformations, without an invertibility assumption.

Source: Stacks Project, Tags 06YS, 0G7D, 06YT, 06YU and Categories 04VK
(blueprint: lem-weil-pbc-site-derived-tensor-descent).

Proof plan:
1. Resolve the vertex of each Ore square and cancellation witness by a K-flat flat-term
   resolution (`lem-pc-kflat-resolution`). The right calculus of fractions for the ambient
   homotopy category (`lem-pc-quasi-isomorphisms-multiplicative-system`) restricts to `P`.
2. The localization universal property induces the comparison functor. Refine every roof
   by a K-flat flat-term resolution to prove fullness (`lem-pc-right-fraction-representation`).
   Resolve common refinement vertices to prove faithfulness
   (`lem-pc-right-fraction-common-refinement`). Resolutions give essential surjectivity.
3. Total tensor descends through homotopy: a homotopy in the first variable is `h ⊗ 1`;
   in the second variable its component in bidegree `(p,q)` is `(-1)^p 1 ⊗ k`.
   The cross differential terms cancel, giving the natural comparison defining `B`.
4. Tensoring a quasi-isomorphism with a K-flat complex preserves quasi-isomorphisms:
   its cone is acyclic (`lem-pur-quasi-iso-cone-acyclic`), tensor preserves its acyclicity
   (`def-pc-kflat-complex`), and total tensor commutes with the cone differential.
   The symmetry with sign `(-1)^(pq)` gives the other variable.
5. Localize the tensor bifunctor twice (`lem-weil-pbc-localization-universal-property`),
   first into a functor category, then in the other variable. This gives `T` and its natural
   representative comparison. Inverting the naturality equations gives compatibility with
   inverse denominators.
6. Extend a transformation uniquely in the first variable by the same localization property.
   Uniqueness implies naturality in the second variable. Localize that variable to get the
   extension on the product derived category. Two applications of uniqueness prove bijectivity.
-/
theorem wf_site_derived_tensor_descent
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{max u v})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))] :
    ∃ P : ObjectProperty (HomotopyCategory (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
          (ComplexShape.up ℤ)),
      (∀ X, P X ↔ CochainComplex.IsAcyclicTensorKFlat (J := J) (R := R) X.as ∧
        ∀ n : ℤ, CategoryTheory.exactFunctor _ _
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max u v}
          ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) _
            (SheafOfModules.monoidalCategory.{v, u, max u v} R)).flip.obj (X.as.X n))) ∧
      (∃ F : ((HomotopyCategory.quasiIso (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) (ComplexShape.up
          ℤ)).inverseImage P.ι).Localization ⥤ (DerivedCategory (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))),
        F.IsEquivalence ∧ Nonempty (((HomotopyCategory.quasiIso (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) (ComplexShape.up
          ℤ)).inverseImage P.ι).Q ⋙ F ≅ (P.ι ⋙ DerivedCategory.Qh))) ∧
      (∃ B : (HomotopyCategory (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
          (ComplexShape.up ℤ)) ×
          (HomotopyCategory (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
          (ComplexShape.up ℤ)) ⥤
          (HomotopyCategory (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
          (ComplexShape.up ℤ)),
        Nonempty (((HomotopyCategory.quotient (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
          (ComplexShape.up ℤ)).prod
          (HomotopyCategory.quotient (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
          (ComplexShape.up ℤ))) ⋙ B ≅
          Functor.uncurry.obj
            ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) _
          (SheafOfModules.monoidalCategory.{v, u, max u v} R)).map₂HomologicalComplex
              (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙
                (HomotopyCategory.quotient (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
          (ComplexShape.up ℤ))) ∧
        ∃ T : (DerivedCategory (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))) ×
          (DerivedCategory
          (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))) ⥤
          (DerivedCategory
          (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))),
          Nonempty ((P.ι.prod P.ι) ⋙ B ⋙ DerivedCategory.Qh ≅
            ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) ⋙ T)) ∧
      (∀ (E : Type e) (_ : Category.{z} E)
        (U V : (DerivedCategory (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))) ×
          (DerivedCategory
          (SheafOfModules.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))) ⥤ E),
        Function.Bijective (fun τ : U ⟶ V ↦
          Functor.whiskerLeft ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) τ)) := by
  obtain ⟨P, hP, hF, hB, hτ⟩ :=
    site_derived_tensor_descent_independentCoefficients.{u, v, max u v, w, e, z} J R
  refine ⟨P, ?_, hF, hB, hτ⟩
  intro X
  rw [hP X]
  constructor
  · rintro ⟨hK, hflat⟩
    refine ⟨hK, fun n ↦ ?_⟩
    exact (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso R (X.as.X n)) (hflat n)
  · rintro ⟨hK, hflat⟩
    refine ⟨hK, fun n ↦ ?_⟩
    exact (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso R (X.as.X n)).symm (hflat n)

end SheafOfModules
