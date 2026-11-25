/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Scalar computation for normalized section transport

## References

* Stacks Project, Tags 06YY, 0D6D and 07A6
* Stacks 06YY and 07A6, the scalar computation step of normalized section transport
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Share the large inferred cochain structures while checking the diagram proof.
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient

attribute [local instance] ModuleRingedComparison.sectionFunctorAdditive

attribute [local semireducible] QuotientChange.L
attribute [local implicit_reducible] QuotientChange.L
  InternalAbelianSheafModule.sectionRingSheaf
  DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.catToReflQuiver
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafSymmetricCategory

private theorem map_id_cleanup
    {A C D : Type*} [Category A] [Category C] [Category D]
    (F : A ⥤ D) (G : C ⥤ D) {x : A} {y : C} (t : F.obj x ⟶ G.obj y) :
    F.map (𝟙 x) ≫ t ≫ G.map (𝟙 y) ≫ 𝟙 _ = t := by
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

private theorem compute_eq (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) :
    compute a T P = (scalarCounit a T).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  unfold compute
  change (D a T).map (𝟙 _) ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  exact map_id_cleanup (D a T) DerivedCategory.Qh _

variable
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

private theorem native_localization_hom (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) :
    ((ModuleRingedComparison.equivalence Λ T).functor.mapDerivedCategoryFactors).hom.app P =
      (ModuleRingedComparison.sectionLocalizationComparison Λ T P).hom := by
  rfl

/-- Endpoint normalization expressed through the actual scalar localization counit. -/
theorem section_pull_transport_scalar_computation (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (c : ScalarSectionData a T) (h : ScalarSectionNormalized a T c)
    (P : CochainComplex (Modules Λ T) ℤ) :
    @Eq ((ModuleRingedComparison.derivedEquivalence Λ' T).functor.obj
      ((D a T).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((c.model.E.mapHomologicalComplex (.up ℤ)).obj
        (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj
          P)))
      ((ModuleRingedComparison.derivedEquivalence Λ' T).functor.map
        (compute a T P) ≫
        ((ModuleRingedComparison.equivalence Λ' T).functor.mapDerivedCategoryFactors).hom.app
          (((extension a T).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (((Functor.mapHomologicalComplexCompIso c.ordinary (.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl ((ModuleRingedComparison.equivalence Λ T).functor ⋙ c.model.E))
            (.up ℤ)).symm)).hom.app P))
      (c.derived.hom.app (DerivedCategory.Q.obj P) ≫
        c.model.T.map
          (((ModuleRingedComparison.equivalence Λ T).functor.mapDerivedCategoryFactors).hom.app P) ≫
        c.model.ε.app
          (((ModuleRingedComparison.equivalence Λ T).functor.mapHomologicalComplex
            (.up ℤ)).obj P)) := by
  have hh := (h.2 P).symm
  dsimp only [ModuleRingedComparison.derivedEquivalence, Functor.asEquivalence] at *
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Functor.comp_obj, Category.assoc, compute_eq,
    native_localization_hom]
    using hh

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
