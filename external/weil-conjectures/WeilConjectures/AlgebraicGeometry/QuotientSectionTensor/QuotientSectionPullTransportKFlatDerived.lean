/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData
import all WeilConjectures.AlgebraicGeometry.SectionPullComputationOfRealization
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionPullTransportScalarComputation
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Flat-term derived square for quotient section pull transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
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
open ModuleRingedComparison

attribute [local instance] ModuleRingedComparison.sectionFunctorAdditive

attribute [local semireducible] QuotientChange.L
attribute [local implicit_reducible] QuotientChange.L
  InternalAbelianSheafModule.sectionRingSheaf
  DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh
  CategoryTheory.catToReflQuiver
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafSymmetricCategory

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

set_option cleanup.letToHave false in
-- Instance synthesis traverses the eight localization functors in the pasting diagram.
-- The fully typed categorical pasting diagram needs a larger elaboration budget.
/-- Given the normalized ordinary square and the conjugated derived comparison,
the scalar-model counit computation holds on every flat-term K-flat complex.
This is the representative calculation: expand the endpoint model counits,
apply the two normalization equations, and use `PullNormalized` for the central
internal square. -/
theorem section_pull_transport_kflat_derived {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (hcX : ScalarSectionNormalized a X cX) (hcY : ScalarSectionNormalized a Y cY)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hlam : PullNormalized a f lam)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T)
    (hbarLam : ∀ M : DerivedCategory (Modules Λ Y),
      (derivedEquivalence Λ' X).functor.map (lam.hom.app M) ≫
          cX.derived.hom.app ((L Λ f).obj M) ≫
          cX.model.T.map ((scalarSectionPullComparison Λ f).hom.app M) =
        (scalarSectionPullComparison Λ' f).hom.app ((D a Y).obj M) ≫
          (derivedPullback Λ' f).map (cY.derived.hom.app M) ≫
          barLam.hom.app ((derivedEquivalence Λ Y).functor.obj M))
    (e : cY.model.E ⋙ pullback Λ' f ≅ pullback Λ f ⋙ cX.model.E)
    (he : ∀ M : Modules Λ Y,
      (equivalence Λ' X).functor.map ((CondensedRing.pullIso a f).inv.app M) ≫
          cX.ordinary.hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
          cX.model.E.map ((pullComparison Λ f).hom.app M) =
        (pullComparison Λ' f).hom.app ((QuotientChange.extension a Y).obj M) ≫
          (pullback Λ' f).map (cY.ordinary.hom.app M) ≫
          e.hom.app ((equivalence Λ Y).functor.obj M)) :
    ∀ P : CochainComplex (modules Λ Y) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      barLam.hom.app (DerivedCategory.Q.obj P) ≫
          cX.model.T.map ((pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
          cX.model.ε.app (((pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (pullback Λ f ⋙ cX.model.E)) (.up ℤ)).hom.app P) =
        (derivedPullback Λ' f).map (cY.model.ε.app P) ≫
          (pullback Λ' f).mapDerivedCategoryFactors.hom.app
            ((cY.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P) := by
  let AD := D a Y
  let BD := D a X
  let FD := L Λ f
  let JD := L Λ' f
  let fD := ModuleRingedComparison.derivedPullback Λ f
  let jD := ModuleRingedComparison.derivedPullback Λ' f
  let kD0 := (ModuleRingedComparison.derivedEquivalence Λ Y).functor
  let kD1 := (ModuleRingedComparison.derivedEquivalence Λ X).functor
  let kD2 := (ModuleRingedComparison.derivedEquivalence Λ' Y).functor
  let kD3 := (ModuleRingedComparison.derivedEquivalence Λ' X).functor
  have hInt := cochain_normalization
    (A := Modules Λ Y) (B := Modules Λ X)
    (C := Modules Λ' Y) (D := Modules Λ' X)
    (extension a Y) (extension a X)
    (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ' f)
    AD BD FD JD
    (scalarCounit a Y) (scalarCounit a X)
    (pullCounit (Λ := Λ) f) (pullCounit (Λ := Λ') f)
    lam (CondensedRing.pullIso a f).symm hlam
  have hall := paste_diagram
    ((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ))
    ((CondensedRing.upperStar Λ' f).mapHomologicalComplex (.up ℤ))
    ((extension a Y).mapHomologicalComplex (.up ℤ))
    ((extension a X).mapHomologicalComplex (.up ℤ))
    ((pullback Λ f).mapHomologicalComplex (.up ℤ))
    ((pullback Λ' f).mapHomologicalComplex (.up ℤ))
    (cY.model.E.mapHomologicalComplex (.up ℤ))
    (cX.model.E.mapHomologicalComplex (.up ℤ))
    ((equivalence Λ Y).functor.mapHomologicalComplex (.up ℤ))
    ((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ))
    ((equivalence Λ' Y).functor.mapHomologicalComplex (.up ℤ))
    ((equivalence Λ' X).functor.mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    AD BD FD JD
    cY.model.T cX.model.T
    fD jD kD0 kD1 kD2 kD3
    (complex_iso cY.ordinary) (complex_iso cX.ordinary)
    (complex_iso (pullComparison Λ f)) (complex_iso (pullComparison Λ' f))
    (complex_comp_iso (CondensedRing.pullIso a f).symm) (complex_comp_iso e)
    cY.derived cX.derived
    (scalarSectionPullComparison Λ f) (scalarSectionPullComparison Λ' f) lam barLam
    (section_localization_iso (Λ := Λ) Y) (section_localization_iso (Λ := Λ) X)
    (section_localization_iso (Λ := Λ') Y) (section_localization_iso (Λ := Λ') X)
    (fun P ↦ (scalarCounit a Y).app ((HomotopyCategory.quotient _ _).obj P))
    (fun P ↦ (scalarCounit a X).app ((HomotopyCategory.quotient _ _).obj P))
    (fun P ↦ (pullCounit (Λ := Λ) f).app ((HomotopyCategory.quotient _ _).obj P))
    (fun P ↦ (pullCounit (Λ := Λ') f).app ((HomotopyCategory.quotient _ _).obj P))
    cY.model.ε cX.model.ε
    (section_pull_compute_nat (Λ := Λ) f)
    (section_pull_compute_nat (Λ := Λ') f)
    (complex_equivalence (ModuleRingedComparison.equivalence Λ Y))
    (fun P ↦ by
      dsimp only [AD, kD2, complex_iso, section_localization_iso, Functor.comp_obj]
      simpa only [QuotientChange.compute_eq] using
        section_pull_transport_scalar_computation a Y cY hcY P)
    (fun P ↦ by
      dsimp only [BD, kD3, complex_iso, section_localization_iso, Functor.comp_obj]
      simpa only [QuotientChange.compute_eq] using
        section_pull_transport_scalar_computation a X cX hcX P)
    (geometric_computation (Λ := Λ) f) (geometric_computation (Λ := Λ') f)
    (complex_square (CondensedRing.upperStar Λ f) (CondensedRing.upperStar Λ' f)
      (extension a Y) (extension a X) (pullback Λ f) (pullback Λ' f)
      cY.model.E cX.model.E (equivalence Λ Y).functor (equivalence Λ X).functor
      (equivalence Λ' Y).functor (equivalence Λ' X).functor
      cY.ordinary cX.ordinary (pullComparison Λ f) (pullComparison Λ' f)
      (CondensedRing.pullIso a f).symm e he) hInt hbarLam
  intro P _ _
  rw [Functor.mapHomologicalComplexCompIso_refl_hom_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simpa only [complex_comp_iso_hom_app, section_pull_compute_nat] using hall P

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
