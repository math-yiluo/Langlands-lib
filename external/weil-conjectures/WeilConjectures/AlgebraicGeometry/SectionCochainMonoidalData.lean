/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionDerivedTensorData
import all WeilConjectures.AlgebraicGeometry.InternalSectionTensorLocalization
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors

/-! # The monoidal structure on the termwise section equivalence

Source: Stacks Project, sites-cohomology.tex, Tags 06YU, 0FPT, and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

attribute [local implicit_reducible] tensor
  ResolvingOplaxConstraints.TensorFunctorTransport.tensorFunctor
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Monoidal.induced
  CategoryTheory.Mod.monoidalCategoryCochainComplex
  CategoryTheory.Mod.derivedMonoidalCategory CategoryTheory.Mod.laxMonoidalQ
  SheafOfModules.cochainModulesMonoidal RingedDerivedNative.moduleMonoidal
  ModuleObjectRingedComparison.ringedMonoidal
  ModuleObjectRingedComparison.internalComplexMonoidal
  ModuleObjectRingedComparison.sliceCochainMonoidal

attribute [local irreducible] totalComparison

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
private theorem ordinary_monoidal (T : Scheme.{u}) :
    ∃ m : (equivalence Λ T).functor.Monoidal, letI := m
      ∀ M N, Functor.OplaxMonoidal.δ (equivalence Λ T).functor M N =
        (ordinaryTensorComparison Λ T M N).hom := by
  have hc : IsCommMonObj (condensedRingObj Λ T) :=
    AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ T
  obtain ⟨d⟩ := ModuleObjectRingedComparison.section_monoidal_data
    (Scheme.ProEt.topology T) (condensedRingObj Λ T) (hcomm := hc)
  refine ⟨d.monoidal, ?_⟩
  intro M N
  exact (d.delta M N).trans (congrArg Iso.hom (ordinaryTensorComparison_eq Λ T M N))

-- Identifying the signed total comparison elaborates the native cochain monoidal structure.
/-- The termwise section equivalence is strong monoidal with the specified signed comparison.

Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 07A4, and the signed-total
construction of the tensor comparison (Tag 0FPT).

Proof: take the canonical ordinary section monoidal data and identify its oplax
comparison with ordinaryTensorComparison by the pure-tensor normalization theorem.
The standard cochain extension of this additive monoidal equivalence is strong
monoidal. Its oplax tensorator is mapBifunctorComparison of the curried ordinary
oplax transformation. Equality of these ordinary components identifies the two
curried natural transformations; sectionTotalComparison_eq then identifies the
cochain tensorator with cochainTensorComparison. This construction is unbounded
and also applies to zero complexes, zero coefficients and empty sites.
(auxiliary; not a blueprint node). -/
theorem section_cochain_monoidal_data (T : Scheme.{u}) :
    ∃ m : ((equivalence Λ T).mapHomologicalComplex (.up ℤ)).functor.Monoidal,
      letI := m
      ∀ P Q : CochainComplex (internalModules Λ T) ℤ,
        Functor.OplaxMonoidal.δ
            ((equivalence Λ T).mapHomologicalComplex (.up ℤ)).functor P Q =
          (cochainTensorComparison Λ T P Q).hom := by
  obtain ⟨o, ho⟩ := ordinary_monoidal Λ T
  let := o
  let mc : ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).Monoidal :=
    Functor.mapCochainComplexMonoidal (equivalence Λ T).functor
  let := mc
  let m : ((equivalence Λ T).mapHomologicalComplex (.up ℤ)).functor.Monoidal := mc
  refine ⟨m, ?_⟩
  intro P Q
  change Functor.OplaxMonoidal.δ
      ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)) P Q =
    (cochainTensorComparison Λ T P Q).hom
  erw [cochainTensorComparison,
    Functor.mapCochainComplex_δ (C := internalModules Λ T) (D := modules Λ T),
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app
      (C := internalModules Λ T) (D := modules Λ T)]
  change HomologicalComplex.mapBifunctorComparison
      (Functor.OplaxMonoidal.δNatTrans (equivalence Λ T).functor) (.up ℤ) P Q =
    (totalComparison Λ T P Q).hom
  rw [← sectionTotalComparison_eq]
  unfold sectionTotalComparison
  congr 1
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext N
  exact (ho M N).trans (sectionOrdinaryTensorMap_app Λ T M N).symm

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
