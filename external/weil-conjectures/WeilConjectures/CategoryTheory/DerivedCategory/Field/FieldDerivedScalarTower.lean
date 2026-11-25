/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldComplexScalarExtension
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Canonical derived scalar-extension comparisons

Source: Weil blueprint, `lemma-perfect-complexes-geometric-point`, order 1509
(blueprint: lem-weil-derived-field-scalar-extension-tower).

## Main definitions and statements

* `fieldScalarTower`, `fieldScalarUnit`: the uniquely normalized tensor comparisons.
* `fieldScalarTower_assoc`, `fieldScalarTower_units`: their coherence.
* `fieldScalarTower_commShift`: compatibility with the triangulated shifts.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {K L M : Type u} [Field K] [Field L] [Field M]

/-- The prescribed component of the tower comparison on a representing complex.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower). -/
noncomputable def fieldScalarTowerComponent (f : K →+* L) (g : L →+* M)
    (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    ((fieldDerivedScalarExtension f ⋙ fieldDerivedScalarExtension g).obj
      (DerivedCategory.Q.obj C)) ≅
      (fieldDerivedScalarExtension (g.comp f)).obj (DerivedCategory.Q.obj C) :=
  (fieldDerivedScalarExtension g).mapIso
      ((ModuleCat.extendScalars f).mapDerivedCategoryFactors.app C) ≪≫
    (ModuleCat.extendScalars g).mapDerivedCategoryFactors.app
      ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj C) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f g).symm
        (ComplexShape.up ℤ)).app C) ≪≫
    ((ModuleCat.extendScalars (g.comp f)).mapDerivedCategoryFactors.app C).symm

/-- Localization gives the unique tower comparison with these prescribed components.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower).
Proof: the termwise tensor tower isomorphism is natural and inverts quasi-isomorphisms.
Lift it through Q using localization. Every derived object is represented by a complex,
and precomposition with Q is fully faithful on the resulting functors, so the
prescribed components determine the lift uniquely. -/
theorem existsUnique_fieldScalarTower (f : K →+* L) (g : L →+* M) :
    ∃! e : fieldDerivedScalarExtension f ⋙ fieldDerivedScalarExtension g ≅
        fieldDerivedScalarExtension (g.comp f),
      ∀ C : CochainComplex (ModuleCat.{u} K) ℤ,
        e.app (DerivedCategory.Q.obj C) = fieldScalarTowerComponent f g C := by
  let e₀ : DerivedCategory.Q ⋙
      (fieldDerivedScalarExtension f ⋙ fieldDerivedScalarExtension g) ≅
      DerivedCategory.Q ⋙ fieldDerivedScalarExtension (g.comp f) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ModuleCat.extendScalars f).mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ModuleCat.extendScalars g).mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f g).symm
          (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      ((ModuleCat.extendScalars (g.comp f)).mapDerivedCategoryFactors).symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
    (DerivedCategory (ModuleCat.{u} M))
  refine ⟨ff.preimageIso e₀, ?_, ?_⟩
  · intro C
    apply Iso.ext
    have hc := congr_app (ff.map_preimage e₀.hom) C
    simpa [e₀, fieldScalarTowerComponent] using hc
  · intro e he
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
    intro C
    have hc := congr_app (ff.map_preimage e₀.hom) C
    exact congrArg Iso.hom (he C) |>.trans (by
      simpa [e₀, fieldScalarTowerComponent] using hc.symm)

/-- The canonical tower comparison, selected from a uniquely determined natural isomorphism.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower). -/
noncomputable def fieldScalarTower (f : K →+* L) (g : L →+* M) :
    fieldDerivedScalarExtension f ⋙ fieldDerivedScalarExtension g ≅
      fieldDerivedScalarExtension (g.comp f) :=
  (existsUnique_fieldScalarTower f g).exists.choose

end DerivedCategory
