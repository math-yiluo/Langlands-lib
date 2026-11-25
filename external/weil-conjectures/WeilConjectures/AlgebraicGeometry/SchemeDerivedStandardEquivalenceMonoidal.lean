/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! # Monoidal comparison with the standard derived localization

Source: Stacks Project, Tags 079U and 05RU.
(blueprint: lem-sc-standard-derived-equivalence-monoidal).
-/

@[expose] public section
set_option autoImplicit false
universe u wX
open CategoryTheory
@[instance_reducible]
private noncomputable def kFlatCompMonoidal
    {C D K : Type*} [Category C] [Category D] [Category K]
    [MonoidalCategory C] [MonoidalCategory K]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.ContainsIdentities] [W.RespectsIso] [W.HasTwoOutOfThreeProperty]
    [W.localizerMorphismKFlat.IsLeftDerivabilityStructure]
    (J : K ⥤ C) [J.Monoidal] (hJ : ∀ P, W.kFlat (J.obj P)) :
    (J ⋙ toDerivedMonoidal L W).Monoidal := by
  have : ∀ P N, IsIso (Functor.LaxMonoidal.μ
      (J ⋙ toDerivedMonoidal L W) P N) := by
    intro P N
    have := DerivedMonoidal.isIso_counit_app_app_of_kFlat_left L W
      (J.obj P) (J.obj N) (hJ P)
    dsimp only [Functor.LaxMonoidal.comp_μ]
    infer_instance
  have : IsIso (Functor.LaxMonoidal.ε (J ⋙ toDerivedMonoidal L W)) := by
    dsimp only [Functor.LaxMonoidal.comp_ε]
    infer_instance
  exact Functor.Monoidal.ofLaxMonoidal _

private theorem exists_standardLocalization_monoidal
    (A : Type*) [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [HasDerivedCategory.{wX} A] :
    letI : Limits.HasColimitsOfSize.{0, 0} A := Limits.hasColimitsOfSizeShrink A
    letI : MonoidalCategory (DerivedCategory A) :=
      inferInstanceAs (MonoidalCategory (DerivedMonoidal (DerivedCategory.Qh (C := A))
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))))
    letI : MonoidalCategory (@DerivedCategory A _ _ (HasDerivedCategory.standard A)) :=
      inferInstanceAs (MonoidalCategory (DerivedMonoidal
        (@DerivedCategory.Qh A _ _ (HasDerivedCategory.standard A))
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))))
    Nonempty ((Localization.uniq (DerivedCategory.Qh (C := A))
      (@DerivedCategory.Qh A _ _ (HasDerivedCategory.standard A))
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))).functor.CoreMonoidal) := by
  have : Limits.HasColimitsOfSize.{0, 0} A := Limits.hasColimitsOfSizeShrink A
  have (P : A) : Limits.PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor A).flip.obj P) :=
    Limits.preservesColimitsOfShape_of_natIso (F := MonoidalCategory.tensorLeft P)
      (NatIso.ofComponents (fun N ↦ BraidedCategory.braiding P N)
        (by intros; simp [MonoidalCategory.curriedTensor]))
  have : (ObjectProperty.flat (A := A)).IsStableUnderRetracts :=
    ⟨fun h hN ↦ ObjectProperty.flat_of_retract h hN⟩
  have (P N : GradedObject ℤ A) : P.HasTensor N := inferInstance
  have (P N R S : GradedObject ℤ A) : GradedObject.HasTensor₄ObjExt P N R S :=
    inferInstance
  have (P N R : GradedObject ℤ A) : GradedObject.HasGoodTensor₁₂Tensor P N R :=
    inferInstance
  have (P N R : GradedObject ℤ A) : GradedObject.HasGoodTensorTensor₂₃ P N R :=
    inferInstance
  have : (ObjectProperty.flat (A := A)).ContainsZero :=
    ⟨_, Limits.isZero_zero A, ObjectProperty.flat_of_isZero (Limits.isZero_zero A)⟩
  have : Limits.HasZeroObject (ObjectProperty.flat (A := A)).FullSubcategory := inferInstance
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  let Wh := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let I := W.ιKFlat
  let J := I ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have : W.localizerMorphismKFlat.IsLocalizedEquivalence := by
    let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ A) := Classical.arbitrary _
    exact W.localizerMorphismKFlat.isLocalizedEquivalence_of_functorial_left_resolutions
      (Λ.reduced.kFlatResolutionNatTrans ObjectProperty.flat.essImage_ι_le)
      (fun K ↦ by
        change HomologicalComplex.quasiIso A (ComplexShape.up ℤ) _
        rw [HomologicalComplex.mem_quasiIso_iff]
        infer_instance) rfl
  have : Wh.localizerMorphismKFlat.IsLeftDerivabilityStructure := by
    let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ A) := Classical.arbitrary _
    exact Λ.reduced.homotopyCategory_kFlat_isLeftDerivabilityStructure
      ObjectProperty.flat.essImage_ι_le
  let Q₁ := DerivedCategory.Qh (C := A)
  let Q₂ := @DerivedCategory.Qh A _ _ (HasDerivedCategory.standard A)
  let : MonoidalCategory (DerivedMonoidal Q₁ Wh) :=
    DerivedMonoidal.instMonoidalCategory Q₁ Wh
  let : MonoidalCategory (DerivedMonoidal Q₂ Wh) :=
    DerivedMonoidal.instMonoidalCategory Q₂ Wh
  let L := J ⋙ Q₁
  let G := J ⋙ Q₂
  let : L.Monoidal := kFlatCompMonoidal Q₁ Wh J
    (fun P ↦ (HomotopyCategory.kFlat_quotient_obj_iff P.obj).2 P.property)
  let : G.Monoidal := kFlatCompMonoidal Q₂ Wh J
    (fun P ↦ (HomotopyCategory.kFlat_quotient_obj_iff P.obj).2 P.property)
  have : (I ⋙ DerivedCategory.Q (C := A)).IsLocalization W.WKFlat :=
    inferInstanceAs ((W.localizerMorphismKFlat.functor ⋙
      DerivedCategory.Q (C := A)).IsLocalization W.WKFlat)
  have : L.IsLocalization W.WKFlat := Functor.IsLocalization.of_iso _
    ((Functor.associator I (HomotopyCategory.quotient A (ComplexShape.up ℤ)) Q₁) ≪≫
      Functor.isoWhiskerLeft I (DerivedCategory.quotientCompQhIso A)).symm
  let E := (Localization.uniq Q₁ Q₂ Wh).functor
  let : Localization.Lifting L W.WKFlat G E := ⟨
    Functor.associator J Q₁ E ≪≫ Functor.isoWhiskerLeft J
      (Localization.compUniqFunctor Q₁ Q₂ Wh)⟩
  exact ⟨Localization.Monoidal.functorCoreMonoidalOfComp L W.WKFlat E G⟩

namespace AlgebraicGeometry
/-- The specified equivalence to the standard localization preserves the fixed
K-flat derived tensor and its unit. Source: Stacks Project, Tags 079U and 05RU,
with the identity morphism in 079U and the localization universal property.
(blueprint: lem-sc-standard-derived-equivalence-monoidal).

Proof: write E for schemeDerivedStandardEquivalence X. Its canonical comparison
Qh ⋙ E.functor ≅ Qh_standard identifies localized representatives. For K-flat
complexes P and N, identify their derived tensor with the localization of their
ordinary total tensor complex in both localizations. Conjugating these two
comparison isomorphisms by the factorization of E yields an invertible map
E(P) tensor E(N) -> E(P tensor N). The unit is the localization of the structure
sheaf in degree zero in both categories, so the same factorization gives its
invertible comparison. Extend the tensor maps to arbitrary objects through K-flat
resolutions. Naturality of the localization factorization and tensor comparisons
shows independence of the resolutions and naturality in both arguments.
Resolve three arguments simultaneously: associativity is the image of the
associativity of the total tensor complex; the comparison maps cancel. Resolving
one argument and using the structure sheaf as the other gives both unit laws.
The localization universal property descends these equalities to all objects.
Package the maps and these laws as CoreMonoidal. No condition on X or on the
chosen localization universe is required; zero complexes and empty schemes use
the same construction. -/
theorem exists_schemeDerivedStandardEquivalence_monoidal
    (X : Scheme.{u})
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    Nonempty ((schemeDerivedStandardEquivalence X).functor.CoreMonoidal) := by
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let := moduleTensor X
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive A := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed A := Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{u} A :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : Limits.HasColimitsOfSize.{0, 0} A := Limits.hasColimitsOfSizeShrink.{0, 0, u, u} A
  have := schemeModule_hasFunctorialFlatResolution X
  have h := exists_standardLocalization_monoidal.{u, wX} A
  exact h
end AlgebraicGeometry
