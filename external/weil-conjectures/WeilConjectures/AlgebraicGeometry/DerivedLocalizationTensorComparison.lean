/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure

/-! # Tensor under the standard localization comparison

Source: Stacks Project, Tags 05RU and 06YH.
(blueprint: lem-pc-derived-localization-tensor-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The inverse standard comparison respects the K-flat derived tensor.
Source: Stacks Project, Tags 05RU and 06YH.
(blueprint: lem-pc-derived-localization-tensor-comparison).

Proof: the comparison is the unique equivalence commuting with Qh. Compute each
of the two tensors using K-flat resolutions of its arguments. The resolutions and
termwise tensor are in the same homotopy category before either localization, so
Qh comparison identifies their images. The K-flat resolution counits are inverted
by both localizations, giving the displayed isomorphism for arbitrary unbounded
arguments. Equivalently, uncurry the derived tensor into a right Kan extension
along Qh times Qh; transport this universal property through the equivalences of
its domain and codomain and use uniqueness of right Kan extensions. No
quasi-coherence or Noetherian hypothesis is needed. For the empty scheme the
same comparisons apply to the zero category; for a standard input localization
they specialize to the canonical localization self-equivalence comparisons. -/
theorem derivedLocalization_tensorComparison (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (A B : @schemeDerivedCategory X (HasDerivedCategory.standard _)) :
    Nonempty ((schemeDerivedStandardEquivalence X).inverse.obj (A ⊗ B) ≅
      (schemeDerivedStandardEquivalence X).inverse.obj A ⊗
        (schemeDerivedStandardEquivalence X).inverse.obj B) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u, u} _
  have := schemeModule_hasFunctorialFlatResolution X
  have (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
      CategoryTheory.Limits.PreservesColimitsOfShape ℤ
        ((curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))).flip.obj M) :=
    CategoryTheory.Limits.preservesColimitsOfShape_of_natIso (F := tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [curriedTensor]))
  have (M N : GradedObject ℤ (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
      M.HasTensor N := inferInstance
  have (M N P R : GradedObject ℤ (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
      GradedObject.HasTensor₄ObjExt M N P R := inferInstance
  have (M N P : GradedObject ℤ (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
      GradedObject.HasGoodTensor₁₂Tensor M N P := inferInstance
  have (M N P : GradedObject ℤ (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
      GradedObject.HasGoodTensorTensor₂₃ M N P := inferInstance
  have (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
      CategoryTheory.Limits.PreservesColimitsOfShape ℤ
        ((curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))).obj M) :=
    inferInstance
  have : HasExactColimitsOfShape ℤ
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance
  have (j : ℤ) : CategoryTheory.Limits.HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j}))
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance
  have : (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure := inferInstance
  let Q := DerivedCategory.Qh
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let E := schemeDerivedStandardEquivalence X
  have tensorModel (P R : HomotopyCategory
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ))
      (hP : (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat P) :
      Q.obj P ⊗ Q.obj R ≅ Q.obj (P ⊗ R) := by
    have := DerivedCategory.isIso_tensorLeftCounit P hP
    exact (asIso (DerivedCategory.tensorLeftCounit P)).app R
  let : HasDerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    HasDerivedCategory.standard _
  obtain ⟨P, hP, ⟨eP⟩⟩ := DerivedCategory.exists_kFlat_iso A
  obtain ⟨R, hR, ⟨eR⟩⟩ := DerivedCategory.exists_kFlat_iso B
  have := DerivedCategory.isIso_tensorLeftCounit P hP
  let Qs := DerivedCategory.Qh
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let c := Localization.compUniqInverse Q Qs (HomotopyCategory.quasiIso _ (.up ℤ))
  exact ⟨E.inverse.mapIso (tensorIso eP eR).symm ≪≫
    E.inverse.mapIso ((asIso (DerivedCategory.tensorLeftCounit P)).app R) ≪≫
    c.app (P ⊗ R) ≪≫ (tensorModel P R hP).symm ≪≫
    tensorIso ((c.app P).symm ≪≫ E.inverse.mapIso eP)
      ((c.app R).symm ≪≫ E.inverse.mapIso eR)⟩

end AlgebraicGeometry
