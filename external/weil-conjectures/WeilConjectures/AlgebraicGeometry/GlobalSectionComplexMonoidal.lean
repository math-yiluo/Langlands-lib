/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.AlgebraicGeometry.GlobalSectionScalarExtension
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.AlgebraicGeometry.GlobalSectionModuleMonoidal

/-! # Tensor structure of global scalar extension on complexes

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E;
algebra.tex, Tag 00DK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite CategoryTheory.MonoidalCategory
namespace CategoryTheory

attribute [local instance] ringFamilyGlobalExtension_additive
/-- The usual total-tensor monoidal structure, with small colimit instances cached.
This is the existing `HomologicalComplex.monoidalCategory`, without any changed tensor data.
Source: Stacks Project, Tags 0996 and 099E, total tensor complexes.
(auxiliary; not a blueprint node). -/
noncomputable abbrev smallClosedCochainMonoidal
    (D : Type w) [Category.{v} D] [Preadditive D] [HasZeroObject D]
    [MonoidalCategory D] [SymmetricCategory D] [MonoidalPreadditive D]
    [MonoidalClosed D] [HasColimitsOfSize.{0, 0} D] :
    MonoidalCategory (CochainComplex D ℤ) := by
  let (X : D) : PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (ihom.adjunction X).leftAdjoint_preservesColimits
  let (X : D) : (tensorRight X).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso (BraidedCategory.tensorLeftIsoTensorRight X)
  let (X : D) : PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    (Adjunction.ofIsLeftAdjoint (tensorRight X)).leftAdjoint_preservesColimits
  let (X Y : GradedObject ℤ D) : GradedObject.HasTensor X Y := by infer_instance
  let (X Y Z : GradedObject ℤ D) :
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := by infer_instance
  let (X Y Z : GradedObject ℤ D) :
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := by infer_instance
  let (X Y Z W : GradedObject ℤ D) :
      GradedObject.HasTensor₄ObjExt X Y Z W := by infer_instance
  exact HomologicalComplex.monoidalCategory D (.up ℤ)

/-- The scalar-extension functor on complexes is strong monoidal with its prescribed
multiplication as the inverse unit constraint.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E.
(auxiliary; not a blueprint node).

Proof: use the module-level normalized strong monoidal structure and the proved small
colimit preservation. Apply the source library's additive monoidal lift to cochain
complexes; it uses these coproducts to commute the functor with total tensors. The inverse
of its unit comparison is the single-complex comparison followed by the single of the
inverse module unit. Substituting the prescribed module unit gives exactly the definition
of ringFamilyGlobalExtensionAugmentation on the identity of the degree-zero complex. -/
theorem ringFamilyGlobalExtension_complex_monoidal
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) :
    let R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)
    let A := CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O)
    let R₀ := ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj A)
    letI := SheafOfModules.isGrothendieckAbelian R
    letI := SheafOfModules.monoidalCategory O
    letI := SheafOfModules.symmetricCategory O
    letI := Classical.choice (SheafOfModules.tensorClosed O).1
    letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
    letI : Abelian (SheafOfModules.{u} R) := inferInstance
    letI : HasZeroObject (SheafOfModules.{u} R) := inferInstance
    letI : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} R) :=
      hasColimitsOfSizeShrink.{0, 0, u} _
    letI := SheafOfModules.isGrothendieckAbelian R₀
    letI := SheafOfModules.monoidalCategory A
    letI := SheafOfModules.symmetricCategory A
    letI := Classical.choice (SheafOfModules.tensorClosed A).1
    letI := Classical.choice (SheafOfModules.tensorClosed A).2.1
    letI : Abelian (RingSiteModules (ringFamilyGlobalRing O)) := inferInstance
    letI : HasZeroObject (RingSiteModules (ringFamilyGlobalRing O)) := inferInstance
    letI : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} R₀) :=
      hasColimitsOfSizeShrink.{0, 0, u} _
    letI := smallClosedCochainMonoidal (RingSiteModules (ringFamilyGlobalRing O))
    letI := smallClosedCochainMonoidal (ringedSiteModules.{u} R)
    ∃ mon : ((ringFamilyGlobalExtension O).mapHomologicalComplex (.up ℤ)).Monoidal,
      letI := mon
      Functor.OplaxMonoidal.η
          ((ringFamilyGlobalExtension O).mapHomologicalComplex (.up ℤ)) =
        ringFamilyGlobalExtensionAugmentation O (𝟙 (ringComplexSingle
          (ringFamilyGlobalRing O))) := by
  let R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)
  let A := CochainComplex.onePointRingSheaf (ringFamilyGlobalRing O)
  let R₀ := ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj A)
  let := SheafOfModules.isGrothendieckAbelian R
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let : Abelian (SheafOfModules.{u} R) := inferInstance
  let : HasZeroObject (SheafOfModules.{u} R) := inferInstance
  let : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} R) :=
    hasColimitsOfSizeShrink.{0, 0, u} _
  let := SheafOfModules.isGrothendieckAbelian R₀
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.symmetricCategory A
  let := Classical.choice (SheafOfModules.tensorClosed A).1
  let := Classical.choice (SheafOfModules.tensorClosed A).2.1
  let : Abelian (RingSiteModules (ringFamilyGlobalRing O)) := inferInstance
  let : HasZeroObject (RingSiteModules (ringFamilyGlobalRing O)) := inferInstance
  let : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} R₀) :=
    hasColimitsOfSizeShrink.{0, 0, u} _
  let := smallClosedCochainMonoidal (RingSiteModules (ringFamilyGlobalRing O))
  let := smallClosedCochainMonoidal (ringedSiteModules.{u} R)
  let (X : RingSiteModules (ringFamilyGlobalRing O)) :
      PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (ihom.adjunction X).leftAdjoint_preservesColimits
  let (X : RingSiteModules (ringFamilyGlobalRing O)) : (tensorRight X).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso (BraidedCategory.tensorLeftIsoTensorRight X)
  let (X : RingSiteModules (ringFamilyGlobalRing O)) :
      PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    (Adjunction.ofIsLeftAdjoint (tensorRight X)).leftAdjoint_preservesColimits
  let (X Y : GradedObject ℤ (RingSiteModules (ringFamilyGlobalRing O))) :
      GradedObject.HasTensor X Y := by infer_instance
  let (X Y Z : GradedObject ℤ (RingSiteModules (ringFamilyGlobalRing O))) :
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := by infer_instance
  let (X Y Z : GradedObject ℤ (RingSiteModules (ringFamilyGlobalRing O))) :
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := by infer_instance
  let (X Y Z W : GradedObject ℤ (RingSiteModules (ringFamilyGlobalRing O))) :
      GradedObject.HasTensor₄ObjExt X Y Z W := by infer_instance
  let (X : SheafOfModules.{u} R) : PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    (ihom.adjunction X).leftAdjoint_preservesColimits
  let (X : SheafOfModules.{u} R) : (tensorRight X).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso (BraidedCategory.tensorLeftIsoTensorRight X)
  let (X : SheafOfModules.{u} R) : PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    (Adjunction.ofIsLeftAdjoint (tensorRight X)).leftAdjoint_preservesColimits
  let (X Y : GradedObject ℤ (SheafOfModules.{u} R)) :
      GradedObject.HasTensor X Y := by infer_instance
  let (X Y Z : GradedObject ℤ (SheafOfModules.{u} R)) :
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := by infer_instance
  let (X Y Z : GradedObject ℤ (SheafOfModules.{u} R)) :
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := by infer_instance
  let (X Y Z W : GradedObject ℤ (SheafOfModules.{u} R)) :
      GradedObject.HasTensor₄ObjExt X Y Z W := by infer_instance
  -- Keep the instance-rich target out of the existential elimination motive.
  let hmod := ringFamilyGlobalExtension_module_monoidal O
  let mon := hmod.choose
  let hmon := hmod.choose_spec
  let := mon
  have := ringFamilyGlobalExtension_preservesColimits O
  refine ⟨Functor.mapCochainComplexMonoidal (ringFamilyGlobalExtension O), ?_⟩
  rw [Functor.mapCochainComplex_η]
  simp only [Functor.mapCochainComplexεIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Functor.Monoidal.εIso_inv, hmon,
    ringFamilyGlobalExtensionAugmentation, Functor.map_id]
  exact (Category.id_comp _).symm

end CategoryTheory
