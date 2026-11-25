/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictScalarKoszulInstances
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import all WeilConjectures.CategoryTheory.ScalarKoszulTransport.KoszulScalarTransport
import all WeilConjectures.Algebra.Homology.StrictScalarHom.StrictScalarHomChain
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence

/-! # KoszulScalarTensorComparison for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-koszul-scalar-tensor-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}

open MonoidalCategory
open scoped CategoryTheory.Prod

attribute [local irreducible] homComplexFunctor
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor

attribute [local instance] gradedTensorCache gradedGoodTensorLeftCache
  gradedGoodTensorRightCache gradedFourCache tensorPreservesEmptyLeftCache
  tensorPreservesEmptyRightCache cachedModuleMonoidal cachedModuleSymmetric
  cachedModulePreadditive cachedModuleClosed cachedComplexMonoidal
  cachedComplexBraided cachedComplexClosed

/-- Ordinary scalar extension, constructed using its actual sheafification maps.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-scalar-tensor-comparison). -/
def extension (φ : R ⟶ B) : Modules R ⥤ Modules B where
  obj M := SheafOfModules.changeOfRingsOfUniverses.{u, u, u, u} φ M
  map f := SheafOfModules.changeOfRingsHomOfUniverses.{u, u, u, u} φ _ f
  map_id M := SheafOfModules.scalarExtension_map_id φ M
  map_comp f g := SheafOfModules.scalarExtension_map_comp φ f g

instance scalarExtensionAdditive (φ : R ⟶ B) : (extension φ).Additive where
  map_add {M N} f g := by
    dsimp only [extension]
    apply SheafOfModules.scalarExtension_hom_ext φ M
    intro U s x
    simp only [SheafOfModules.scalarExtension_map_tmul, SheafOfModules.add_val,
      PresheafOfModules.add_app, ModuleCat.hom_add, LinearMap.add_apply]
    exact SheafOfModules.scalarExtensionSection_add φ N U s _ _

-- Elaborate the tensor and Hom comparison through their explicit site instances.
private theorem scalar_intertwines (φ : R ⟶ B)
    (s : (R.obj ⋙ forget CommRingCat).sections) :
    (extension φ).map (ringedKoszulScalar R s).asHom ≫
        (SheafOfModules.scalarExtensionUnitIso φ).hom =
      (SheafOfModules.scalarExtensionUnitIso φ).hom ≫
        (ringedKoszulScalar B (imageSections φ (fun _ : Fin 1 ↦ s) 0)).asHom := by
  apply SheafOfModules.scalarExtension_hom_ext φ (one R)
  intro U b x
  change (SheafOfModules.scalarExtensionUnitIso φ).hom.val.app U
      ((SheafOfModules.changeOfRingsHomOfUniverses.{u, u, u, u} φ _
        (ringedKoszulScalar R s).asHom).val.app U
        (SheafOfModules.scalarExtensionSection.{u, u, u, u} φ _ U b x)) = _
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [SheafOfModules.scalarExtension_map_tmul.{u, u, u, u} φ
    (ringedKoszulScalar R s).asHom U b x]
  erw [SheafOfModules.scalarExtensionUnitIso_tmul φ U b
    ((ringedKoszulScalar R s).asHom.val.app U x),
    SheafOfModules.scalarExtensionUnitIso_tmul φ U b x]
  change R.obj.obj U at x
  let sv : R.obj.obj U := s.val U
  change b * φ.hom.app U (x * sv) =
    (b * φ.hom.app U x) * φ.hom.app U sv
  rw [map_mul, mul_assoc]

private def extensionTensorIso (φ : R ⟶ B) (M N : Modules R) :
    (extension φ).obj ((tensor R).obj M |>.obj N) ≅
      (tensor B).obj ((extension φ).obj M) |>.obj ((extension φ).obj N) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory B
  exact (extension φ).mapIso (SheafOfModules.tensorIsoSite R M N) ≪≫
    SheafOfModules.scalarTensorBinaryIso φ M N ≪≫
      (SheafOfModules.tensorIsoSite B _ _).symm

private theorem extensionIso_natural (φ : R ⟶ B) {M N : Modules R} (f : M ⟶ N) :
    SheafOfModules.changeOfRingsHom φ M f ≫ (SheafOfModules.extensionIso φ N).hom =
      (SheafOfModules.extensionIso φ M).hom ≫
        (extension φ).map f := by
  apply SheafOfModules.extension_ext φ M _ _ _
  intro U x
  change _ = (SheafOfModules.changeOfRingsHomOfUniverses.{u, u, u, u} φ M f).val.app U _
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [SheafOfModules.extension_map_tmul φ f U x 1,
    SheafOfModules.extensionIso_tmul φ N U (f.val.app U x) 1,
    SheafOfModules.extensionIso_tmul φ M U x 1,
    SheafOfModules.scalarExtension_map_tmul.{u, u, u, u} φ f U 1 x]

private theorem extensionTensorIso_transport (φ : R ⟶ B) (M N : Modules R) :
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.monoidalCategory B
    (SheafOfModules.extensionIso φ (M ⊗ N)).hom ≫
        (extensionTensorIso φ M N).hom =
      (SheafOfModules.comparisonIso φ M N).hom ≫
        ((SheafOfModules.extensionIso φ M).hom ⊗ₘ
          (SheafOfModules.extensionIso φ N).hom) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory B
  dsimp only
  simp only [SheafOfModules.comparisonIso, extensionTensorIso, Iso.trans_hom,
    Iso.symm_hom, tensorIso_hom, Functor.mapIso_hom, Category.assoc]
  rw [tensorHom_comp_tensorHom]
  simp only [Iso.inv_hom_id, tensorHom_id, id_whiskerRight, Category.comp_id]
  rfl

private theorem extensionTensorIso_natural (φ : R ⟶ B)
    {M M' N N' : Modules R} (f : M ⟶ M') (g : N ⟶ N') :
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.monoidalCategory B
    (extension φ).map (f ⊗ₘ g) ≫ (extensionTensorIso φ M' N').hom =
      (extensionTensorIso φ M N).hom ≫
        ((extension φ).map f ⊗ₘ (extension φ).map g) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory B
  dsimp only
  apply (cancel_epi (SheafOfModules.extensionIso φ (M ⊗ N)).hom).mp
  rw [← Category.assoc, ← extensionIso_natural, Category.assoc,
    extensionTensorIso_transport,
    ← Category.assoc]
  erw [SheafOfModules.forward_natural φ f g]
  rw [Category.assoc,
    tensorHom_comp_tensorHom, extensionIso_natural, extensionIso_natural,
    ← tensorHom_comp_tensorHom, ← Category.assoc, ← extensionTensorIso_transport]
  simp only [Category.assoc]

private theorem tensorUnitNaturality {D : Type*} [Category D] [MonoidalCategory D]
    {A B U V : D} (f : A ⟶ B) (g : U ⟶ V) (j : V ⟶ 𝟙_ D) :
    (f ⊗ₘ g) ≫ B ◁ j ≫ (ρ_ B).hom =
      A ◁ (g ≫ j) ≫ (ρ_ A).hom ≫ f := by
  rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id,
    tensorHom_def', Category.assoc, rightUnitor_naturality]

private theorem tensorUnitTransport {D : Type*} [Category D] [MonoidalCategory D]
    {A A' M M' U U' : D} (a : A ≅ A') (b : M ≅ M') (c : U ≅ U')
    (μ : A ⟶ M ⊗ U) (μ' : A' ⟶ M' ⊗ U')
    (j : U ⟶ 𝟙_ D) (j' : U' ⟶ 𝟙_ D) (f : A ⟶ M) (f' : A' ⟶ M')
    (hμ : a.hom ≫ μ' = μ ≫ (b.hom ⊗ₘ c.hom)) (hj : j = c.hom ≫ j')
    (hu : μ ≫ M ◁ j ≫ (ρ_ M).hom = f) (hf : f ≫ b.hom = a.hom ≫ f') :
    μ' ≫ M' ◁ j' ≫ (ρ_ M').hom = f' := by
  apply (cancel_epi a.hom).mp
  rw [← Category.assoc, ← Category.assoc, hμ]
  rw [Category.assoc, Category.assoc, tensorUnitNaturality b.hom c.hom j',
    ← hj, reassoc_of% hu]
  exact hf

-- Transport the two tensor constructions and their unit constraints.
private theorem extensionTensorIso_unit (φ : R ⟶ B) (M : Modules R) :
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.monoidalCategory B
    (extensionTensorIso φ M (one R)).hom ≫
        (((extension φ).obj M ◁ (SheafOfModules.scalarExtensionUnitIso φ).hom)) ≫
        (ρ_ ((extension φ).obj M)).hom =
      (extension φ).map (ρ_ M).hom := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory B
  dsimp only
  exact tensorUnitTransport
    (SheafOfModules.extensionIso φ (M ⊗ one R))
    (SheafOfModules.extensionIso φ M) (SheafOfModules.extensionIso φ (one R))
    (SheafOfModules.comparisonIso φ M (one R)).hom
    (extensionTensorIso φ M (one R)).hom
    (SheafOfModules.comparisonUnitIso φ).hom
    (SheafOfModules.scalarExtensionUnitIso φ).hom
    (SheafOfModules.changeOfRingsHom φ _ (ρ_ M).hom) ((extension φ).map (ρ_ M).hom)
    (extensionTensorIso_transport φ M (one R)) rfl
    (SheafOfModules.forward_right_unit φ M) (extensionIso_natural φ (ρ_ M).hom)

/-- Ordinary scalar extension and its normalized total tensor comparison.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
Proof step 1: Define the functor using changeOfRingsOfUniverses and changeOfRingsHomOfUniverses,
with the existing identity and composition proofs. Check additivity on scalar-extension
generators. Check the multiplication square on generators b tensor x using multiplicativity of
the ring map.
Proof step 2: Conjugate the existing scalar-extension binary isomorphism by tensorIsoSite. On
scalar-extension generators the old and new extension functors are naturally isomorphic.
Transport binary naturality and right-unit coherence across this isomorphism, cancelling its
invertible components.
Proof step 3: Use the ordinary extension/restriction adjunction and the generic total tensor
comparison construction. Supply its unit condition by inverting the proved module right-unit
coherence.
(blueprint: lem-f5-koszul-scalar-tensor-comparison). -/
private def scalarTensorComparison (φ : R ⟶ B) :
    ScalarKoszulTransport.TensorPullbackComparison
      ((extension φ).mapHomologicalComplex (.up ℤ))
      (ringedKoszulTensor R) (ringedKoszulTensor B)
      (ringedSiteRingComplex R) (ringedSiteRingComplex B)
      (ringedKoszulRightUnitIso R) (ringedKoszulRightUnitIso B) := by
  let : IsGrothendieckAbelian.{u} (Modules R) := SheafOfModules.isGrothendieckAbelian _
  let : IsGrothendieckAbelian.{u} (Modules B) := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory B
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.symmetricCategory B
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let := Classical.choice (SheafOfModules.tensorClosed B).1
  let := SheafOfModules.monoidalClosed (R := R)
  let := SheafOfModules.monoidalClosed (R := B)
  let : HasColimitsOfSize.{0, 0} (Modules R) := hasColimitsOfSizeShrink.{0, 0, u, u} _
  let : HasColimitsOfSize.{0, 0} (Modules B) := hasColimitsOfSizeShrink.{0, 0, u, u} _
  exact ScalarKoszulTransport.tensorComparisonFamily (extension φ)
    (extensionTensorIso φ) (extensionTensorIso_natural φ) (restriction φ)
    (SheafOfModules.StrictScalarHom.ordinaryAdjunction.{u, u, u} φ)
    (SheafOfModules.scalarExtensionUnitIso φ)
    (ScalarKoszulTransport.tensorUnitInverse (extension φ) (extensionTensorIso φ)
      (SheafOfModules.scalarExtensionUnitIso φ) (fun M ↦ by
        rw [id_tensorHom]
        change (extensionTensorIso φ M (one R)).hom ≫ _ ≫ _ = _
        exact extensionTensorIso_unit φ M))

end CategoryTheory.FlatScalarKoszul
