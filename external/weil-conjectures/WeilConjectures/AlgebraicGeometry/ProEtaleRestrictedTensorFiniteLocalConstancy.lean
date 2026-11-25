/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.AlgebraicGeometry.LocallyConstantTensor
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import all WeilConjectures.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullback
import all WeilConjectures.AlgebraicGeometry.SiteTensorLocalModelComparison
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import all WeilConjectures.CategoryTheory.SiteModuleSheafConstantRingEquivalence
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence

set_option linter.privateModule false

/-!
# Finite local constancy of a restricted derived tensor

Source: Stacks Project, Cohomology on Sites, Tags 094H and 07A4.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u
set_option autoImplicit false
-- Honor the sealed tensor constructions despite the package's legacy default.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 256
-- Check each sealed comparison before elaborating its consumers.
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

section Proof

-- Build total tensors directly from countable colimits, avoiding diagram-wide search.
private instance tensorTotal {C : Type*} [Category C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasColimitsOfSize.{0, 0} C]
    (P Q : CochainComplex C ℤ) :
    HomologicalComplex.HasMapBifunctor P Q (curriedTensor C) (.up ℤ) :=
  fun _ ↦ @HasColimitsOfShape.has_colimit _ _ _ _
    (@HasColimitsOfSize.has_colimits_of_shape _ _
      (inferInstance : HasColimitsOfSize.{0, 0} C) _ _) _

-- Build total tensors directly from countable colimits, avoiding diagram-wide search.
section TensorTransport
universe u₁ u₂ v₁ v₂
open CategoryTheory.MonoidalCategory
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]

end TensorTransport

attribute [local instance] Sheaf.monoidalCategory

section SmallCoefficients
universe s
variable {C : Type s} [Category.{s} C] (J : GrothendieckTopology C)
  (B : Type s) [CommRing B]

private noncomputable abbrev smallR := (sheafCompose J
  (forget₂ CommRingCat.{s} RingCat.{s})).obj
    ((constantSheaf J CommRingCat.{s}).obj (CommRingCat.of B))
private noncomputable abbrev smallScalar :
    (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ (smallR J B).obj := Functor.whiskerRight
  (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of B)))
  (forget₂ CommRingCat.{s} RingCat.{s})
private instance smallScalar_injective : Presheaf.IsLocallyInjective J (smallScalar J B) :=
  SheafOfModules.constantCommRingUnit_locallyInjective J B

private instance smallScalar_surjective : Presheaf.IsLocallySurjective J (smallScalar J B) :=
  SheafOfModules.constantCommRingUnit_locallySurjective J B

private noncomputable abbrev smallG := moduleRestriction J B (smallR J B) (smallScalar J B)

@[instance_reducible]
private noncomputable instance smallConstMonoidal :
    MonoidalCategory (PresheafOfModules.{s}
      ((Functor.const Cᵒᵖ).obj (RingCat.of B))) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{s}
    (((Functor.const Cᵒᵖ).obj (CommRingCat.of B)) ⋙ forget₂ CommRingCat RingCat)))

attribute [local irreducible] SheafOfModules.monoidalCategory Sheaf.monoidalCategory

private noncomputable abbrev smallMonoidal :=
  @SheafOfModules.monoidalCategory.{s, s, s} C _ J _
    ((constantSheaf J CommRingCat.{s}).obj (CommRingCat.of B)) _ _
    (SheafOfModules.isMonoidal_W
      ((constantSheaf J CommRingCat.{s}).obj (CommRingCat.of B)))

attribute [local instance] smallMonoidal

private theorem small_models (F : SheafOfModules.{s} (smallR J B)) :
    SheafOfModules.IsLocallyConstantFiniteType J B F ↔
    AlgebraicGeometry.Scheme.ProFiniteModels.fixedModels J B ((smallG J B).obj F) := by
  let R := smallR J B
  let α := smallScalar J B
  let G := smallG J B
  let c := SheafOfModules.strictPerfectConstantPresheaf (C := C) B ⋙
    PresheafOfModules.sheafification (R := R) α
  let ec := moduleRestrictionConstantIso J B R α
  have hi (U : C) (M : ModuleCat.{s} B) :
      Nonempty (F.over U ≅ (c.obj M).over U) ↔
      Nonempty ((G.obj F).over U ≅ (constantSheaf (J.over U) _).obj M) := by
    let αU := Functor.whiskerLeft (Over.forget U).op α
    have hαi : Presheaf.IsLocallyInjective (J.over U) αU := by
      dsimp only [αU]
      exact Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) α
    have hαs : Presheaf.IsLocallySurjective (J.over U) αU := by
      dsimp only [αU]
      exact Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) α
    let GU := @moduleRestriction.{s} (Over U) _ (J.over U) B _ (R.over U)
      αU hαi hαs
    let : GU.IsEquivalence := @moduleRestriction_isEquivalence.{s} (Over U) _
      (J.over U) B _ (R.over U) αU hαi hαs
    let hGU (N : SheafOfModules R) : GU.obj (N.over U) ≅ (G.obj N).over U :=
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ by
        dsimp only [GU, G, smallG, moduleRestriction, moduleRestrictionObj]
        exact Iso.refl _) (by intro V W f; ext x; rfl))
    let q : GU.obj ((c.obj M).over U) ≅ (constantSheaf (J.over U) _).obj M :=
      hGU (c.obj M) ≪≫ (J.overPullback _ U).mapIso (ec.app M) ≪≫
        (constantSheafOverIso J (ModuleCat.{s} B) U M).symm
    constructor
    · rintro ⟨e⟩
      exact ⟨(hGU F).symm ≪≫ GU.mapIso e ≪≫ q⟩
    · rintro ⟨e⟩
      exact ⟨GU.preimageIso (hGU F ≪≫ e ≪≫ q.symm)⟩
  constructor
  all_goals
    intro h V
    obtain ⟨S, hS, h⟩ := h V
    refine ⟨S, hS, fun U f hf ↦ ?_⟩
    obtain ⟨M, hM, he⟩ := h U f hf
    first
    | exact ⟨M, hM, (hi U M).mp he⟩
    | exact ⟨M, hM, (hi U M).mpr he⟩

end SmallCoefficients

attribute [-instance] smallConstMonoidal

namespace AlgebraicGeometry.Scheme

attribute [local instance] ProFiniteModels.asSmallDownEquivalence
  ProFiniteModels.asSmallUpEquivalence ProFiniteModels.asSmallDense
  ProFiniteModels.asSmallUpDense

private instance intrinsicMonoidalW (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ((ProEt.topology X).W.inverseImage (PresheafOfModules.toPresheaf.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).IsMonoidal :=
  SheafOfModules.isMonoidal_W_separateHomUniverse.{u + 1, u} (R := R)

@[no_expose, instance_reducible]
private noncomputable instance intrinsicRTMonoidal (X : Scheme.{u}) (A : Type u)
    [CommRing A] : MonoidalCategory (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  SheafOfModules.monoidalCategory.{u, u + 1, u + 1} (proEtaleConstantRing X A)

section EncodingTensor
-- Comparing tensor functors needs only the API, never the localization construction.
attribute [local irreducible] SheafOfModules.monoidalCategory Sheaf.monoidalCategory

end EncodingTensor

-- Use tensor comparison lemmas without reducing their localized monoidal structures.
attribute [local irreducible] SheafOfModules.monoidalCategory Sheaf.monoidalCategory

attribute [-instance] intrinsicRTMonoidal

attribute [local instance] intrinsicRTMonoidal

private instance intrinsicCountableColimits (X : Scheme.{u}) (A : Type u) [CommRing A] :
    HasColimitsOfSize.{0, 0} (proEtaleRingModules X (proEtaleConstantRing X A)) :=
  inferInstance

end AlgebraicGeometry.Scheme

end Proof
