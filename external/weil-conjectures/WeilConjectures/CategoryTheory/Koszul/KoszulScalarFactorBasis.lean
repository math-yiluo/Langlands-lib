/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Koszul.KoszulScalarTensorComparison
public import WeilConjectures.CategoryTheory.ScalarKoszulTransport.KoszulScalarTransport
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarTensorComparison
import all WeilConjectures.CategoryTheory.ScalarKoszulTransport.KoszulScalarTransport
import all WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement

/-! # KoszulScalarFactorBasis for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-koszul-scalar-factor-basis).
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

private theorem scalarTensor_inclusion (φ : R ⟶ B)
    (P Q : ringedSiteComplex R) (p q n : ℤ) (h : p + q = n) :
    (extension φ).map (CochainComplex.ιMapBifunctor P Q (tensor R) p q n h) ≫
        ((scalarTensorComparison φ).t P Q).hom.f n =
      (extensionTensorIso φ (P.X p) (Q.X q)).hom ≫
        CochainComplex.ιMapBifunctor
          (((extension φ).mapHomologicalComplex (.up ℤ)).obj P)
          (((extension φ).mapHomologicalComplex (.up ℤ)).obj Q)
          (tensor B) p q n h := by
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
  let z := (HomologicalComplex.eval (Modules B) (.up ℤ) n).mapIso
    ((scalarTensorComparison φ).t P Q).symm
  let i := CochainComplex.ιMapBifunctor P Q (tensor R) p q n h
  let i' := CochainComplex.ιMapBifunctor
    (((extension φ).mapHomologicalComplex (.up ℤ)).obj P)
    (((extension φ).mapHomologicalComplex (.up ℤ)).obj Q) (tensor B) p q n h
  have hz : i' ≫ z.hom =
      (extensionTensorIso φ (P.X p) (Q.X q)).inv ≫ (extension φ).map i := by
    change i' ≫ tensorPullbackTotalComponent (extension φ) (extensionTensorIso φ) P Q n = _
    exact HomologicalComplex.ι_mapBifunctorDesc _ p q h
  change (extension φ).map i ≫ z.inv = (extensionTensorIso φ (P.X p) (Q.X q)).hom ≫ i'
  exact ScalarKoszulTransport.inverseNaturality
    (extensionTensorIso φ (P.X p) (Q.X q)).symm z i' ((extension φ).map i) hz

private theorem scalarRankOne (φ : R ⟶ B) :
    ScalarKoszulTransport.rankOneIso (extension φ) (scalarTensorComparison φ).j =
      SheafOfModules.scalarExtensionUnitIso φ := by
  apply Iso.ext
  simp only [ScalarKoszulTransport.rankOneIso, scalarTensorComparison,
    ScalarKoszulTransport.tensorComparisonFamily, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, HomologicalComplex.Hom.isoApp_hom,
    HomologicalComplex.comp_f, Iso.app_hom,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, Category.assoc,
    Iso.inv_hom_id_assoc]
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory B
  change (extension φ).map _ ≫ (extension φ).map _ ≫ _ = _
  rw [← Functor.map_comp_assoc]
  change (extension φ).map
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one R)).inv ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one R)).hom) ≫
    (SheafOfModules.scalarExtensionUnitIso φ).hom ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one B)).inv ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (one B)).hom = _
  simp only [Iso.inv_hom_id, Category.comp_id]
  change (extension φ).map (𝟙 (one R)) ≫ _ = _
  rw [Functor.map_id, Category.id_comp]

/-- Scalar extension preserves both specified inclusions of a two-term Koszul factor.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
Proof step 1: Rewrite the inverse total tensor comparison on each inclusion using
tensorPullbackTotal_ι and cancel its component isomorphism. The resulting map is precisely the
tensor of the degreewise comparison maps.
Proof step 2: At the unit factor, singleMapHomologicalComplex identifies its zero-degree
component with scalar extension of the single-object component. Cancelling these maps proves the
rank-one formula. In each of the two factor degrees, unfold the double-complex comparison and
cancel single-object identifications, leaving this rank-one formula.
Proof step 3: For the tensor unit basis, compare inverse left unitors under scalar extension
using the module binary comparison and its unit formula; naturality and inverse cancellation
finish the identity.
(blueprint: lem-f5-koszul-scalar-factor-basis). -/
theorem scalarFactorBasis (φ : R ⟶ B)
    (s : (R.obj ⋙ forget CommRingCat).sections) (m : ℕ) (e : Bool)
    (j : (extension φ).obj (one R) ≅ one B)
    (hj : (extension φ).map (ringedKoszulScalar R s).asHom ≫ j.hom =
      j.hom ≫ (ringedKoszulScalar B (imageSections φ (fun _ : Fin 1 ↦ s) 0)).asHom) :
    (extension φ).map (factorBasis R s m e) ≫
        (ScalarKoszulTransport.factorIso (extension φ) s
          (imageSections φ (fun _ : Fin 1 ↦ s) 0)
          j hj m).hom.f
          (if e then 1 else 0) =
      j.hom ≫
        factorBasis B (imageSections φ (fun _ : Fin 1 ↦ s) 0) m e := by
  cases e
  · simp only [Fin.isValue, Bool.false_eq_true, ↓dreduceIte, factorBasis,
      ScalarKoszulTransport.factorIso, ScalarKoszulTransport.doubleComparison,
      HomologicalComplex.Hom.isoOfComponents_hom_f,
      ScalarKoszulTransport.doubleComparisonX, ↓reduceDIte,
      Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    change (extension φ).map _ ≫ (extension φ).map _ ≫ _ = _
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  · simp only [Fin.isValue, ↓dreduceIte, factorBasis,
      ScalarKoszulTransport.factorIso, ScalarKoszulTransport.doubleComparison,
      HomologicalComplex.Hom.isoOfComponents_hom_f,
      ScalarKoszulTransport.doubleComparisonX, one_ne_zero, ↓reduceDIte,
      Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    change (extension φ).map _ ≫ (extension φ).map _ ≫ _ = _
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]

private theorem scalarUnitTensor (φ : R ⟶ B) :
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.monoidalCategory B
    (extension φ).map (λ_ (one R)).inv ≫
        (extensionTensorIso φ (one R) (one R)).hom ≫
        ((SheafOfModules.scalarExtensionUnitIso φ).hom ⊗ₘ
          (SheafOfModules.scalarExtensionUnitIso φ).hom) =
      (SheafOfModules.scalarExtensionUnitIso φ).hom ≫ (λ_ (one B)).inv := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory B
  dsimp only
  apply (cancel_mono (ρ_ (one B)).hom).mp
  rw [tensorHom_def', Category.assoc, Category.assoc, Category.assoc]
  erw [rightUnitor_naturality]
  simp only [Category.assoc]
  erw [reassoc_of% (extensionTensorIso_unit φ (one R))]
  change (extension φ).map (λ_ (one R)).inv ≫
    (extension φ).map (ρ_ (one R)).hom ≫ _ = _
  rw [← Functor.map_comp_assoc]
  have hR : (λ_ (one R)).inv ≫ (ρ_ (one R)).hom = 𝟙 (one R) := by
    change (λ_ (𝟙_ (Modules R))).inv ≫ (ρ_ (𝟙_ (Modules R))).hom = _
    rw [unitors_inv_equal, Iso.inv_hom_id]
    rfl
  have hB : (λ_ (one B)).inv ≫ (ρ_ (one B)).hom = 𝟙 (one B) := by
    change (λ_ (𝟙_ (Modules B))).inv ≫ (ρ_ (𝟙_ (Modules B))).hom = _
    rw [unitors_inv_equal, Iso.inv_hom_id]
    rfl
  erw [hR, hB]
  change (extension φ).map (𝟙 (one R)) ≫ _ = _
  rw [Functor.map_id, Category.id_comp, Category.comp_id]

end CategoryTheory.FlatScalarKoszul
