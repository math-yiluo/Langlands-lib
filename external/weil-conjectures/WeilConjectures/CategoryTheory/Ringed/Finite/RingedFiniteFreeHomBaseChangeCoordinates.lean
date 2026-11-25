/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.IndFiniteFree.IndFiniteFreeScalarModel
import all WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
/-! # Finite-free coordinates for the scalar-Hom comparison

Source: Stacks Project, Tags 08J9 and 08JA.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace CategoryTheory

namespace FiniteFreeLocalizationProof

private def adjunction {A B D E : Type*} [Category A] [Category B]
    [Category D] [Category E] {G : A ⥤ B} {F : B ⥤ A}
    (adj : G ⊣ F) (Q : A ⥤ D) (W : MorphismProperty A) [Q.IsLocalization W]
    (Q' : B ⥤ E) (W' : MorphismProperty B) [Q'.IsLocalization W']
    (G' : D ⥤ E) (F' : E ⥤ D)
    (α : Q ⋙ G' ≅ G ⋙ Q') (χ : Q' ⋙ F' ≅ F ⋙ Q) : G' ⊣ F' := by
  let : CatCommSq G Q Q' G' := ⟨α.symm⟩
  let : CatCommSq F Q' Q F' := ⟨χ.symm⟩
  exact adj.localization Q W Q' W' G' F'

private theorem transpose {A B D E : Type*} [Category A] [Category B]
    [Category D] [Category E] {G : A ⥤ B} {F : B ⥤ A}
    (adj : G ⊣ F) (Q : A ⥤ D) (W : MorphismProperty A) [Q.IsLocalization W]
    (Q' : B ⥤ E) (W' : MorphismProperty B) [Q'.IsLocalization W']
    (G' : D ⥤ E) (F' : E ⥤ D)
    (α : Q ⋙ G' ≅ G ⋙ Q') (χ : Q' ⋙ F' ≅ F ⋙ Q)
    (X : A) (Y : B) (g : X ⟶ F.obj Y) :
    ((adjunction adj Q W Q' W' G' F' α χ).homEquiv (Q.obj X) (Q'.obj Y)).symm
      (Q.map g ≫ χ.inv.app Y) =
        α.hom.app X ≫ Q'.map ((adj.homEquiv X Y).symm g) := by
  dsimp only [adjunction]
  rw [Adjunction.homEquiv_counit, Adjunction.localization_counit_app]
  change G'.map (Q.map g ≫ χ.inv.app Y) ≫
    G'.map (χ.hom.app Y) ≫ α.hom.app (F.obj Y) ≫ Q'.map (adj.counit.app Y) = _
  rw [G'.map_comp]
  simp only [Category.assoc]
  rw [← G'.map_comp_assoc (χ.inv.app Y) (χ.hom.app Y),
    Iso.inv_hom_id_app, G'.map_id, Category.id_comp]
  have hn := α.hom.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← Q'.map_comp, Adjunction.homEquiv_counit]

private theorem unit {A B D E : Type*} [Category A] [Category B]
    [Category D] [Category E] {G : A ⥤ B} {F : B ⥤ A}
    (adj : G ⊣ F) (Q : A ⥤ D) (W : MorphismProperty A) [Q.IsLocalization W]
    (Q' : B ⥤ E) (W' : MorphismProperty B) [Q'.IsLocalization W']
    (G' : D ⥤ E) (F' : E ⥤ D)
    (α : Q ⋙ G' ≅ G ⋙ Q') (χ : Q' ⋙ F' ≅ F ⋙ Q) (X : A) :
    (adjunction adj Q W Q' W' G' F' α χ).unit.app (Q.obj X) =
      Q.map (adj.unit.app X) ≫ χ.inv.app (G.obj X) ≫ F'.map (α.inv.app X) := by
  let : CatCommSq G Q Q' G' := ⟨α.symm⟩
  let : CatCommSq F Q' Q F' := ⟨χ.symm⟩
  dsimp only [adjunction]
  exact adj.localization_unit_app Q W Q' W' G' F' X

end FiniteFreeLocalizationProof

namespace FiniteFreeClosedProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open WeilConjectures
variable {A B : Type*} [Category A] [Category B]
  {H : Aᵒᵖ × A ⥤ A} {I : Bᵒᵖ × B ⥤ B}
  (AR : CoefficientClosedStructure H) (AS : CoefficientClosedStructure I)
  {T : A ⥤ B} {U : B ⥤ A} (δ : T ⊣ U)
  (μ : AR.tensor ⋙ T ≅ T.prod T ⋙ AS.tensor)
  [Preadditive B] (K : Type*) [Ring K] [Linear K B]

private theorem basis_coordinate (P Q : A) (s : K)
    (hs : ∀ X Y : B,
      AS.tensor.map (Prod.mkHom (s • 𝟙 X) (𝟙 Y)) =
        s • 𝟙 (AS.tensor.obj (X, Y))) :
    (δ.unit.app (H.obj (op P, Q)) ≫
      U.map (s • 𝟙 (T.obj (H.obj (op P, Q))))) ≫
      U.map (AS.transpose _ (T.obj P) (T.obj Q)
        (μ.inv.app (H.obj (op P, Q), P) ≫ T.map (AR.evaluation P Q))) ≫
      (ClosedScalarHom.iso AR AS δ μ).hom.app (op P, T.obj Q) =
    H.map (Prod.mkHom (𝟙 (op P))
      (δ.unit.app Q ≫ U.map (s • 𝟙 (T.obj Q)))) := by
  let := AS.monoidal
  let c := AS.transpose _ (T.obj P) (T.obj Q)
    (μ.inv.app (H.obj (op P, Q), P) ≫ T.map (AR.evaluation P Q))
  rw [← Category.assoc]
  change ((δ.unit.app _ ≫ U.map (s • 𝟙 _)) ≫ U.map c) ≫
    (ClosedScalarHom.iso AR AS δ μ).hom.app (op P, T.obj Q) = _
  rw [← ClosedScalarHom.representing AR AS δ μ _ P (T.obj Q)
    ((δ.unit.app _ ≫ U.map (s • 𝟙 _)) ≫ U.map c)]
  dsimp only [ClosedScalarHom.bijection, Equiv.trans_apply]
  have hδ (f : T.obj (H.obj (op P, Q)) ⟶ I.obj (op (T.obj P), T.obj Q)) :
      (δ.homEquiv _ _).symm (δ.unit.app _ ≫ U.map f) = f := by
    simpa only [Adjunction.homEquiv_unit, Functor.id_obj] using
      (δ.homEquiv (H.obj (op P, Q)) _).symm_apply_apply f
  change AR.transpose _ P (U.obj (T.obj Q))
    (δ.homEquiv _ _ (μ.hom.app _ ≫
      (AS.transpose _ (T.obj P) (T.obj Q)).symm
        ((δ.homEquiv _ _).symm
          ((δ.unit.app _ ≫ U.map (s • 𝟙 _)) ≫ U.map c)) ≫ 𝟙 _)) = _
  rw [Category.assoc, ← U.map_comp]
  dsimp only [Functor.id_obj] at hδ ⊢
  erw [hδ]
  have ht : (AS.transpose _ (T.obj P) (T.obj Q)).symm ((s • 𝟙 _) ≫ c) =
      AS.tensor.map (Prod.mkHom (s • 𝟙 _) (𝟙 (T.obj P))) ≫
        (AS.transpose _ (T.obj P) (T.obj Q)).symm c := by
    rw [ClosedScalarHom.uncurry_formula, ClosedScalarHom.uncurry_formula]
    have hprod : Prod.mkHom ((s • 𝟙 (T.obj (H.obj (op P, Q)))) ≫ c)
        (𝟙 (T.obj P)) =
      Prod.mkHom (s • 𝟙 (T.obj (H.obj (op P, Q)))) (𝟙 (T.obj P)) ≫
        Prod.mkHom c (𝟙 (T.obj P)) := by simp
    rw [hprod, AS.tensor.map_comp, Category.assoc]
  rw [ht, hs, Linear.smul_comp, Category.id_comp]
  dsimp only [c]
  rw [Equiv.symm_apply_apply]
  simp only [Linear.comp_smul, Iso.hom_inv_id_app_assoc, Category.comp_id]
  have he : s • T.map (AR.evaluation P Q) =
      T.map (AR.evaluation P Q) ≫ (s • 𝟙 (T.obj Q)) := by simp
  rw [he, δ.homEquiv_naturality_right, Adjunction.homEquiv_unit]
  have hn := δ.unit.naturality (AR.evaluation P Q)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  erw [← hn]
  rw [Category.assoc]
  apply (AR.transpose _ P (U.obj (T.obj Q))).symm.injective
  rw [Equiv.symm_apply_apply]
  rw [ClosedScalarHom.uncurry_formula, ClosedScalarHom.evaluation_target]

private theorem coordinate_of_units (P Q : A) (s : K)
    (u : H.obj (op P, Q) ⟶ U.obj (T.obj (H.obj (op P, Q))))
    (v : Q ⟶ U.obj (T.obj Q))
    (hu : u = δ.unit.app _ ≫ U.map (s • 𝟙 _))
    (hv : v = δ.unit.app Q ≫ U.map (s • 𝟙 _))
    (hs : ∀ X Y : B,
      AS.tensor.map (Prod.mkHom (s • 𝟙 X) (𝟙 Y)) =
        s • 𝟙 (AS.tensor.obj (X, Y))) :
    u ≫ U.map (AS.transpose _ (T.obj P) (T.obj Q)
      (μ.inv.app (H.obj (op P, Q), P) ≫ T.map (AR.evaluation P Q))) ≫
      (ClosedScalarHom.iso AR AS δ μ).hom.app (op P, T.obj Q) =
        H.map (Prod.mkHom (𝟙 (op P)) v) := by
  rw [hu, hv]
  exact basis_coordinate AR AS δ μ K P Q s hs

omit [Preadditive B] in
private theorem evaluation_formula (P : A) (Q : B) :
    (AR.transpose _ P (U.obj Q)).symm
      ((ClosedScalarHom.iso AR AS δ μ).app (op P, Q)).hom =
    AR.tensor.map (Prod.mkHom (𝟙 (U.obj (I.obj (op (T.obj P), Q)))) (δ.unit.app P)) ≫
      δ.unit.app (AR.tensor.obj (U.obj (I.obj (op (T.obj P), Q)), U.obj (T.obj P))) ≫
      U.map (μ.hom.app (U.obj (I.obj (op (T.obj P), Q)), U.obj (T.obj P)) ≫
        AS.tensor.map (Prod.mkHom (δ.counit.app (I.obj (op (T.obj P), Q)))
          (δ.counit.app (T.obj P)))) ≫
      U.map (AS.evaluation (T.obj P) Q) := by
  simpa only [Iso.app_hom, Functor.comp_obj, Functor.prod_obj, Functor.op_obj,
    Functor.id_obj, ClosedScalarHom.restrictedEvaluation, ClosedScalarHom.restrictionTensor,
    WeilConjectures.CoefficientClosedStructure.tensor, MonoidalCategory.tensor_obj,
    Category.assoc] using
      ClosedScalarHom.evaluation AR AS δ μ P Q

end FiniteFreeClosedProof

namespace RingedFiniteFreeCoordinatesProof
open SheafOfModules MonoidalCategory
universe u₀ v₀ r₀
variable {C : Type u₀} [Category.{v₀} C] [EssentiallySmall.{r₀} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r₀} RingCat.{r₀})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r₀}]
  [HasSheafify J AddCommGrpCat.{r₀}]
  {R S : Sheaf J CommRingCat.{r₀}}

attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
  Abelian.hasFiniteBiproducts
attribute [local irreducible] monoidalCategory tensorObjIsoSheafification
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private def regularTensorIso
    (M : SheafOfModules.{r₀} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (monoidalCategory R).tensorObj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M ≅ M :=
  tensorObjIsoSheafification _ M ≪≫
    (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).mapIso (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit).app M

set_option maxHeartbeats 100000 in
-- Tensor sheafification comparisons require additional elaboration.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem regularTensorIso_inv_apply
    (M : SheafOfModules.{r₀} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Cᵒᵖ) (x : M.val.obj V) :
    (regularTensorIso M).inv.val.app V x =
      (SheafOfModules.IndFiniteFree.tensorPresheafUnit
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M).app V
        ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have : IsIso adj.counit := by dsimp [adj]; infer_instance
  let e := (asIso adj.counit).app M
  have hc : e.inv.val = adj.unit.app M.val := by
    have he : e.inv = inv (adj.counit.app M) := NatIso.isIso_inv_app adj.counit M
    rw [he]
    change (SheafOfModules.forget _).map (inv (adj.counit.app M)) = _
    rw [Functor.map_inv]
    exact adj.inv_counit_map
  let a := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have hb : e.inv.val ≫ (a.map (λ_ M.val).inv).val =
      (λ_ M.val).inv ≫ adj.unit.app (_ ⊗ M.val) := by
    rw [hc]
    exact (adj.unit.naturality (λ_ M.val).inv).symm
  have hb' := congrArg (fun k ↦ k.app V x) hb
  change (tensorObjIsoSheafification
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M).inv.val.app V
      (((e.inv.val ≫ (a.map (λ_ M.val).inv).val).app V) x) = _
  rw [hb']
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def ordinaryBasisIso (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (M : scalarModules J R) :
    (⨁ fun _ : Fin d ↦ M) ≅ (scalarRestriction φ).obj (changeOfRings φ M) := by
  let U := unit (derivedChangeRingIndependentCoefficients J R)
  let G : scalarModules J R ⥤ scalarModules J R := tensorRight M
  have : PreservesColimitsOfSize.{r₀, r₀} (tensorLeft M) :=
    tensorLeft_preservesColimits_independentCoefficients R M
  let b : tensorLeft M ≅ G := NatIso.ofComponents (fun N ↦ β_ M N)
    (fun f ↦ BraidedCategory.braiding_naturality_right M f)
  have : PreservesColimitsOfSize.{r₀, r₀} G := preservesColimits_of_natIso b
  let i₁ : (⨁ fun _ : Fin d ↦ M) ≅ ∐ fun _ : Fin d ↦ M :=
    biproduct.isoCoproduct _
  let i₂ : (∐ fun _ : Fin d ↦ M) ≅ ∐ fun _ : ULift.{r₀} (Fin d) ↦ G.obj U :=
    Sigma.whiskerEquiv (Equiv.ulift : ULift.{r₀} (Fin d) ≃ Fin d).symm
      (fun _ ↦ regularTensorIso M)
  let i₃ : (∐ fun _ : ULift.{r₀} (Fin d) ↦ G.obj U) ≅
      G.obj (free (R := derivedChangeRingIndependentCoefficients J R)
        (ULift.{r₀} (Fin d))) :=
    (PreservesCoproduct.iso G (fun _ : ULift.{r₀} (Fin d) ↦ U)).symm
  let i₄ : G.obj (free (R := derivedChangeRingIndependentCoefficients J R)
      (ULift.{r₀} (Fin d))) ≅
      G.obj ((scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S))) :=
    G.mapIso e.symm
  let i₅ : G.obj ((scalarRestriction φ).obj
      (unit (derivedChangeRingIndependentCoefficients J S))) ≅
        (scalarRestriction φ).obj (changeOfRings φ M) :=
    (IndFiniteFree.exists_extensionTensorComparison φ M).choose
  exact i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅

set_option maxHeartbeats 100000 in
-- Tensor sheafification comparisons require additional elaboration.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryBasisIso_ι (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (M : scalarModules J R) (i : Fin d) :
    biproduct.ι _ i ≫ (ordinaryBasisIso φ d e M).hom =
      (regularTensorIso M).inv ≫ ((ιFree (ULift.up i) ≫ e.inv) ▷ M) ≫
        (SheafOfModules.IndFiniteFree.exists_extensionTensorComparison φ M).choose.hom := by
  dsimp only [ordinaryBasisIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    PreservesCoproduct.inv_hom]
  simp only [biproduct.isoCoproduct_hom, biproduct.ι_desc_assoc]
  rw [Sigma.whiskerEquiv_hom, Sigma.ι_comp_map'_assoc,
    ι_comp_sigmaComparison_assoc]
  change (regularTensorIso M).inv ≫ ((ιFree (ULift.up i)) ▷ M) ≫ (e.inv ▷ M) ≫ _ = _
  rw [comp_whiskerRight, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryBasisIso_ι_apply (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (M : scalarModules J R) (i : Fin d) (V : Cᵒᵖ) (x : M.val.obj V) :
    (biproduct.ι _ i ≫ (ordinaryBasisIso φ d e M).hom).val.app V x =
      (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app V
        (((ιFree (ULift.up i) ≫ e.inv).val.app V (1 : R.obj.obj V))
          ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x) := by
  rw [ordinaryBasisIso_ι]
  change (IndFiniteFree.exists_extensionTensorComparison φ M).choose.hom.val.app V
    ((((ιFree (ULift.up i) ≫ e.inv) ▷ M).val.app V
      ((regularTensorIso M).inv.val.app V x))) = _
  rw [regularTensorIso_inv_apply]
  change (IndFiniteFree.exists_extensionTensorComparison φ M).choose.hom.val.app V
    ((((ιFree (ULift.up i) ≫ e.inv) ▷ M).val.app V
      (IndFiniteFree.pureTensor _ M V (show R.obj.obj V from 1) x))) = _
  rw [IndFiniteFree.pureTensor_whiskerRight]
  exact (IndFiniteFree.exists_extensionTensorComparison φ M).choose_spec V _ x

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev copies {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D]
    (d : ℕ) : D ⥤ D where
  obj X := ⨁ fun _ : Fin d ↦ X
  map f := biproduct.map (fun _ ↦ f)
  map_id X := by ext i j; simp
  map_comp f g := by ext i j; simp

private instance copies_additive {D : Type*} [Category D] [Preadditive D]
    [HasFiniteBiproducts D] (d : ℕ) : (copies (D := D) d).Additive where
  map_add := by
    intro X Y f g
    change biproduct.map (fun _ : Fin d ↦ f + g) =
      biproduct.map (fun _ : Fin d ↦ f) + biproduct.map (fun _ : Fin d ↦ g)
    apply biproduct.hom_ext'
    intro i
    rw [Preadditive.comp_add, biproduct.ι_map, biproduct.ι_map, biproduct.ι_map]
    simp only [Preadditive.add_comp]

private def complexCopiesIso {D : Type*} [Category D] [Abelian D]
    (d : ℕ) (F : CochainComplex D ℤ) :
    (⨁ fun _ : Fin d ↦ F) ≅ ((copies d).mapHomologicalComplex (.up ℤ)).obj F :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (HomologicalComplex.eval D (.up ℤ) n).mapBiproduct (fun _ : Fin d ↦ F)) (by
      intro n m hnm
      change ((HomologicalComplex.eval D (.up ℤ) n).mapBiproduct _).hom ≫
        biproduct.map (fun _ : Fin d ↦ F.d n m) = _
      apply biproduct.hom_ext
      intro i
      simp only [Category.assoc, biproduct.map_π, Functor.mapBiproduct_hom]
      erw [biproduct.lift_π_assoc, biproduct.lift_π]
      exact (biproduct.π (fun _ : Fin d ↦ F) i).comm n m)

private theorem complexCopiesIso_ι_f {D : Type*} [Category D] [Abelian D]
    (d : ℕ) (F : CochainComplex D ℤ) (i : Fin d) (n : ℤ) :
    (biproduct.ι (fun _ : Fin d ↦ F) i ≫ (complexCopiesIso d F).hom).f n =
      biproduct.ι (fun _ : Fin d ↦ F.X n) i := by
  dsimp only [complexCopiesIso, HomologicalComplex.comp_f,
    HomologicalComplex.Hom.isoOfComponents_hom_f]
  change (HomologicalComplex.eval D (.up ℤ) n).map (biproduct.ι _ i) ≫
    ((HomologicalComplex.eval D (.up ℤ) n).mapBiproduct _).hom = _
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc, Functor.mapBiproduct_hom]
  erw [biproduct.lift_π]
  rw [← Functor.map_comp]
  change (HomologicalComplex.eval D (.up ℤ) n).map
    (biproduct.ι (fun _ : Fin d ↦ F) i ≫ biproduct.π _ j) =
      biproduct.ι (fun _ : Fin d ↦ F.X n) i ≫
        biproduct.π (fun _ : Fin d ↦ F.X n) j
  by_cases h : i = j
  · subst j
    simp only [biproduct.ι_π_self, Functor.map_id]
    rfl
  · simp only [biproduct.ι_π_ne _ h, Functor.map_zero]

private def complexCopies {D : Type*} [Category D] [Abelian D] (d : ℕ) :
    copies (D := CochainComplex D ℤ) d ≅ (copies d).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (complexCopiesIso d) (by
    intro F G f
    apply biproduct.hom_ext'
    intro i
    dsimp only [copies]
    rw [biproduct.ι_map_assoc]
    apply HomologicalComplex.hom_ext
    intro n
    simp only [HomologicalComplex.comp_f]
    change f.f n ≫ ((biproduct.ι (fun _ : Fin d ↦ G) i).f n ≫
        (complexCopiesIso d G).hom.f n) =
      (biproduct.ι (fun _ : Fin d ↦ F) i).f n ≫
        ((complexCopiesIso d F).hom.f n ≫ biproduct.map (fun _ ↦ f.f n))
    rw [← Category.assoc ((biproduct.ι (fun _ : Fin d ↦ F) i).f n)]
    have hF := complexCopiesIso_ι_f d F i n
    have hG := complexCopiesIso_ι_f d G i n
    dsimp only [HomologicalComplex.comp_f] at hF hG
    rw [hF, hG, biproduct.ι_map])

private def inclusion {D : Type*} [Category D] [Preadditive D]
    [HasFiniteBiproducts D] (d : ℕ) (i : Fin d) : 𝟭 D ⟶ copies d where
  app X := biproduct.ι (fun _ : Fin d ↦ X) i
  naturality {X Y} f := by
    change f ≫ biproduct.ι (fun _ : Fin d ↦ Y) i =
      biproduct.ι (fun _ : Fin d ↦ X) i ≫ biproduct.map (fun _ ↦ f)
    rw [biproduct.ι_map]

private def scalarNat {D : Type*} [Category D] [Preadditive D]
    (K : Type*) [Ring K] [Linear K D] (s : K) : 𝟭 D ⟶ 𝟭 D where
  app X := s • 𝟙 X
  naturality {X Y} f := by dsimp only [Functor.id_map]; simp

private def copiesComparison {D D' : Type*} [Category D] [Category D']
    [Preadditive D] [Preadditive D'] [HasFiniteBiproducts D] [HasFiniteBiproducts D']
    (F : D ⥤ D') [F.Additive] (d : ℕ) : copies d ⋙ F ≅ F ⋙ copies d :=
  NatIso.ofComponents (fun X ↦ F.mapBiproduct (fun _ : Fin d ↦ X)) (by
    intro X Y f
    dsimp only [Functor.comp_map, copies]
    apply (cancel_epi (F.mapBiproduct (fun _ : Fin d ↦ X)).inv).1
    apply biproduct.hom_ext'
    intro i
    simp only [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc]
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc]
    change F.map (biproduct.ι (fun _ : Fin d ↦ X) i) ≫
        F.map (biproduct.map (fun _ ↦ f)) ≫
        (F.mapBiproduct (fun _ : Fin d ↦ Y)).hom ≫ biproduct.π _ j =
      F.map (biproduct.ι (fun _ : Fin d ↦ X) i) ≫
        (F.mapBiproduct (fun _ : Fin d ↦ X)).hom ≫
        biproduct.map (fun _ ↦ F.map f) ≫ biproduct.π _ j
    simp only [Functor.mapBiproduct_hom, biproduct.map_π]
    erw [biproduct.lift_π, biproduct.lift_π_assoc]
    rw [← F.map_comp_assoc, ← F.map_comp]
    simp only [Category.assoc, biproduct.map_π, F.map_comp])

private def localizedBasis {D D' : Type*} [Category D] [Category D']
    [Preadditive D] [Preadditive D'] [HasFiniteBiproducts D] [HasFiniteBiproducts D']
    (Q : D ⥤ D') [Q.Additive] (W : MorphismProperty D) [Q.IsLocalization W]
    (d : ℕ) (F : D ⥤ D) (G : D' ⥤ D')
    (b : copies d ≅ F) (χ : Q ⋙ G ≅ F ⋙ Q) : copies d ≅ G :=
  Localization.liftNatIso Q W (Q ⋙ copies d) (Q ⋙ G) (copies d) G
    ((copiesComparison Q d).symm ≪≫ Functor.isoWhiskerRight b Q ≪≫ χ.symm)

private theorem localizedBasis_app {D D' : Type*} [Category D] [Category D']
    [Preadditive D] [Preadditive D'] [HasFiniteBiproducts D] [HasFiniteBiproducts D']
    (Q : D ⥤ D') [Q.Additive] (W : MorphismProperty D) [Q.IsLocalization W]
    (d : ℕ) (F : D ⥤ D) (G : D' ⥤ D')
    (b : copies d ≅ F) (χ : Q ⋙ G ≅ F ⋙ Q) (X : D) (i : Fin d) :
    biproduct.ι _ i ≫ (localizedBasis Q W d F G b χ).hom.app (Q.obj X) ≫
      χ.hom.app X = Q.map (biproduct.ι _ i ≫ b.hom.app X) := by
  dsimp only [localizedBasis, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id]
  change biproduct.ι _ i ≫
    ((Q.mapBiproduct (fun _ : Fin d ↦ X)).inv ≫ Q.map (b.hom.app X) ≫
      χ.inv.app X) ≫ χ.hom.app X = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc]
  erw [Category.comp_id]
  exact (Q.map_comp _ _).symm

private theorem basis_transport {A B D E : Type*}
    [Category A] [Category B] [Category D] [Category E]
    [Preadditive A] [Preadditive D] [HasFiniteBiproducts A] [HasFiniteBiproducts D]
    (Q : A ⥤ D) (Q' : B ⥤ E)
    (F : A ⥤ B) (U : B ⥤ A) (F' : D ⥤ E) (U' : E ⥤ D)
    (ε : Q ⋙ F' ≅ F ⋙ Q') (χ : Q' ⋙ U' ≅ U ⋙ Q)
    (d : ℕ) (a : copies d ≅ F' ⋙ U') (b : copies d ≅ F ⋙ U)
    (hl : ∀ X i, biproduct.ι _ i ≫ a.hom.app (Q.obj X) ≫ U'.map (ε.hom.app X) =
      Q.map (biproduct.ι _ i ≫ b.hom.app X) ≫ χ.inv.app (F.obj X))
    (X : D) (Y : A) (q : Q.obj Y ≅ X) (i : Fin d) :
    q.inv ≫ Q.map (biproduct.ι (fun _ : Fin d ↦ Y) i ≫ b.hom.app Y) ≫ χ.inv.app (F.obj Y) =
      biproduct.ι _ i ≫ a.hom.app X ≫ U'.map (F'.map q.inv ≫ ε.hom.app Y) := by
  rw [← hl Y i]
  have hn := a.hom.naturality q.inv
  dsimp only [Functor.comp_map, copies] at hn
  have hi := congrArg (fun f ↦ biproduct.ι (fun _ : Fin d ↦ X) i ≫ f) hn
  simp only [biproduct.ι_map_assoc] at hi
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ f ≫ U'.map (ε.hom.app Y)) hi

private theorem localizedBasis_unit {A B D E : Type*}
    [Category A] [Category B] [Category D] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive D] [Preadditive E]
    [HasFiniteBiproducts A] [HasFiniteBiproducts D]
    (K : Type*) [Ring K] [Linear K B] [Linear K E]
    (Q : A ⥤ D) (W : MorphismProperty A) [Q.IsLocalization W]
    (Q' : B ⥤ E) [Q'.Linear K]
    (F : A ⥤ B) (U : B ⥤ A) (F' : D ⥤ E) (U' : E ⥤ D)
    (adj : F ⊣ U) (δ : F' ⊣ U')
    (ε : Q ⋙ F' ≅ F ⋙ Q') (χ : Q' ⋙ U' ≅ U ⋙ Q)
    (d : ℕ) (a : copies d ≅ F' ⋙ U') (b : copies d ≅ F ⋙ U)
    (hl : ∀ X i, biproduct.ι _ i ≫ a.hom.app (Q.obj X) ≫ U'.map (ε.hom.app X) =
      Q.map (biproduct.ι _ i ≫ b.hom.app X) ≫ χ.inv.app (F.obj X))
    (hu : ∀ X, δ.unit.app (Q.obj X) =
      Q.map (adj.unit.app X) ≫ χ.inv.app (F.obj X) ≫ U'.map (ε.inv.app X))
    (i : Fin d) (s : K)
    (hb : ∀ X, biproduct.ι _ i ≫ b.hom.app X =
      adj.unit.app X ≫ U.map (s • 𝟙 (F.obj X))) (X : D) :
    biproduct.ι _ i ≫ a.hom.app X = δ.unit.app X ≫ U'.map (s • 𝟙 (F'.obj X)) := by
  let l := inclusion d i ≫ a.hom
  let k := δ.unit ≫ Functor.whiskerRight (Functor.whiskerLeft F' (scalarNat K s)) U'
  suffices l = k from congrArg (fun z ↦ z.app X) this
  apply Localization.natTrans_ext Q W
  intro Y
  change biproduct.ι _ i ≫ a.hom.app (Q.obj Y) =
    δ.unit.app (Q.obj Y) ≫ U'.map (s • 𝟙 _)
  apply (cancel_mono (U'.map (ε.hom.app Y))).1
  rw [Category.assoc, hl, hb, Q.map_comp]
  have hn := χ.inv.naturality (s • 𝟙 (F.obj Y))
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, hn, Functor.map_smul, Functor.map_id]
  have hs : (s • 𝟙 (F'.obj (Q.obj Y))) ≫ ε.hom.app Y =
      ε.hom.app Y ≫ (s • 𝟙 (Q'.obj (F.obj Y))) := by simp
  rw [Category.assoc, ← U'.map_comp, hs, U'.map_comp, hu]
  simp only [Category.assoc, ← U'.map_comp, Iso.inv_hom_id_app_assoc]

universe w₁
variable [HasDerivedCategory.{w₁} (scalarModules J R)]
  [HasDerivedCategory.{w₁} (scalarModules J S)]

private def scalarModel (φ : R ⟶ S) :
    DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ :=
  (nonempty_derivedChangeOfRingsCochainModel φ).some

attribute [local irreducible] scalarModel

private def moduleBasisIso (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ)
    (M : scalarModules J R) :
    (copies d).obj M ≅ (scalarRestriction φ).obj (m.E.obj M) :=
  ordinaryBasisIso φ d e M ≪≫ (scalarRestriction φ).mapIso (eqToIso (m.obj_eq M).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem moduleBasisIso_ι_apply (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ)
    (M : scalarModules J R) (i : Fin d) (V : Cᵒᵖ) (x : M.val.obj V) :
    (biproduct.ι _ i ≫ (moduleBasisIso φ d e m M).hom).val.app V x =
      IndFiniteFree.extensionPure m M V
        ((ιFree (ULift.up i) ≫ e.inv).val.app V (1 : R.obj.obj V)) x := by
  change (eqToHom (m.obj_eq M).symm).val.app V
    ((biproduct.ι _ i ≫ (ordinaryBasisIso φ d e M).hom).val.app V x) = _
  rw [ordinaryBasisIso_ι_apply]
  rfl

attribute [local irreducible] ordinaryBasisIso regularTensorIso moduleBasisIso

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def moduleBasis (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ) :
    copies d ≅ m.E ⋙ scalarRestriction φ :=
  NatIso.ofComponents (moduleBasisIso φ d e m) (by
    intro M N f
    dsimp only [copies, Functor.comp_map]
    apply biproduct.hom_ext'
    intro i
    change biproduct.ι _ i ≫ biproduct.map (fun _ ↦ f) ≫ _ = _
    rw [biproduct.ι_map_assoc]
    apply SheafOfModules.hom_ext
    ext V x
    change (biproduct.ι _ i ≫ (moduleBasisIso φ d e m N).hom).val.app V
      (f.val.app V x) =
      (m.E.map f).val.app V
        ((biproduct.ι _ i ≫ (moduleBasisIso φ d e m M).hom).val.app V x)
    rw [moduleBasisIso_ι_apply, moduleBasisIso_ι_apply]
    exact (IndFiniteFree.extensionPure_naturality m f V _ x).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem model_finite_limits (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ) :
    PreservesFiniteLimits m.E := by
  have := (sheafRingCoefficientOrdinaryAdjunction φ).choose
  have := (sheafRingCoefficientOrdinaryAdjunction φ).choose_spec.choose
  let A := (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S))
  let U := unit (derivedChangeRingIndependentCoefficients J R)
  let e' : A ≅ ∏ᶜ fun _ : Fin d ↦ U := e ≪≫
    Sigma.whiskerEquiv (Equiv.ulift : ULift.{r₀} (Fin d) ≃ Fin d)
      (fun _ ↦ Iso.refl U) ≪≫
    (biproduct.isoCoproduct _).symm ≪≫ biproduct.isoProduct _
  have : PreservesFiniteLimits
      (tensorLeft ((IndFiniteFree.algebraModules R).obj (Under.mk φ))) :=
    IndFiniteFree.tensorLeft_finiteFree_finiteLimits A d e'
  have : PreservesFiniteLimits (m.E ⋙ scalarRestriction φ) :=
    preservesFiniteLimits_of_natIso (IndFiniteFree.ordinaryComparison m)
  have : (scalarRestriction φ).ReflectsIsomorphisms := by
    have : (scalarRestriction φ ⋙ toSheaf
        (derivedChangeRingIndependentCoefficients J R)).ReflectsIsomorphisms :=
      inferInstanceAs
        ((toSheaf (derivedChangeRingIndependentCoefficients J S)).ReflectsIsomorphisms)
    exact reflectsIsomorphisms_of_comp _ (toSheaf _)
  exact preservesFiniteLimits_of_reflects_of_preserves m.E (scalarRestriction φ)

omit [EssentiallySmall.{r₀} C]
  [HasDerivedCategory.{w₁} (scalarModules J R)]
  [HasDerivedCategory.{w₁} (scalarModules J S)] in
private theorem normalizedOrdinaryAdjunction (φ : R ⟶ S)
    (E : scalarModules J R ⥤ scalarModules J S)
    (h : ∀ M, E.obj M = changeOfRings φ M)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    [E.Additive] : ∃ adj : E ⊣ scalarRestriction φ,
      ∀ (M : scalarModules J R) (V : Cᵒᵖ) (x : M.val.obj V),
        (adj.unit.app M).val.app V x =
          (eqToHom (h M).symm).val.app V
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
                (changeOfRingsPresheaf φ M)).app V
              ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  all_goals
    have ha := (sheafRingCoefficientOrdinaryAdjunction φ).choose_spec.choose_spec E h hm
    let adj := ha.choose
    have hu := ha.choose_spec
    refine ⟨adj, ?_⟩
    intro M V x
    have hh := hu M (E.obj M) (eqToHom (h M).symm) V x
    simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at hh
    exact hh

private def modelIso (φ : R ⟶ S)
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ)
    (E : scalarModules J R ⥤ scalarModules J S)
    (h : ∀ M, E.obj M = changeOfRings φ M)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ changeOfRingsHom φ M f ≫ eqToHom (h N).symm) : E ≅ m.E :=
  NatIso.ofComponents (fun M ↦ eqToIso ((h M).trans (m.obj_eq M).symm)) (by
    intro M N f
    rw [hm, m.map_eq]
    simp)

private theorem modelIso_inv_app (φ : R ⟶ S)
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ)
    (E : scalarModules J R ⥤ scalarModules J S)
    (h : ∀ M, E.obj M = changeOfRings φ M)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    (M : scalarModules J R) :
    (modelIso φ m E h hm).inv.app M =
      eqToHom ((h M).trans (m.obj_eq M).symm).symm := rfl

attribute [local irreducible] modelIso

private def chainBasis (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ) :
    copies d ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙
      (scalarRestriction φ).mapHomologicalComplex (.up ℤ) :=
  complexCopies d ≪≫ NatIso.mapHomologicalComplex (moduleBasis φ d e m) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm

private theorem chainBasis_ι_f (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ)
    (F : CochainComplex (scalarModules J R) ℤ) (i : Fin d) (n : ℤ) :
    (biproduct.ι _ i ≫ (chainBasis φ d e m).hom.app F).f n =
      biproduct.ι _ i ≫ (moduleBasisIso φ d e m (F.X n)).hom := by
  change (biproduct.ι _ i ≫ (complexCopiesIso d F).hom ≫
    ((NatIso.mapHomologicalComplex (moduleBasis φ d e m) (.up ℤ)).hom.app F) ≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).inv.app F)).f n = _
  change (biproduct.ι (fun _ : Fin d ↦ F) i).f n ≫ (complexCopiesIso d F).hom.f n ≫
    (moduleBasisIso φ d e m (F.X n)).hom ≫ 𝟙 _ = _
  rw [Category.comp_id, ← Category.assoc, ← HomologicalComplex.comp_f,
    complexCopiesIso_ι_f]

attribute [local irreducible] chainBasis moduleBasis

private def chainBasisE (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ)
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive] (eE : E ≅ m.E) :
    copies d ≅ E.mapHomologicalComplex (.up ℤ) ⋙
      (scalarRestriction φ).mapHomologicalComplex (.up ℤ) :=
  chainBasis φ d e m ≪≫ Functor.isoWhiskerRight
    (NatIso.mapHomologicalComplex eE.symm (.up ℤ)) _

private theorem chainBasisE_ι_f (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ)
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive] (eE : E ≅ m.E)
    (F : CochainComplex (scalarModules J R) ℤ) (i : Fin d) (n : ℤ) :
    (biproduct.ι _ i ≫ (chainBasisE φ d e m E eE).hom.app F).f n =
      (biproduct.ι _ i ≫ (moduleBasisIso φ d e m (F.X n)).hom) ≫
        (scalarRestriction φ).map (eE.inv.app (F.X n)) := by
  change (biproduct.ι _ i ≫ (chainBasis φ d e m).hom.app F ≫
    ((scalarRestriction φ).mapHomologicalComplex (.up ℤ)).map
      ((NatIso.mapHomologicalComplex eE.symm (.up ℤ)).hom.app F)).f n = _
  rw [← Category.assoc, HomologicalComplex.comp_f, chainBasis_ι_f]
  rfl

private theorem chainBasisModel_ι_apply (φ : R ⟶ S) (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{r₀} (Fin d)))
    (m : DerivedChangeOfRingsCochainModel.{u₀, v₀, r₀, w₁, w₁} φ)
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive]
    (h : ∀ M, E.obj M = changeOfRings φ M)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f =
      eqToHom (h M) ≫ changeOfRingsHom φ M f ≫ eqToHom (h N).symm)
    (F : CochainComplex (scalarModules J R) ℤ) (i : Fin d) (n : ℤ)
    (V : Cᵒᵖ) (x : (F.X n).val.obj V) :
    ((biproduct.ι _ i ≫
      (chainBasisE φ d e m E (modelIso φ m E h hm)).hom.app F).f n).val.app V x =
      (eqToHom (h (F.X n)).symm).val.app V
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
            (changeOfRingsPresheaf φ (F.X n))).app V
          (((ιFree (ULift.up i) ≫ e.inv).val.app V (1 : R.obj.obj V))
            ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)) := by
  rw [chainBasisE_ι_f]
  change ((modelIso φ m E h hm).inv.app (F.X n)).val.app V
    ((biproduct.ι _ i ≫ (moduleBasisIso φ d e m (F.X n)).hom).val.app V x) = _
  rw [moduleBasisIso_ι_apply, modelIso_inv_app]
  change ((eqToHom (m.obj_eq (F.X n)).symm ≫
    eqToHom ((h (F.X n)).trans (m.obj_eq (F.X n)).symm).symm).val.app V) _ = _
  rw [eqToHom_trans]
  rfl

private def restrictionFactors (φ : R ⟶ S)
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive]
    (T : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Q ⋙ T ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    DerivedCategory.Q ⋙ (T ⋙ scalarDerivedRestriction.{u₀, v₀, r₀, w₁} φ) ≅
      (E.mapHomologicalComplex (.up ℤ) ⋙
        (scalarRestriction φ).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ε _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (scalarRestrictionComparison φ) ≪≫
    (Functor.associator _ _ _).symm

private theorem restrictionFactors_hom_app (φ : R ⟶ S)
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive]
    (T : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Q ⋙ T ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F : CochainComplex (scalarModules J R) ℤ) :
    (restrictionFactors φ E T ε).hom.app F =
      (scalarDerivedRestriction φ).map (ε.hom.app F) ≫
        (scalarRestrictionComparison φ).hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj F) := by
  simp only [restrictionFactors, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] scalarDerivedRestriction scalarRestrictionComparison
  FiniteFreeLocalizationProof.adjunction

private def derivedAdjunction (φ : R ⟶ S)
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive]
    (T : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Q ⋙ T ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (adj : E ⊣ scalarRestriction φ) : T ⊣ scalarDerivedRestriction φ :=
  FiniteFreeLocalizationProof.adjunction (adj.mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ)) T
    (scalarDerivedRestriction φ) ε (scalarRestrictionComparison φ)

private theorem derivedAdjunction_transpose (φ : R ⟶ S)
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive]
    (T : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Q ⋙ T ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (adj : E ⊣ scalarRestriction φ)
    (F : CochainComplex (scalarModules J R) ℤ)
    (N : CochainComplex (scalarModules J S) ℤ)
    (g : F ⟶ ((scalarRestriction φ).mapHomologicalComplex (.up ℤ)).obj N) :
    ((derivedAdjunction φ E T ε adj).homEquiv
      (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj N)).symm
        (DerivedCategory.Q.map g ≫ (scalarRestrictionComparison φ).inv.app N) =
      ε.hom.app F ≫ DerivedCategory.Q.map
        (((adj.mapHomologicalComplex (.up ℤ)).homEquiv F N).symm g) :=
  FiniteFreeLocalizationProof.transpose (adj.mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ)) T
    (scalarDerivedRestriction φ) ε (scalarRestrictionComparison φ) F N g

private theorem derivedAdjunction_unit (φ : R ⟶ S)
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive]
    (T : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Q ⋙ T ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (adj : E ⊣ scalarRestriction φ) (F : CochainComplex (scalarModules J R) ℤ) :
    (derivedAdjunction φ E T ε adj).unit.app (DerivedCategory.Q.obj F) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app F) ≫
        (scalarRestrictionComparison φ).inv.app
          ((E.mapHomologicalComplex (.up ℤ)).obj F) ≫
        (scalarDerivedRestriction φ).map (ε.inv.app F) :=
  FiniteFreeLocalizationProof.unit (adj.mapHomologicalComplex (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ)) T
    (scalarDerivedRestriction φ) ε (scalarRestrictionComparison φ) F

attribute [local irreducible] derivedAdjunction

private theorem localizedBasis_restriction (φ : R ⟶ S)
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive]
    (T : DerivedCategory (scalarModules J R) ⥤ DerivedCategory (scalarModules J S))
    (ε : DerivedCategory.Q ⋙ T ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (d : ℕ) (b : copies d ≅ E.mapHomologicalComplex (.up ℤ) ⋙
      (scalarRestriction φ).mapHomologicalComplex (.up ℤ))
    (F : CochainComplex (scalarModules J R) ℤ) (i : Fin d) :
    biproduct.ι _ i ≫
      (localizedBasis DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ)) d _ _ b
        (restrictionFactors φ E T ε)).hom.app (DerivedCategory.Q.obj F) ≫
          (scalarDerivedRestriction φ).map (ε.hom.app F) =
      DerivedCategory.Q.map (biproduct.ι _ i ≫ b.hom.app F) ≫
        (scalarRestrictionComparison φ).inv.app ((E.mapHomologicalComplex (.up ℤ)).obj F) := by
  have hh := localizedBasis_app DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) d _ _ b (restrictionFactors φ E T ε) F i
  rw [restrictionFactors_hom_app] at hh
  apply (cancel_mono ((scalarRestrictionComparison φ).hom.app
    ((E.mapHomologicalComplex (.up ℤ)).obj F))).1
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    Functor.comp_obj] using hh

attribute [local irreducible] chainBasisE localizedBasis

end RingedFiniteFreeCoordinatesProof

private instance sectionLinearIndependent {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (S : Sheaf J CommRingCat.{r}) :
    Linear (RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
      (SheafOfModules.scalarModules J S) :=
  SheafOfModules.homLinear S.obj
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).property

private instance derivedSectionLinear {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (S : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J S)] :
    Linear (RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
      (DerivedCategory (SheafOfModules.scalarModules J S)) :=
  DerivedCategory.instLinear _ _

private instance sectionQLinear {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (S : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J S)] :
    Functor.Linear (RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat))
      (DerivedCategory.Q : CochainComplex (SheafOfModules.scalarModules J S) ℤ ⥤ _) := by
  unfold derivedSectionLinear
  infer_instance

attribute [local irreducible] derivedSectionLinear

private theorem kflatRepresentative {C : Type c} [Category.{v} C]
    [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (S : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J S)]
    (X : DerivedCategory (SheafOfModules.scalarModules J S)) :
    ∃ F : CochainComplex (SheafOfModules.scalarModules J S) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S) F ∧
        Nonempty (DerivedCategory.Q.obj F ≅ X) := by
  obtain ⟨F, f, hF, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{r, c, v}
      (C := C) (J := J) (R := S) (DerivedCategory.Q.objPreimage X)
  let := hf
  exact ⟨F, hF, ⟨asIso (DerivedCategory.Q.map f) ≪≫
    DerivedCategory.Q.objObjPreimageIso X⟩⟩

open MonoidalCategory in
private theorem totalTensorScalar {D : Type*} [Category D] [Preadditive D]
    [MonoidalCategory D] [MonoidalPreadditive D]
    (K : Type*) [Ring K] [Linear K D]
    (P Q : CochainComplex D ℤ)
    [HomologicalComplex.HasMapBifunctor P Q (MonoidalCategory.curriedTensor D) (.up ℤ)]
    (s : K) (h : ∀ X Y : D, (s • 𝟙 X) ▷ Y = s • 𝟙 (X ⊗ Y)) :
    HomologicalComplex.mapBifunctorMap (s • 𝟙 P) (𝟙 Q)
      (MonoidalCategory.curriedTensor D) (.up ℤ) = s • 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [HomologicalComplex.ι_mapBifunctorMap]
  change ((s • 𝟙 (P.X p)) ▷ Q.X q) ≫ (P.X p ◁ 𝟙 (Q.X q)) ≫ _ =
    _ ≫ (s • 𝟙 _)
  rw [h]
  simp only [MonoidalCategory.whiskerLeft_id, Linear.smul_comp, Linear.comp_smul,
    Category.id_comp, Category.comp_id]

open MonoidalCategory in
private theorem totalTensorFunctorScalar {D : Type*} [Category D] [Preadditive D]
    [MonoidalCategory D] [MonoidalPreadditive D]
    (K : Type*) [Ring K] [Linear K D]
    [∀ X Y : CochainComplex D ℤ,
      HomologicalComplex.HasMapBifunctor X Y (curriedTensor D) (.up ℤ)]
    (P Q : CochainComplex D ℤ) (s : K)
    (h : ∀ X Y : D, (s • 𝟙 X) ▷ Y = s • 𝟙 (X ⊗ Y)) :
    (Functor.uncurry.obj ((curriedTensor D).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))).map (Prod.mkHom (s • 𝟙 P) (𝟙 Q)) =
        s • 𝟙 (HomologicalComplex.mapBifunctor P Q (curriedTensor D) (.up ℤ)) := by
  change HomologicalComplex.mapBifunctorMap (s • 𝟙 P) (𝟙 Q) _ _ ≫
    HomologicalComplex.mapBifunctorMap (𝟙 P) (𝟙 Q) _ _ = _
  rw [totalTensorScalar K P Q s h]
  have hi : HomologicalComplex.mapBifunctorMap (𝟙 P) (𝟙 Q)
      (curriedTensor D) (.up ℤ) = 𝟙 _ := by
    simp [HomologicalComplex.mapBifunctorMap]
  rw [hi, Category.comp_id]

section Site
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

namespace FiniteFreeScalarProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open SheafOfModules MonoidalCategory WeilConjectures
attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
attribute [local irreducible] monoidalCategory tensorObjIsoSheafification
  derivedInternalHomOfUniverses SheafOfModules.homLinear SheafOfModules.homModule

private abbrev sections (S : Sheaf J CommRingCat.{max c v r}) :=
  RingCat.sectionsSubring (S.obj ⋙ forget₂ CommRingCat RingCat)

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] in
private theorem smul_apply (M N : scalarModules J S) (f : M ⟶ N)
    (s : sections.{c, v, r} J S) (V : Cᵒᵖ) (x : M.val.obj V) :
    (s • f).val.app V x = (show S.obj.obj V from s.val V) • f.val.app V x := by
  unfold sectionLinearIndependent SheafOfModules.homLinear SheafOfModules.homModule
  rfl

private theorem tensor_smul (M N : scalarModules J S) (s : sections.{c, v, r} J S) :
    (s • 𝟙 M) ▷ N = s • 𝟙 (M ⊗ N) := by
  apply IndFiniteFree.pureTensor_ext
  intro V x y
  rw [IndFiniteFree.pureTensor_whiskerRight, smul_apply.{c, v, r},
    smul_apply.{c, v, r}]
  change IndFiniteFree.pureTensor M N V (s.val V • x) y =
    s.val V • IndFiniteFree.pureTensor M N V x y
  dsimp only [IndFiniteFree.pureTensor]
  rw [← ((tensorObjIsoSheafification M N).inv.val.app V).hom.map_smul]
  rw [← (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
      (M.val ⊗ N.val)).app V).hom.map_smul]
  congr 2

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem totalTensor_smul
    (P Q : CochainComplex (scalarModules J S) ℤ) (s : sections.{c, v, r} J S) :
    (coefficientTotalTensor.{r, c, v} J S).map
      (Prod.mkHom (s • 𝟙 P) (𝟙 Q)) =
        s • 𝟙 ((coefficientTotalTensor.{r, c, v} J S).obj (P, Q)) := by
  exact totalTensorFunctorScalar (sections.{c, v, r} J S) P Q s
    (fun X Y ↦ tensor_smul.{c, v, r} J X Y s)

private theorem tensor_smul_iso {D : Type*} [Category D] [Preadditive D]
    (K : Type*) [Ring K] [Linear K D] (F : D × D ⥤ D)
    {X Y X' Y' : D} (e : X' ≅ X) (f : Y' ≅ Y) (s : K)
    (h : F.map (Prod.mkHom (s • 𝟙 X') (𝟙 Y')) = s • 𝟙 _) :
    F.map (Prod.mkHom (s • 𝟙 X) (𝟙 Y)) = s • 𝟙 _ := by
  let ef : (X', Y') ≅ (X, Y) :=
    { hom := Prod.mkHom e.hom f.hom
      inv := Prod.mkHom e.inv f.inv }
  apply (cancel_epi (F.mapIso ef).hom).1
  change F.map (Prod.mkHom e.hom f.hom) ≫ _ =
    F.map (Prod.mkHom e.hom f.hom) ≫ _
  have hn : F.map (Prod.mkHom e.hom f.hom) ≫
      F.map (Prod.mkHom (s • 𝟙 X) (𝟙 Y)) =
    F.map (Prod.mkHom (s • 𝟙 X') (𝟙 Y')) ≫
      F.map (Prod.mkHom e.hom f.hom) := by
    rw [← F.map_comp, ← F.map_comp]
    congr 1
    ext <;> simp
  rw [hn, h]
  simp

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarComparison {A D : Type*} [Category A] [Category D]
    [Preadditive A] [Preadditive D] (K : Type*) [Ring K] [Linear K A] [Linear K D]
    (Q : A ⥤ D) [Functor.Linear K Q] (F : A × A ⥤ A) (G : D × D ⥤ D)
    (P : ObjectProperty A) (e : (P.ι.prod P.ι) ⋙ F ⋙ Q ≅
      (P.ι ⋙ Q).prod (P.ι ⋙ Q) ⋙ G)
    (X Y : P.FullSubcategory) (s : K)
    (h : F.map (Prod.mkHom (s • 𝟙 X.obj) (𝟙 Y.obj)) =
      s • 𝟙 (F.obj (X.obj, Y.obj))) :
    G.map (Prod.mkHom (s • 𝟙 (Q.obj X.obj)) (𝟙 (Q.obj Y.obj))) = s • 𝟙 _ := by
  have hn := e.hom.naturality
    (Prod.mkHom (ObjectProperty.homMk (s • 𝟙 X.obj)) (𝟙 Y))
  change Q.map (F.map (Prod.mkHom (s • 𝟙 X.obj) (𝟙 Y.obj))) ≫
    (e.app (X, Y)).hom = (e.app (X, Y)).hom ≫
      G.map (Prod.mkHom (Q.map (s • 𝟙 X.obj)) (Q.map (𝟙 Y.obj))) at hn
  rw [h] at hn
  have hx : Q.map (𝟙 X.obj) = 𝟙 (Q.obj X.obj) := Q.map_id X.obj
  have hy : Q.map (𝟙 Y.obj) = 𝟙 (Q.obj Y.obj) := Q.map_id Y.obj
  have hz : Q.map (𝟙 (F.obj (X.obj, Y.obj))) = 𝟙 _ := Q.map_id _
  have hs : Q.map (s • 𝟙 X.obj) = s • 𝟙 (Q.obj X.obj) := by
    rw [Q.map_smul, hx]
  rw [Q.map_smul, hz, hs, hy] at hn
  apply (cancel_epi (e.app (X, Y)).hom).1
  calc
    _ = (s • 𝟙 (Q.obj (F.obj (X.obj, Y.obj)))) ≫ (e.app (X, Y)).hom := hn.symm
    _ = s • (e.app (X, Y)).hom := by rw [Linear.smul_comp, Category.id_comp]
    _ = _ := by
      rw [Linear.comp_smul]
      exact congrArg (fun t ↦ s • t) (Category.comp_id (e.app (X, Y)).hom).symm

private theorem scalarComparisonAll {A D : Type*} [Category A] [Category D]
    [Preadditive A] [Preadditive D] (K : Type*) [Ring K] [Linear K A] [Linear K D]
    (Q : A ⥤ D) [Functor.Linear K Q] (F : A × A ⥤ A) (G : D × D ⥤ D)
    (P : ObjectProperty A) (e : (P.ι.prod P.ι) ⋙ F ⋙ Q ≅
      (P.ι ⋙ Q).prod (P.ι ⋙ Q) ⋙ G)
    (hc : ∀ X : D, ∃ Y : P.FullSubcategory, Nonempty (Q.obj Y.obj ≅ X))
    (h : ∀ X Y : P.FullSubcategory, ∀ s : K,
      F.map (Prod.mkHom (s • 𝟙 X.obj) (𝟙 Y.obj)) = s • 𝟙 (F.obj (X.obj, Y.obj)))
    (X Y : D) (s : K) :
    G.map (Prod.mkHom (s • 𝟙 X) (𝟙 Y)) = s • 𝟙 (G.obj (X, Y)) := by
  obtain ⟨X', ⟨a⟩⟩ := hc X
  obtain ⟨Y', ⟨b⟩⟩ := hc Y
  exact tensor_smul_iso K G a b s (scalarComparison K Q F G P e X' Y' s (h X' Y' s))

attribute [local irreducible] coefficientTotalTensor DerivedCategory.instLinear
  CoefficientClosedStructure.tensor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem derivedTensor_smul (S : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (scalarModules J S)]
    (AS : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J S))
    (MS : CoefficientTensorModels.{r, c, v, w} J S AS)
    (X Y : DerivedCategory (scalarModules J S)) (s : sections.{c, v, r} J S) :
    AS.tensor.map (Prod.mkHom (s • 𝟙 X) (𝟙 Y)) =
      s • 𝟙 (AS.tensor.obj (X, Y)) := by
  let K : ObjectProperty (CochainComplex (scalarModules J S) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
  let b : (K.ι.prod K.ι) ⋙ coefficientTotalTensor.{r, c, v} J S ⋙ DerivedCategory.Q ≅
      (K.ι ⋙ DerivedCategory.Q).prod (K.ι ⋙ DerivedCategory.Q) ⋙ AS.tensor :=
    MS.comparison
  apply scalarComparisonAll (sections.{c, v, r} J S) DerivedCategory.Q
    (coefficientTotalTensor.{r, c, v} J S) AS.tensor K b ?_ ?_ X Y s
  · intro X
    obtain ⟨F, hF, he⟩ := kflatRepresentative.{c, v, max c v r, w} S X
    exact ⟨⟨F, hF⟩, he⟩
  · intro P Q s
    exact totalTensor_smul.{c, v, r} J P.obj Q.obj s

end FiniteFreeScalarProof

/-- The basis components of a finite-free scalar-extension isomorphism, specified
on every K-flat representative. The degreewise map is multiplication by the actual
basis section, followed by sheafification; the localization square fixes its derived class.
Source: Stacks Project, Tags 08J9 and 08JA.
(blueprint: lem-sf-ringed-finite-free-hom-coordinates). -/
def RingedFiniteFreeBasisCoordinates
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J R)]
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J S)]
    (d : ℕ) (e : (SheafOfModules.scalarRestriction φ).obj
      (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
      SheafOfModules.free
        (R := SheafOfModules.derivedChangeRingIndependentCoefficients J R)
        (ULift.{max c v r} (Fin d)))
    (E : SheafOfModules.scalarModules J R ⥤ SheafOfModules.scalarModules J S)
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    [E.Additive]
    (T : DerivedCategory (SheafOfModules.scalarModules J R) ⥤
      DerivedCategory (SheafOfModules.scalarModules J S))
    (ε : DerivedCategory.Q ⋙ T ⟶
      E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (X : DerivedCategory (SheafOfModules.scalarModules J R))
    (a : (⨁ fun _ : Fin d ↦ X) ≅ (SheafOfModules.scalarDerivedRestriction φ).obj
      (T.obj X)) : Prop :=
  ∀ (F : CochainComplex (SheafOfModules.scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) F →
    ∀ (q : DerivedCategory.Q.obj F ≅ X) (j : Fin d),
    ∃ b : F ⟶ ((SheafOfModules.scalarRestriction φ).mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj F),
      (∀ (n : ℤ) (V : Cᵒᵖ) (x : (F.X n).val.obj V),
        (b.f n).val.app V x = ringedFiniteFreeScalarSection.{c, v, r} J φ E h (F.X n) V
          (((SheafOfModules.ιFree (ULift.up j) ≫ e.inv).val.app V)
            (show R.obj.obj V from 1)) x) ∧
      q.inv ≫ DerivedCategory.Q.map b ≫
          (SheafOfModules.scalarRestrictionComparison φ).inv.app
            ((E.mapHomologicalComplex (.up ℤ)).obj F) =
        biproduct.ι _ j ≫ a.hom ≫
          (SheafOfModules.scalarDerivedRestriction φ).map (T.map q.inv ≫ ε.app F)

private theorem basisCoordinates_of_components
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J R)]
    [HasDerivedCategory.{w} (SheafOfModules.scalarModules J S)]
    (d : ℕ) (e : (SheafOfModules.scalarRestriction φ).obj
      (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
      SheafOfModules.free
        (R := SheafOfModules.derivedChangeRingIndependentCoefficients J R)
        (ULift.{max c v r} (Fin d)))
    (E : SheafOfModules.scalarModules J R ⥤ SheafOfModules.scalarModules J S)
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M) [E.Additive]
    (T : DerivedCategory (SheafOfModules.scalarModules J R) ⥤
      DerivedCategory (SheafOfModules.scalarModules J S))
    (ε : DerivedCategory.Q ⋙ T ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (a : RingedFiniteFreeCoordinatesProof.copies d ≅
      T ⋙ SheafOfModules.scalarDerivedRestriction φ)
    (b : RingedFiniteFreeCoordinatesProof.copies d ≅ E.mapHomologicalComplex (.up ℤ) ⋙
      (SheafOfModules.scalarRestriction φ).mapHomologicalComplex (.up ℤ))
    (hb : ∀ (F : CochainComplex (SheafOfModules.scalarModules J R) ℤ)
      (i : Fin d) (n : ℤ) (V : Cᵒᵖ) (x : (F.X n).val.obj V),
      ((biproduct.ι (fun _ : Fin d ↦ F) i ≫ b.hom.app F).f n).val.app V x =
        ringedFiniteFreeScalarSection.{c, v, r} J φ E h (F.X n) V
          ((SheafOfModules.ιFree (ULift.up i) ≫ e.inv).val.app V (1 : R.obj.obj V)) x)
    (hl : ∀ F i, biproduct.ι _ i ≫ a.hom.app (DerivedCategory.Q.obj F) ≫
      (SheafOfModules.scalarDerivedRestriction φ).map (ε.hom.app F) =
      DerivedCategory.Q.map (biproduct.ι _ i ≫ b.hom.app F) ≫
        (SheafOfModules.scalarRestrictionComparison φ).inv.app
          ((E.mapHomologicalComplex (.up ℤ)).obj F))
    (X : DerivedCategory (SheafOfModules.scalarModules J R)) :
    RingedFiniteFreeBasisCoordinates.{c, v, r, w} J φ d e E h T ε.hom X (a.app X) := by
  intro F hF q i
  refine ⟨biproduct.ι (fun _ : Fin d ↦ F) i ≫ b.hom.app F, hb F i, ?_⟩
  simpa only [Iso.app_hom] using
    RingedFiniteFreeCoordinatesProof.basis_transport DerivedCategory.Q DerivedCategory.Q
      (E.mapHomologicalComplex (.up ℤ))
      ((SheafOfModules.scalarRestriction φ).mapHomologicalComplex (.up ℤ))
      T (SheafOfModules.scalarDerivedRestriction φ) ε
      (SheafOfModules.scalarRestrictionComparison φ) d a b hl X F q i

namespace FiniteFreeScalarProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open SheafOfModules

private def basisSection (d : ℕ)
    (e : (scalarRestriction φ).obj (unit (derivedChangeRingIndependentCoefficients J S)) ≅
      free (R := derivedChangeRingIndependentCoefficients J R) (ULift.{max c v r} (Fin d)))
    (i : Fin d) : sections.{c, v, r} J S := by
  let f := ιFree (ULift.up i) ≫ e.inv
  refine ⟨fun V ↦ f.val.app V (1 : R.obj.obj V), ?_⟩
  intro V W k
  have hn := congrArg (fun g ↦ g (1 : R.obj.obj V))
    (f.val.naturality k)
  change f.val.app W (R.obj.map k 1) = S.obj.map k (f.val.app V (show R.obj.obj V from 1)) at hn
  change S.obj.map k (f.val.app V (show R.obj.obj V from 1)) =
    f.val.app W (show R.obj.obj W from 1)
  have hr : R.obj.map k (1 : R.obj.obj V) = 1 := (R.obj.map k).hom.map_one
  exact hn.symm.trans (congrArg (f.val.app W) hr)

private theorem scalarSection_smul
    (E : scalarModules J R ⥤ scalarModules J S)
    (h : ∀ M, E.obj M = changeOfRings φ M)
    (M : scalarModules J R) (V : Cᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V) :
    ringedFiniteFreeScalarSection.{c, v, r} J φ E h M V s x =
      s • ringedFiniteFreeScalarSection.{c, v, r} J φ E h M V 1 x := by
  dsimp only [ringedFiniteFreeScalarSection]
  rw [← ((eqToHom (h M).symm).val.app V).hom.map_smul]
  rw [← (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
      (changeOfRingsPresheaf φ M)).app V).hom.map_smul]
  congr 2
  exact ((ModuleCat.ExtendScalars.smul_tmul (φ.hom.app V).hom s 1 x).trans
    (by rw [mul_one])).symm

end FiniteFreeScalarProof

attribute [-instance] sectionLinearIndependent derivedSectionLinear sectionQLinear

attribute [local irreducible] FiniteFreeLocalizationProof.adjunction
  derivedInternalHomOfUniverses WeilConjectures.CoefficientClosedStructure.tensor
  WeilConjectures.coefficientTotalTensor
  SheafOfModules.scalarDerivedRestriction SheafOfModules.scalarRestrictionComparison
  SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom
  SheafOfModules.monoidalCategory SheafOfModules.tensorObjIsoSheafification
  WeilConjectures.CoefficientTensorModels.iso
  RingedFiniteFreeCoordinatesProof.derivedAdjunction
  RingedFiniteFreeCoordinatesProof.scalarModel RingedFiniteFreeCoordinatesProof.modelIso
  RingedFiniteFreeCoordinatesProof.chainBasisE
  RingedFiniteFreeCoordinatesProof.moduleBasisIso
  RingedFiniteFreeCoordinatesProof.localizedBasis
  RingedFiniteFreeCoordinatesProof.restrictionFactors
  ringedFiniteFreeScalarSection WeilConjectures.coefficientTensorGenerator
  RingedFiniteFreeBasisCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Basis coordinates of the restricted evaluation comparison.
The basis identifications are fixed on every K-flat representative by their actual
basis sections. The ordinary scalar adjunction is fixed by its unit sections, its
derived adjunction by its chain transposes, and β by restricted evaluation. Only
the resulting equation on basis inclusions remains to be calculated. Product preservation,
the matrix calculation, naturality, conservativity and assembly of the internal-Hom
isomorphism are proved outside.
Source: Stacks Project, sites-cohomology.tex, Tags 08J9 and 08JA, finite-free
specialization of lemma-internal-hom and lemma-section-RHom-over-U.
(blueprint: lem-sf-ringed-finite-free-hom-coordinates).

Proof: use the displayed basis of S over R. On K-flat representatives the maps
(x_j) ↦ sum e_j tensor x_j and the basis coefficient maps are inverse chain maps.
Finite sums preserve quasi-isomorphisms, giving a_X : X^d ≅ U(TX).
The normalized scalar-Hom adjunction identifies U H_S(TP,TQ) with H_R(P,UTQ),
giving β. Transport its ordinary and derived adjunctions to E and T using their
actual object and map formulas and the unique universal counit comparison. Their
unit and chain-transpose equations fix the transported adjunctions. The displayed
transpose equation for β expands scalarHomRestrictedEvaluation: insert eta_P,
apply the counit mate of μ, and restrict S-evaluation. Transpose bijectivity fixes β.
Use a_H and a_Q for the two displayed basis isomorphisms. Transpose
β after the restricted comparison and the i-th basis inclusion. The normalized
scalar unit inserts 1, while the κ formula and μ square multiply it by e_i.
Its transpose is evaluation followed by the i-th basis inclusion on Q.
Uniqueness of transpose gives precisely H_R(P,ι_i followed by a_Q), the equation
asserted here. These identities can be checked on actual K-flat representatives
and localized. Rank zero has no inclusions; no boundedness is used.
No preservation of products or invertibility of the comparison is asserted here. -/
theorem ringedFiniteFreeHomBaseChange_coordinates
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (d : ℕ) (e :
      (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map φ)).obj
          (SheafOfModules.unit
            (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        SheafOfModules.free (R :=
          SheafOfModules.derivedChangeRingIndependentCoefficients J R)
            (ULift.{max c v r} (Fin d)))
    (E : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) ⥤ SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
      (h : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
      (_hm : ∀ {M N : SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)} (f : M ⟶ N),
        E.map f = eqToHom (h M) ≫ SheafOfModules.changeOfRingsHom φ M f ≫
          eqToHom (h N).symm)
      [_hE : E.Additive]
      (T : DerivedCategory (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ⥤
        DerivedCategory (SheafOfModules.{max c v r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J S)))
      (ε : DerivedCategory.Q ⋙ T ⟶
        E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (_hT : T.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) (ComplexShape.up ℤ)))
      (AR : WeilConjectures.CoefficientClosedStructure
        (derivedInternalHomOfUniverses.{c, v, r, w} J R))
      (AS : WeilConjectures.CoefficientClosedStructure
        (derivedInternalHomOfUniverses.{c, v, r, w} J S))
      (MR : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R AR)
      (MS : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J S AS)
      (κ : WeilConjectures.coefficientTotalTensor.{r, c, v} J R ⋙
          E.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (E.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            WeilConjectures.coefficientTotalTensor.{r, c, v} J S)
      (μ : AR.tensor ⋙ T ≅ T.prod T ⋙ AS.tensor)
    (hκ : (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h
            (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
            U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
              P Q p q (p + q) rfl U x y)) =
        WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h (P.X p) U 1 x)
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E h (Q.X q) U 1 y)))
    (hcomp : (∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
        ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hEQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          IsIso (ε.app P) ∧ IsIso (ε.app Q) ∧
          T.map ((MR.iso J R AR P Q hP hQ).hom) ≫
              μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              AS.tensor.map (Prod.mkHom (ε.app P) (ε.app Q)) =
            ε.app ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
              DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
              (MS.iso J S AS _ _ hEP hEQ).hom)) :
    ∃ (adj : E ⊣ SheafOfModules.scalarRestriction φ)
      (δ : T ⊣ SheafOfModules.scalarDerivedRestriction φ),
      (∀ (M : SheafOfModules.scalarModules J R) (V : Cᵒᵖ) (x : M.val.obj V),
        (adj.unit.app M).val.app V x = ringedFiniteFreeScalarSection.{c, v, r} J φ E h M V 1 x) ∧
      (∀ (F : CochainComplex (SheafOfModules.scalarModules J R) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) F →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (F.X n)) →
        ∀ (N : CochainComplex (SheafOfModules.scalarModules J S) ℤ)
          (g : F ⟶ ((SheafOfModules.scalarRestriction φ).mapHomologicalComplex
            (.up ℤ)).obj N),
        (δ.homEquiv (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj N)).symm
            (DerivedCategory.Q.map g ≫
              (SheafOfModules.scalarRestrictionComparison φ).inv.app N) =
          ε.app F ≫ DerivedCategory.Q.map
            (SheafOfModules.scalarChainTranspose.{c, v, max c v r} φ E _hE adj F N g)) ∧
    ∀ P Q : DerivedCategory (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)),
    ∃ (a : (⨁ fun _ : Fin d ↦
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) ≅
      (SheafOfModules.scalarDerivedRestriction φ).obj
        (T.obj ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q))))
      (aQ : (⨁ fun _ : Fin d ↦ Q) ≅
        (SheafOfModules.scalarDerivedRestriction φ).obj (T.obj Q))
      (β : (SheafOfModules.scalarDerivedRestriction φ).obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J S).obj (op (T.obj P), T.obj Q)) ≅
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
          (op P, (SheafOfModules.scalarDerivedRestriction φ).obj (T.obj Q))),
      RingedFiniteFreeBasisCoordinates.{c, v, r, w} J φ d e E h T ε
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) a ∧
      RingedFiniteFreeBasisCoordinates.{c, v, r, w} J φ d e E h T ε Q aQ ∧
      (AR.transpose _ P ((SheafOfModules.scalarDerivedRestriction φ).obj (T.obj Q))).symm
          β.hom =
        AR.tensor.map (Prod.mkHom (𝟙 _) (δ.unit.app P)) ≫
          δ.unit.app _ ≫
          (SheafOfModules.scalarDerivedRestriction φ).map
            (μ.hom.app _ ≫ AS.tensor.map
              (Prod.mkHom (δ.counit.app _) (δ.counit.app _))) ≫
          (SheafOfModules.scalarDerivedRestriction φ).map
            (AS.evaluation (T.obj P) (T.obj Q)) ∧
      ∀ i : Fin d,
        biproduct.ι _ i ≫ a.hom ≫
          (SheafOfModules.scalarDerivedRestriction φ).map
            (AS.transpose _ (T.obj P) (T.obj Q)
              (μ.inv.app
                ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q), P) ≫
                T.map (AR.evaluation P Q))) ≫ β.hom =
          (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
            (Prod.mkHom (𝟙 (op P)) (biproduct.ι _ i ≫ aQ.hom)) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  all_goals
    classical
    have hκ_used := hκ
    have hcomp_used := hcomp
    clear hκ_used hcomp_used hκ hcomp κ MR
    have ha := @RingedFiniteFreeCoordinatesProof.normalizedOrdinaryAdjunction.{c, v, max c v r}
      C inferInstance J inferInstance inferInstance inferInstance R S φ E h _hm _hE
    let adj := ha.choose
    have hu := ha.choose_spec
    -- Compare the specified extension with its concrete scalar model.
    let m := @RingedFiniteFreeCoordinatesProof.scalarModel.{c, v, max c v r, w}
      C inferInstance inferInstance J inferInstance inferInstance inferInstance R S
      inferInstance inferInstance φ
    have : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso _ (.up ℤ)) := _hT
    let eE : E ≅ m.E :=
      @RingedFiniteFreeCoordinatesProof.modelIso.{c, v, max c v r, w}
        C inferInstance inferInstance J inferInstance inferInstance inferInstance R S
        inferInstance inferInstance φ m E h _hm
    -- Finite freeness makes the derived counit invertible on every complex.
    have : PreservesFiniteLimits m.E :=
      RingedFiniteFreeCoordinatesProof.model_finite_limits φ d e m
    have : PreservesFiniteLimits E := preservesFiniteLimits_of_natIso (F := m.E) (G := E) eE.symm
    have : PreservesColimits E := adj.leftAdjoint_preservesColimits
    have : IsIso ε := Functor.isIso_of_isLeftDerivedFunctor_of_inverts T ε
      (E.mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso (.up ℤ))
    -- Localize the normalized ordinary adjunction.
    let δ : T ⊣ SheafOfModules.scalarDerivedRestriction φ :=
      @RingedFiniteFreeCoordinatesProof.derivedAdjunction.{c, v, max c v r, w}
      C inferInstance inferInstance J inferInstance inferInstance inferInstance R S
      inferInstance inferInstance φ E _hE T (asIso ε) adj
    -- Retain both normalization formulas.
    refine ⟨adj, δ, ?_, ?_, ?_⟩
    · intro M V x
      simpa only [ringedFiniteFreeScalarSection, adj] using hu M V x
    · intro F hF hflat N g
      exact @RingedFiniteFreeCoordinatesProof.derivedAdjunction_transpose.{c, v, max c v r, w}
        C inferInstance inferInstance J inferInstance inferInstance inferInstance R S
        inferInstance inferInstance φ E _hE T (asIso ε) adj F N g
    · let b : RingedFiniteFreeCoordinatesProof.copies d ≅
          E.mapHomologicalComplex (.up ℤ) ⋙
            (SheafOfModules.scalarRestriction φ).mapHomologicalComplex (.up ℤ) :=
        RingedFiniteFreeCoordinatesProof.chainBasisE φ d e m E eE
      let χ : DerivedCategory.Q ⋙ (T ⋙ SheafOfModules.scalarDerivedRestriction φ) ≅
          (E.mapHomologicalComplex (.up ℤ) ⋙
            (SheafOfModules.scalarRestriction φ).mapHomologicalComplex (.up ℤ)) ⋙
              DerivedCategory.Q :=
        RingedFiniteFreeCoordinatesProof.restrictionFactors φ E T (asIso ε)
      let a : RingedFiniteFreeCoordinatesProof.copies d ≅
          T ⋙ SheafOfModules.scalarDerivedRestriction φ :=
        RingedFiniteFreeCoordinatesProof.localizedBasis DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (.up ℤ)) d _ _ b χ
      -- Record the component formulas before hiding the basis constructions.
      set_option backward.isDefEq.respectTransparency false in
      set_option backward.isDefEq.respectTransparency.types false in
      have hb (F : CochainComplex (SheafOfModules.scalarModules J R) ℤ)
          (i : Fin d) (n : ℤ) (V : Cᵒᵖ) (x : (F.X n).val.obj V) :
          ((biproduct.ι _ i ≫ b.hom.app F).f n).val.app V x =
            ringedFiniteFreeScalarSection.{c, v, r} J φ E h (F.X n) V
              ((SheafOfModules.ιFree (ULift.up i) ≫ e.inv).val.app V
                (1 : R.obj.obj V)) x := by
        simpa only [b, eE, ringedFiniteFreeScalarSection] using
          @RingedFiniteFreeCoordinatesProof.chainBasisModel_ι_apply.{c, v, max c v r, w}
            C inferInstance inferInstance J inferInstance inferInstance inferInstance R S
            inferInstance inferInstance φ d e m E _hE h _hm F i n V x
      -- The localized basis commutes with the universal counit.
      have hlocal (F : CochainComplex (SheafOfModules.scalarModules J R) ℤ)
          (i : Fin d) :
          biproduct.ι _ i ≫ a.hom.app (DerivedCategory.Q.obj F) ≫
            (SheafOfModules.scalarDerivedRestriction φ).map (ε.app F) =
          DerivedCategory.Q.map (biproduct.ι _ i ≫ b.hom.app F) ≫
            (SheafOfModules.scalarRestrictionComparison φ).inv.app
              ((E.mapHomologicalComplex (.up ℤ)).obj F) := by
        simpa only [a, χ, asIso_hom] using
          @RingedFiniteFreeCoordinatesProof.localizedBasis_restriction.{c, v, max c v r, w}
            C inferInstance inferInstance J inferInstance inferInstance inferInstance R S
            inferInstance inferInstance φ E _hE T (asIso ε) d b F i
      clear_value a b
      -- Naturality transports the formula along every representative isomorphism.
      have hcoord (X : DerivedCategory (SheafOfModules.scalarModules J R)) :
          RingedFiniteFreeBasisCoordinates.{c, v, r, w} J φ d e E h T ε X (a.app X) :=
        by
          simpa only [asIso_hom] using
            basisCoordinates_of_components.{c, v, r, w} J φ d e E h T
              (asIso ε) a b hb hlocal X
      -- Global sections act centrally on the target derived category.
      let := sectionLinearIndependent S
      let := derivedSectionLinear S
      let := sectionQLinear S
      have hunit (i : Fin d) (X : DerivedCategory (SheafOfModules.scalarModules J R)) :
          biproduct.ι _ i ≫ a.hom.app X = δ.unit.app X ≫
            (SheafOfModules.scalarDerivedRestriction φ).map
              ((FiniteFreeScalarProof.basisSection.{c, v, r} J φ d e i) • 𝟙 (T.obj X)) := by
        refine RingedFiniteFreeCoordinatesProof.localizedBasis_unit
          (FiniteFreeScalarProof.sections.{c, v, r} J S) DerivedCategory.Q
          (HomologicalComplex.quasiIso _ (.up ℤ)) DerivedCategory.Q
          (E.mapHomologicalComplex (.up ℤ))
          ((SheafOfModules.scalarRestriction φ).mapHomologicalComplex (.up ℤ))
          T (SheafOfModules.scalarDerivedRestriction φ)
          (adj.mapHomologicalComplex (.up ℤ)) δ (asIso ε)
          (SheafOfModules.scalarRestrictionComparison φ) d a b hlocal ?_
          i (FiniteFreeScalarProof.basisSection.{c, v, r} J φ d e i) ?_ X
        · intro F
          dsimp only [δ]
          exact RingedFiniteFreeCoordinatesProof.derivedAdjunction_unit φ E T (asIso ε) adj F
        · intro F
          set_option backward.isDefEq.respectTransparency false in
          set_option backward.isDefEq.respectTransparency.types false in
          all_goals
            apply HomologicalComplex.hom_ext
            intro n
            apply SheafOfModules.hom_ext
            ext V x
            rw [hb]
            change _ = (FiniteFreeScalarProof.basisSection.{c, v, r} J φ d e i).val V •
              (show (E.obj (F.X n)).val.obj V from (adj.unit.app (F.X n)).val.app V x)
            rw [FiniteFreeScalarProof.scalarSection_smul]
            congr 1
            simpa only [ringedFiniteFreeScalarSection, adj] using (hu (F.X n) V x).symm
      -- Evaluate the closed comparison on the normalized basis inclusions.
      intro P Q
      refine ⟨a.app _, a.app Q, (ClosedScalarHom.iso AR AS δ μ).app (op P, T.obj Q),
        hcoord _, hcoord Q, ?_, ?_⟩
      · simpa only [Functor.comp_obj, Functor.prod_obj, Functor.op_obj, Functor.id_obj,
          WeilConjectures.CoefficientClosedStructure.tensor, MonoidalCategory.tensor_obj] using
          FiniteFreeClosedProof.evaluation_formula AR AS δ μ P (T.obj Q)
      · intro i
        change biproduct.ι _ i ≫ a.hom.app _ ≫ _ ≫
          (ClosedScalarHom.iso AR AS δ μ).hom.app (op P, T.obj Q) =
            (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
              (Prod.mkHom (𝟙 (op P)) (biproduct.ι _ i ≫ a.hom.app Q))
        simpa only [Category.assoc] using
          FiniteFreeClosedProof.coordinate_of_units AR AS δ μ
            (FiniteFreeScalarProof.sections.{c, v, r} J S) P Q
            (FiniteFreeScalarProof.basisSection.{c, v, r} J φ d e i)
            (biproduct.ι (fun _ : Fin d ↦
              (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, Q)) i ≫
                a.hom.app _) (biproduct.ι (fun _ : Fin d ↦ Q) i ≫ a.hom.app Q)
            (hunit i _) (hunit i Q)
            (fun X Y ↦ FiniteFreeScalarProof.derivedTensor_smul.{c, v, r, w} J S AS MS X Y _)

end Site
end CategoryTheory
