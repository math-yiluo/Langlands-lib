/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLinePullbackFiniteLimits
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineAlgebraicPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # Tensor comparison for coefficient-identified pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option Elab.async false
-- Reuse tagged equalities for the tensor-to-site comparison instances.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  CategoryTheory.Preadditive.preadditiveHasZeroMorphisms
  CategoryTheory.Functor.preservesZeroMorphisms_of_additive
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace SheafOfModules.SignedLineDerivedBaseChange
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal

section Tensor
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  (A : Sheaf J CommRingCat.{max u v w})

private theorem site_tensor_map_pure {M M' N : KFlatFixedTensor.Modules A}
    (f : M ⟶ M') (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    ((siteSheafTensorRight N).map f).val.app V (siteSheafTensorTmul M N V x y) =
      siteSheafTensorTmul M' N V (f.val.app V x) y := by
  exact (congrArg (fun q ↦ q.app V (x ⊗ₜ[A.obj.obj V] y))
    ((PresheafOfModules.sheafificationAdjunction (R :=
      (sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (𝟙 _)).unit.naturality
      (siteTensorHom f.val N.val))).symm

private theorem pure_def (M N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
    (x : M.val.obj V) (y : N.val.obj V) :
    CochainScalarConstruction.pure.{max u v w, u, v} A M N V x y =
      (tensorObjIsoSheafification M N).inv.val.app V
        (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
          (M.val ⊗ N.val)).app V (x ⊗ₜ[A.obj.obj V] y)) := rfl

private theorem pure_eq (M N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
    (x : M.val.obj V) (y : N.val.obj V) :
    ScalarHomOrdinary.pure.{u, v, max u v w} A M N V x y =
      CochainScalarConstruction.pure.{max u v w, u, v} A M N V x y := rfl

private theorem pure_sheaf_apply (M N : KFlatFixedTensor.Modules A) (V : Cᵒᵖ)
    (p : ((CochainScalarConstruction.underlying A).obj M ⊗
      (CochainScalarConstruction.underlying A).obj N).obj.obj V) :
    (CochainInversePairing.pureSheaf A M N).hom.app V p =
      CochainScalarConstruction.pure A M N V p.1 p.2 := rfl

end Tensor
attribute [local irreducible] CochainScalarConstruction.pure ScalarHomOrdinary.pure
  siteSheafTensorRight siteSheafTensorTmul
  Functor.leftAdjoint Functor.rightAdjoint

section Abstract
universe ua va ub vb
variable {AA : Type ua} {BB : Type ub} [Category.{va} AA] [Category.{vb} BB]
  [MonoidalCategory AA] [MonoidalCategory BB]
private def transport_component (F : AA ⥤ BB) (M L : AA) (N : BB) (X : AA) (Y : BB)
    (jR : M ⊗ L ≅ X) (jS : F.obj M ⊗ N ≅ Y)
    (k : F.obj (M ⊗ L) ≅ F.obj M ⊗ F.obj L) (t : F.obj L ≅ N) : F.obj X ≅ Y :=
  F.mapIso jR.symm ≪≫ k ≪≫ tensorIso (Iso.refl _) t ≪≫ jS
private theorem transport_component_hom (F : AA ⥤ BB) (M L : AA) (N : BB)
    (X : AA) (Y : BB) (jR : M ⊗ L ≅ X) (jS : F.obj M ⊗ N ≅ Y)
    (k : F.obj (M ⊗ L) ≅ F.obj M ⊗ F.obj L) (t : F.obj L ≅ N) :
    (transport_component F M L N X Y jR jS k t).hom =
      F.map jR.inv ≫ k.hom ≫ (𝟙 (F.obj M) ⊗ₘ t.hom) ≫ jS.hom := rfl
attribute [local irreducible] transport_component
end Abstract

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}

private theorem presentation_unit_section
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    (em : pull a ⋙ toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat) ≅
      (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat)) ⋙
        sheafPullback U (Type (max u v w)) J K)
    (hem : ∀ (M : KFlatFixedTensor.Modules R) (V : Cᵒᵖ) (x : M.val.obj V),
      (em.hom.app M).hom.app (U.op.obj V)
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          M V.unop x) =
        ((sheafAdjunctionContinuous U (Type (max u v w)) J K).unit.app
          ((toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat)).obj M)).hom.app V x)
    (M : KFlatFixedTensor.Modules R)
      (Z : Sheaf J (Type (max u v w)))
      (f : Z ⟶ (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat)).obj M)
      (V : Cᵒᵖ) (s : Z.obj.obj V) :
      ((sheafPullback U (Type (max u v w)) J K).map f ≫
        em.inv.app M).hom.app (U.op.obj V)
          (((sheafAdjunctionContinuous U (Type (max u v w)) J K).unit.app Z).hom.app V s) =
        ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          M V.unop (f.hom.app V s) := by
  have hn := congrArg (fun q ↦ q.hom.app V s)
    ((sheafAdjunctionContinuous U (Type (max u v w)) J K).unit.naturality f)
  change ((sheafAdjunctionContinuous U (Type (max u v w)) J K).unit.app
    ((toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat)).obj M)).hom.app V
      (f.hom.app V s) =
    ((sheafPullback U (Type (max u v w)) J K).map f).hom.app (U.op.obj V)
      (((sheafAdjunctionContinuous U (Type (max u v w)) J K).unit.app Z).hom.app V s) at hn
  apply Eq.trans (congrArg ((em.inv.app M).hom.app (U.op.obj V)) hn.symm)
  apply Eq.trans (congrArg ((em.inv.app M).hom.app (U.op.obj V))
    (hem M V (f.hom.app V s)).symm)
  exact congrArg (fun q ↦ q.hom.app (U.op.obj V)
    (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
      M V.unop (f.hom.app V s))) (em.app M).hom_inv_id

private theorem pull_section_map
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    {M M' : KFlatFixedTensor.Modules R} (f : M ⟶ M') (V : C)
    (x : M.val.obj (op V)) :
    ((pull a).map f).val.app (op (U.obj V))
      (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a) M V x) =
    ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a) M' V
      (f.val.app (op V) x) := by
  let := module_pushforward_isRightAdjoint_of_universes a
  exact (congrArg (fun g ↦ g.val.app (op V) x)
    ((pullbackPushforwardAdjunction a).unit.naturality f)).symm

-- The generalized pairing formula includes three underlying-sheaf comparisons.
private theorem inverse_tensor_source_unit
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    [HasSheafify J AddCommGrpCat.{max u v w}]
    [HasSheafify K AddCommGrpCat.{max u v w}]
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    (em : pull a ⋙ toSheaf _ ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat) ≅
      (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat)) ⋙
        sheafPullback U (Type (max u v w)) J K)
    (hem : ∀ (M : KFlatFixedTensor.Modules R) (V : Cᵒᵖ) (x : M.val.obj V),
      (em.hom.app M).hom.app (U.op.obj V)
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          M V.unop x) =
        ((sheafAdjunctionContinuous U (Type (max u v w)) J K).unit.app
          ((toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat)).obj M)).hom.app V x)
    (I : AlgebraicInverseImage (sheafPullback U (Type (max u v w)) J K) R S)
    (hI : I.modules = pull a) (hMI : HEq I.moduleUnderlying em) :
    ∃ k : ∀ M N : KFlatFixedTensor.Modules R,
      (pull a).obj ((monoidalCategory R).tensorObj M N) ≅
        (monoidalCategory S).tensorObj ((pull a).obj M) ((pull a).obj N),
      (∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
        (pull a).map ((monoidalCategory R).tensorHom f g) ≫ (k M' N').hom =
          (k M N).hom ≫ (monoidalCategory S).tensorHom ((pull a).map f) ((pull a).map g)) ∧
      ∀ (M L' : KFlatFixedTensor.Modules R) (V : C)
      (x : M.val.obj (op V)) (y : L'.val.obj (op V)),
      (k M L').hom.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          ((monoidalCategory R).tensorObj M L') V
            (CochainScalarConstruction.pure.{max u v w, u, v} R M L' (op V) x y)) =
        CochainScalarConstruction.pure.{max u v w, u, v} S ((pull a).obj M) ((pull a).obj L')
          (op (U.obj V))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a) M V x)
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            L' V y) := by
  let := module_pushforward_isRightAdjoint_of_universes a
  obtain ⟨ri, ra, rm, rz, rone, F, mi, ma, mz, ms⟩ := I
  dsimp only at hI hMI
  subst F
  have hmi : mi = em := eq_of_heq hMI
  subst mi
  let I : AlgebraicInverseImage (sheafPullback U (Type (max u v w)) J K) R S :=
    ⟨ri, ra, rm, rz, rone, pull a, em, ma, mz, ms⟩
  let : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  have : AB5OfSize.{v, max u v} (Type (max u v w)) :=
    AB5OfSize_shrink.{v, max u v, max u v w, max u v w} _
  obtain ⟨k, hk, hp⟩ := CochainInversePairing.exists_inverseImageTensorComparison R S
    (sheafPullback U (Type (max u v w)) J K) I
    (U.sheafPushforwardContinuous (Type (max u v w)) J K)
    (sheafAdjunctionContinuous U (Type (max u v w)) J K)
  refine ⟨k, hk, ?_⟩
  intro M L' V x y
  let Z := (CochainScalarConstruction.underlying R).obj M ⊗
    (CochainScalarConstruction.underlying R).obj L'
  let fst := CartesianMonoidalCategory.fst
    ((CochainScalarConstruction.underlying R).obj M)
    ((CochainScalarConstruction.underlying R).obj L')
  let snd := CartesianMonoidalCategory.snd
    ((CochainScalarConstruction.underlying R).obj M)
    ((CochainScalarConstruction.underlying R).obj L')
  let z := CochainInversePairing.pureSheaf R M L'
  have h := hp M L' Z fst snd z (fun W p ↦ by
      change (CochainInversePairing.pureSheaf R M L').hom.app W p = _
      rw [pure_sheaf_apply]
      unfold CochainScalarConstruction.pure
      rfl) (op (U.obj V))
    (((sheafAdjunctionContinuous U (Type (max u v w)) J K).unit.app Z).hom.app
      (op V) (x, y))
  rw [← pure_def] at h
  change (k M L').hom.val.app (op (U.obj V))
    (((sheafPullback U (Type (max u v w)) J K).map z ≫
      em.inv.app ((monoidalCategory R).tensorObj M L')).hom.app (op (U.obj V)) _) =
    CochainScalarConstruction.pure.{max u v w, u, v} S ((pull a).obj M) ((pull a).obj L') (op
      (U.obj V))
      ((((sheafPullback U (Type (max u v w)) J K).map fst ≫ em.inv.app M).hom.app
        (op (U.obj V))) _)
      ((((sheafPullback U (Type (max u v w)) J K).map snd ≫ em.inv.app L').hom.app
        (op (U.obj V))) _) at h
  have hz := presentation_unit_section.{u, v, w} a em hem ((monoidalCategory R).tensorObj M L')
    Z z (op V) (x, y)
  have hx := presentation_unit_section.{u, v, w} a em hem M Z fst (op V) (x, y)
  have hy := presentation_unit_section.{u, v, w} a em hem L' Z snd (op V) (x, y)
  exact (congrArg ((k M L').hom.val.app (op (U.obj V))) hz.symm).trans
    (h.trans (congrArg₂ (CochainScalarConstruction.pure.{max u v w, u, v} S _ _ (op (U.obj V)))
      hx hy))

-- The proof compares the algebraic and explicit site tensors through their unit sections.
/-- Coefficient-identified pullback preserves tensor, with the source-unit normalization.
Source: Stacks Project, Modules on Sites, Tag 03EL.
(blueprint: lem-pur-signed-line-pullback-tensor)
Proof: construct the algebraic inverse-image lift from its ring and module unit
presentations. Apply the existing inverse-image tensor comparison. Its generalized
pairing formula, evaluated on the unit of the product of the two underlying sheaves,
is the formula on pulled-back pure tensors. Naturality of the module unit identifies
the three factors. The sheafified tensor comparison transports this result to the
explicit site tensor; its naturality is tested on pure tensors. Finally tensor with
the given isomorphism of the second factors. -/
theorem identified_ring_pullback_tensor
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
      (U.sheafPushforwardContinuous RingCat J K).obj
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    (hcover : CoverPreserving J K U)
    (rInv : Sheaf J RingCat.{max u v w} ⥤ Sheaf K RingCat.{max u v w})
    (rAdj : rInv ⊣ U.sheafPushforwardContinuous RingCat J K)
    (ha : IsIso ((rAdj.homEquiv _ _).symm a))
    (L : KFlatFixedTensor.Modules R) (N : KFlatFixedTensor.Modules S)
    (t : (pull a).obj L ≅ N) :
    ∃ γ : siteSheafTensorRight L ⋙ pull a ≅ pull a ⋙ siteSheafTensorRight N,
      ∀ (M : KFlatFixedTensor.Modules R) (V : C) (x : M.val.obj (op V))
        (y : L.val.obj (op V)),
        (γ.hom.app M).val.app (op (U.obj V))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            ((siteSheafTensorRight L).obj M) V (siteSheafTensorTmul M L (op V) x y)) =
          siteSheafTensorTmul ((pull a).obj M) N (op (U.obj V))
            (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
              M V x)
            (t.hom.val.app (op (U.obj V))
              (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
                L V y)) := by
  let := module_pushforward_isRightAdjoint_of_universes a
  obtain ⟨hJ, _⟩ := coefficientSheafification.{u, v, max u v w} J
  obtain ⟨hK, _⟩ := coefficientSheafification.{u, v, max u v w} K
  let := hJ
  let := hK
  obtain ⟨pr, hr, e, he, em, hem⟩ := identified_ring_pullback_presentations a hcover rInv rAdj ha
  obtain ⟨I, hI, hRI, hMI⟩ := algebraic_pullback_of_presentations a pr hr em hem
  obtain ⟨k, hk, hkpure⟩ := inverse_tensor_source_unit.{u, v, w} a em hem I hI hMI
  let jR (M : KFlatFixedTensor.Modules R) :=
    ScalarHomOrdinary.tensorIsoSite.{u, v, max u v w} R M L
  let jS (M : KFlatFixedTensor.Modules S) :=
    ScalarHomOrdinary.tensorIsoSite.{u, v, max u v w} S M N
  let δ (M : KFlatFixedTensor.Modules R) :
      (pull a).obj ((siteSheafTensorRight L).obj M) ≅
        (siteSheafTensorRight N).obj ((pull a).obj M) :=
    @transport_component _ _ _ _ (monoidalCategory R) (monoidalCategory S)
      (pull a) M L N _ _ (jR M) (jS ((pull a).obj M)) (k M L) t
  have hδ (M : KFlatFixedTensor.Modules R) (V : C)
      (x : M.val.obj (op V)) (y : L.val.obj (op V)) :
      (δ M).hom.val.app (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
          ((siteSheafTensorRight L).obj M) V (siteSheafTensorTmul M L (op V) x y)) =
      siteSheafTensorTmul ((pull a).obj M) N (op (U.obj V))
        (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a) M V x)
        (t.hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            L V y)) := by
    rw [transport_component_hom]
    change (jS ((pull a).obj M)).hom.val.app (op (U.obj V))
      (((monoidalCategory S).tensorHom (𝟙 _) t.hom).val.app (op (U.obj V))
        ((k M L).hom.val.app (op (U.obj V))
          (((pull a).map (jR M).inv).val.app (op (U.obj V)) _))) = _
    rw [pull_section_map]
    change (jS ((pull a).obj M)).hom.val.app (op (U.obj V))
      (((monoidalCategory S).tensorHom (𝟙 _) t.hom).val.app (op (U.obj V))
        ((k M L).hom.val.app (op (U.obj V))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            ((monoidalCategory R).tensorObj M L) V
            ((ScalarHomOrdinary.tensorIsoSite.{u, v, max u v w} R M L).inv.val.app (op V)
              (siteSheafTensorTmul M L (op V) x y))))) = _
    rw [ScalarHomOrdinary.tensorIsoSite_inv_pure]
    rw [pure_eq]
    rw [hkpure, CochainScalarConstruction.pure_map]
    rw [← pure_eq]
    exact ScalarHomOrdinary.tensorIsoSite_pure.{u, v, max u v w} S _ _ _ _ _
  let γ : siteSheafTensorRight L ⋙ pull a ≅ pull a ⋙ siteSheafTensorRight N :=
    NatIso.ofComponents δ (by
      intro M M' f
      apply (pullbackPushforwardAdjunction a).homEquiv _ _ |>.injective
      apply scalarTensor_hom_ext
      intro V x y
      change (δ M').hom.val.app (op (U.obj V.unop))
        (((pull a).map ((siteSheafTensorRight L).map f)).val.app (op (U.obj V.unop))
          (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
            ((siteSheafTensorRight L).obj M) V.unop (siteSheafTensorTmul M L V x y))) =
        ((siteSheafTensorRight N).map ((pull a).map f)).val.app (op (U.obj V.unop))
          ((δ M).hom.val.app (op (U.obj V.unop))
            (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
              ((siteSheafTensorRight L).obj M) V.unop (siteSheafTensorTmul M L V x y)))
      rw [pull_section_map, site_tensor_map_pure, hδ, hδ, site_tensor_map_pure,
        pull_section_map])
  exact ⟨γ, hδ⟩

end SheafOfModules.SignedLineDerivedBaseChange
