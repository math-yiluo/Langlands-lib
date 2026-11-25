/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicImmersionResidueComparisonCore
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization
import WeilConjectures.CategoryTheory.ConstantInverseImageScalarNormalization
import all WeilConjectures.CategoryTheory.RingedPullbackPresentationOnSites

/-! # Ordinary immersion pullback in constant-scalar coordinates

Source: Stacks Tags 03A0, 03CY, 06YY, 099L and 099R.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private local instance residueOriginalSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _

private local instance residueModelContinuous {X S : Scheme.{u}} (i : S ⟶ X) :
    (proEtaleModelBaseChange i).IsContinuous
      (proEtaleModelTopology X) (proEtaleModelTopology S) :=
  proEtaleModelBaseChange_isContinuous i

attribute [local instance 60000] residueOriginalSmall residueModelContinuous

private local instance modelSheafify (S : Scheme.{u}) :
    HasSheafify (proEtaleModelTopology S) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u + 1, u + 1}

private local instance modelLocallyBijective (S : Scheme.{u}) :
    (proEtaleModelTopology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u + 1, u + 1}

private local instance fixedSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1}

attribute [local instance 50000] modelSheafify modelLocallyBijective fixedSheafify

private local instance standardDerived {C : Type*} [Category C] [Abelian C] :
    HasDerivedCategory C := HasDerivedCategory.standard _

private local instance fixedLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}

private noncomputable local instance modelAbelian (S : Scheme.{u})
    (R : Sheaf (proEtaleModelTopology S) CommRingCat.{u + 1}) :
    Abelian (ConstantCompletion.Mod R) :=
  SheafOfModules.instAbelian.{u + 1, u + 1, u + 1, u + 1} _

private noncomputable local instance fixedAbelian (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Abelian (proEtaleRingModules X R) :=
  SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _

attribute [local instance 40000] modelAbelian fixedAbelian standardDerived
  fixedLocallyBijective
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

private def residueDirectMap {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] :
    ConstantCompletion.constant (proEtaleModelTopology X) k ⟶
      ((proEtaleModelBaseChange i).sheafPushforwardContinuous CommRingCat.{u + 1}
        (proEtaleModelTopology X) (proEtaleModelTopology S)).obj
          (ConstantCompletion.constant (proEtaleModelTopology S) k) :=
  ((sheafificationAdjunction (proEtaleModelTopology X) CommRingCat.{u + 1}).homEquiv
    ((Functor.const (proEtaleSiteModel X)ᵒᵖ).obj (CommRingCat.of k))
    (((proEtaleModelBaseChange i).sheafPushforwardContinuous CommRingCat.{u + 1}
      (proEtaleModelTopology X) (proEtaleModelTopology S)).obj
        (ConstantCompletion.constant (proEtaleModelTopology S) k))).symm
    (Functor.whiskerLeft (proEtaleModelBaseChange i).op
      (toSheafify (proEtaleModelTopology S)
        ((Functor.const (proEtaleSiteModel S)ᵒᵖ).obj (CommRingCat.of k))))

private def residueModuleDirect {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] :
    ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology S) k) ⥤
      ConstantCompletion.Mod (ConstantCompletion.constant (proEtaleModelTopology X) k) :=
  SheafOfModules.pushforward (F := proEtaleModelBaseChange i)
    ((sheafCompose (proEtaleModelTopology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (residueDirectMap i k))

private def residueModuleAdjunction {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    (k : Type (u + 1)) [CommRing k] :
    ConstantCompletion.pull (sfbImmersionAlgebra i)
      (ConstantCompletion.constantMap (sfbImmersionAlgebra i) k) ⊣ residueModuleDirect i k := by
  let F := sfbImmersionAlgebra i
  let R := ConstantCompletion.constant (proEtaleModelTopology X) k
  let S' := ConstantCompletion.constant (proEtaleModelTopology S) k
  let c := ConstantCompletion.constantMap F k
  let a : SfbAdicRestriction.inverse i ⊣
      (proEtaleModelBaseChange i).sheafPushforwardContinuous (Type (u + 1))
        (proEtaleModelTopology X) (proEtaleModelTopology S) :=
    SfbAdicRestriction.adjunction i
  let g := SheafOfModules.RingedPresentationOnSites.siteContinuousRingedTopos
    (proEtaleModelBaseChange i) (SfbAdicRestriction.inverse i) a S' R (residueDirectMap i k)
  have hc : (sheafCompose (proEtaleModelTopology S)
      (CategoryTheory.forget CommRingCat.{u + 1})).map c =
      (F.algebra R).ringUnderlying.inv ≫ g.ringMap := by
    have h := ConstantCompletion.constantInverseImageScalarNormalization
      (proEtaleModelTopology X) (proEtaleModelTopology S) (proEtaleModelBaseChange i)
      (SfbAdicRestriction.inverse i) a F k
    change (F.algebra R).ringUnderlying.hom ≫ _ = g.ringMap at h
    rw [← h, Iso.inv_hom_id_assoc]
  let adj := Classical.choice
    (SheafOfModules.RingedPresentationOnSites.supplied_adjunction g
      (F.rings.obj R) (F.algebra R) c hc)
  let e : ConstantCompletion.change c ≅
      SheafOfModules.CoefficientOrdinaryProof.tensorFunctor.{u + 1, u + 1, u + 1} c :=
    NatIso.ofComponents (fun M ↦ eqToIso (by rfl)) (by
      intro M N f
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      simp only [Category.comp_id, Category.id_comp]
      rfl)
  exact adj.ofNatIsoLeft (Functor.isoWhiskerLeft (F.algebra R).modules e).symm

private theorem residueDirectMap_unit {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] :
    SheafOfModules.constantCoefficientUnit (proEtaleModelTopology X) k ≫
      ((sheafCompose (proEtaleModelTopology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (residueDirectMap i k)).hom =
      Functor.whiskerLeft (proEtaleModelBaseChange i).op
        (SheafOfModules.constantCoefficientUnit (proEtaleModelTopology S) k) := by
  have h := ((sheafificationAdjunction (proEtaleModelTopology X)
    CommRingCat.{u + 1}).homEquiv
      ((Functor.const (proEtaleSiteModel X)ᵒᵖ).obj (CommRingCat.of k))
      (((proEtaleModelBaseChange i).sheafPushforwardContinuous CommRingCat.{u + 1}
        (proEtaleModelTopology X) (proEtaleModelTopology S)).obj
          (ConstantCompletion.constant (proEtaleModelTopology S) k))).apply_symm_apply
    (Functor.whiskerLeft (proEtaleModelBaseChange i).op
      (toSheafify (proEtaleModelTopology S)
        ((Functor.const (proEtaleSiteModel S)ᵒᵖ).obj (CommRingCat.of k))))
  exact congrArg (fun f ↦ Functor.whiskerRight f
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) h

private def residueRealization (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :=
  CategoryTheory.coefficientModelFixedScalars (proEtaleModelTopology X) k ⋙
    (SfbAdicRestriction.modelEquivalence X (ModuleCat.{u + 1} k)).functor

private def residueDirectSquare {X S : Scheme.{u}} (i : S ⟶ X)
    (k : Type (u + 1)) [CommRing k] :
    residueModuleDirect i k ⋙ residueRealization X k ≅
      residueRealization S k ⋙ proEtaleSheafDirectImage i (ModuleCat.{u + 1} k) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun V ↦ ?_) ?_)) ?_
  · refine ModuleCat.isoMk (Iso.refl _) (fun a ↦ ?_)
    ext x
    have h := congrArg (fun f ↦ f.app (op (AsSmall.up.obj V.unop)) a)
      (residueDirectMap_unit i k)
    exact congrArg (fun b ↦ b • (show M.val.obj
      ((proEtaleModelBaseChange i).op.obj (op (AsSmall.up.obj V.unop))) from x)) h.symm
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext V x
    rfl

attribute [-instance] coefficientModelAdditiveSheafify coefficientEtaleModelAdditiveSheafify
  ConstantScalarRestriction.ringAbelian ConstantScalarRestriction.fixedAbelian
  ConstantScalarRestriction.ringGrothendieck ConstantScalarRestriction.fixedGrothendieck
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective in
/-- Constant-ring module pullback agrees with fixed-scalar inverse image before deriving.
Source: Stacks Tags 00YV, 03A0, 03CY and 03D2
(auxiliary; not a blueprint node).

Proof: transpose the whiskered constant-presheaf unit to construct the canonical
constant-ring direct-image map. The constantInverseImageScalarNormalization
equation identifies its transpose with the specified algebraic constantMap.
The supplied ringed-presentation adjunction therefore identifies ordinary tensor
pullback as left adjoint to this module direct image. After scalar restriction
and AsSmall evaluation, that direct image commutes with the original fixed-scalar
direct image: the section maps are identities, and linearity follows from the
sheafification Hom-equivalence equation that every constant a maps to a.
Compare scalar restriction with coefficientModelFixedScalars via restrictionIso.
Compose the two adjunctions with the model and scalar equivalences and conjugate
the right-adjoint square to obtain the required isomorphism of left adjoints.
All section identities and adjunctions apply also to the zero ring and empty sites. -/
theorem sfbImmersion_constantResidueSquare
    {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    (k : Type (u + 1)) [CommRing k] :
    Nonempty (((SfbAdicRestriction.modelEquivalence X (ModuleCat.{u + 1} k)).inverse ⋙
        (ConstantScalarRestriction.restriction
          (proEtaleModelTopology X) k).asEquivalence.inverse) ⋙
      ConstantCompletion.pull (sfbImmersionAlgebra i)
        (ConstantCompletion.constantMap (sfbImmersionAlgebra i) k) ≅
      SfbResidueComparisonCore.sfbFixedResiduePull i k) := by
  let E := (ConstantScalarRestriction.restriction
    (proEtaleModelTopology X) k).asEquivalence.trans
      (SfbAdicRestriction.modelEquivalence X (ModuleCat.{u + 1} k))
  let G := (ConstantScalarRestriction.restriction
    (proEtaleModelTopology S) k).asEquivalence.trans
      (SfbAdicRestriction.modelEquivalence S (ModuleCat.{u + 1} k))
  let rX : E.functor ≅ residueRealization X k :=
    Functor.isoWhiskerRight (CategoryTheory.restrictionIso (proEtaleModelTopology X) k) _
  let rS : G.functor ≅ residueRealization S k :=
    Functor.isoWhiskerRight (CategoryTheory.restrictionIso (proEtaleModelTopology S) k) _
  let r : residueModuleDirect i k ⋙ E.functor ≅
      G.functor ⋙ proEtaleSheafDirectImage i (ModuleCat.{u + 1} k) :=
    Functor.isoWhiskerLeft (residueModuleDirect i k) rX ≪≫ residueDirectSquare i k ≪≫
      Functor.isoWhiskerRight rS.symm (proEtaleSheafDirectImage i (ModuleCat.{u + 1} k))
  let a := E.symm.toAdjunction.comp (residueModuleAdjunction i k)
  let b := (proEtaleSheafAdjunction i (ModuleCat.{u + 1} k)).comp G.symm.toAdjunction
  exact ⟨((conjugateIsoEquiv a b).symm r).symm⟩

end AlgebraicGeometry.Scheme
