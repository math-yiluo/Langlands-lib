/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleAdjunction
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement

/-!
# Identity normalization of ordinary pro-etale derived pullback

The coprojection formula fixes the module comparison before scalar extension.
The tensor formulas fix its scalar-transport identification. The final equality
fixes the derived comparison on every cochain representative.

## References

* Stacks, Tags 09A5 and 03D2
* Stacks, Tags 09A5 and 00WX
* Stacks, Tag 03EK
* Stacks, Tag 05RU
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The inverse-image module with its action transported by the inverse of the specified
constant-ring comparison. -/
abbrev proEtaleIdentityTransportedInverseImage (X : Scheme.{u})
    (A : Type u) [CommRing A] :=
  proEtaleModuleInverseImage (𝟙 X) (proEtaleConstantRing X A) ⋙
    SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (proEtaleConstantRingComparison (𝟙 X) A).inv)

set_option backward.isDefEq.respectTransparency.types false in
/-- The distinguished identity coprojection, followed by restriction along
`U → U ×[X] X`. This is the inverse of the objectwise identity comparison before
extension of scalars. -/
def proEtaleIdentityModuleCoprojection (X : Scheme.{u}) (A : Type u) [CommRing A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEt)
    (m : M.val.obj (op U)) :
    ((proEtaleModuleInverseImage (𝟙 X) (proEtaleConstantRing X A)).obj M).val.obj
      (op U) :=
  ((proEtaleModuleInverseImage (𝟙 X) (proEtaleConstantRing X A)).obj M).val.map
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U).op
    (((SheafOfModules.pullbackPushforwardAdjunction.{u + 1}
      (proEtaleModelRingUnit (𝟙 X) (proEtaleConstantRing X A))).unit.app
        ((proEtaleModuleToModel ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (proEtaleConstantRing X A))).obj M)).val.app
              (AsSmall.up.op.obj (op U)) m)

/-- The sheafification-unit image of `m ⊗ a` in the specified tensor pullback.
The construction writes the scalar factor first. -/
def proEtaleIdentityPullbackTmul (X : Scheme.{u}) (A : Type u) [CommRing A]
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEtᵒᵖ)
    (m : ((proEtaleModuleInverseImage (𝟙 X) (proEtaleConstantRing X A)).obj M).val.obj U)
    (a : (proEtaleConstantRing X A).obj.obj U) :
    ((proEtaleConstantRingPullback.{u} A (𝟙 X)).obj M).val.obj U :=
  letI := WeilConjectures.integralCoefficientAbSheafify.{u, u} X
  letI := WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X
  letI := SheafOfModules.siteTensor_identity_locallyInjective
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
  letI := SheafOfModules.siteTensor_identity_locallySurjective
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
  (((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (J := ProEt.topology X)
    (R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
    (𝟙 _)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
        (J := ProEt.topology X) (proEtaleCoefficientInverseImageMap (𝟙 X) A)
        ((proEtaleModuleInverseImage (𝟙 X) (proEtaleConstantRing X A)).obj M))).app U)
    (a ⊗ₜ[((proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).obj
      (proEtaleConstantRing X A)).obj.obj U,
        ((proEtaleCoefficientInverseImageMap (𝟙 X) A).hom.app U).hom] m)

/-- The existing unbounded localization in the precise coefficient universes of the
pro-etale operations. Only existing sheafification instances are instantiated;
the functor is Mathlib's Q. -/
abbrev proEtaleIdentityLocalization (X : Scheme.{u}) (A : Type u) [CommRing A] :
    CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ ⥤
      proEtaleDerivedCategory X A :=
  letI := WeilConjectures.integralCoefficientAbSheafify.{u, u} X
  letI := WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X
  DerivedCategory.Q

set_option backward.isDefEq.respectTransparency false in
private def identityRingIso (X : Scheme.{u}) :
    proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1} ≅
      𝟭 (Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  (conjugateIsoEquiv Adjunction.id
    (proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1})).symm
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).symm

set_option backward.isDefEq.respectTransparency false in
private theorem identityRingIso_unit (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1}).unit.app F ≫
      (proEtaleSheafDirectImage (𝟙 X) CommRingCat.{u + 1}).map
        ((identityRingIso X).hom.app F) =
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).inv.app F := by
  exact (unit_conjugateEquiv_symm Adjunction.id
    (proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1})
    (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} X).inv F).symm

set_option backward.isDefEq.respectTransparency false in
private theorem identityRingIso_coefficient (X : Scheme.{u}) (A : Type u) [CommRing A] :
    (identityRingIso X).hom.app (proEtaleConstantRing X A) =
      proEtaleCoefficientInverseImageMap (𝟙 X) A := by
  apply (proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1}).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_unit, identityRingIso_unit]
  unfold proEtaleCoefficientInverseImageMap proEtaleConstantInverseImageMap
  rw [← Adjunction.homEquiv_symm_apply]
  dsimp only [Functor.id_obj]
  rw [Equiv.apply_symm_apply]
  apply ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
    ((proEtaleSheafDirectImage (𝟙 X) CommRingCat.{u + 1}).obj
      (proEtaleConstantRing X A))).injective
  rw [proEtaleConstantDirectImageMap, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  ext U
  simp only [AlgebraicGeometry.ProEtale.lowerStarId,
    Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, ObjectProperty.ι_obj,
    Functor.const_obj_obj, Functor.comp_obj, sheafificationAdjunction_unit_app,
    ObjectProperty.ι_map, NatTrans.comp_app, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply, Functor.whiskerLeft_app, Functor.op_obj]
  have h := (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).naturality
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app U.unop).op
  exact ConcreteCategory.congr_hom h.symm _

set_option backward.isDefEq.respectTransparency false in
private theorem identityRingIso_normalization (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : X.ProEt) :
    ((identityRingIso X).hom.app F).hom.app (op U) =
      ((proEtaleIsoInverseImageIdentification (𝟙 X) CommRingCat.{u + 1}).hom.app F).app
        (op U) ≫ F.obj.map
          ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X (𝟙 X) rfl).inv.app U).op := by
  let i := proEtaleIsoInverseImageIdentification (𝟙 X) CommRingCat.{u + 1}
  have hn := (existsUnique_proEtaleIsoInverseImageIdentification (𝟙 X)
    CommRingCat.{u + 1}).exists.choose_spec F U
  apply (cancel_epi ((i.inv.app F).app (op U))).1
  change (i.inv.app F).app (op U) ≫ _ =
    (i.inv.app F).app (op U) ≫ (i.hom.app F).app (op U) ≫ _
  have hi := congrArg (fun f ↦ f.app (op U)) (i.inv_hom_id_app F)
  dsimp only [NatTrans.comp_app, NatTrans.id_app] at hi
  rw [← Category.assoc, hi, Category.id_comp]
  change (i.inv.app F).app (op U) = _ at hn
  let V := (proEtaleIsoPostcompose (𝟙 X)).obj U
  let δ := proEtaleIsoCommaArrow (𝟙 X) U
  let a := ((identityRingIso X).hom.app F).hom
  let η := ((proEtaleSheafAdjunction (𝟙 X) CommRingCat.{u + 1}).unit.app F).hom
  have hu := congrArg (fun h ↦ h.hom.app (op V)) (identityRingIso_unit X F)
  change η.app (op V) ≫ a.app (op ((proEtaleBaseChange (𝟙 X)).obj V)) =
      F.obj.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op at hu
  calc
    _ = (η.app (op V) ≫
        ((proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1}).obj F).obj.map δ.op) ≫
          a.app (op U) := congrArg (fun h ↦ h ≫ a.app (op U)) hn
    _ = η.app (op V) ≫ (a.app (op ((proEtaleBaseChange (𝟙 X)).obj V)) ≫
        F.obj.map δ.op) := by
      exact (Category.assoc _ _ _).trans
        (congrArg (fun h ↦ η.app (op V) ≫ h) (a.naturality δ.op))
    _ = F.obj.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op ≫
        F.obj.map δ.op := (Category.assoc _ _ _).symm.trans
          (congrArg (fun h ↦ h ≫ F.obj.map δ.op) hu)
    _ = F.obj.map (δ ≫
        (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op :=
      (F.obj.map_comp _ _).symm
    _ = _ := by
      apply congrArg F.obj.map
      apply congrArg Quiver.Hom.op
      apply MorphismProperty.Over.Hom.ext
      change δ.left ≫ ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).left =
        𝟙 U.left
      rw [MorphismProperty.Over.pullbackId_hom_app_left]
      change pullback.lift (𝟙 U.left) U.hom (by simp) ≫
        pullback.fst (U.hom ≫ 𝟙 X) (𝟙 X) = 𝟙 U.left
      exact pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
private def cancelScalarTransport {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (c : R ≅ S)
    (M : proEtaleRingModules X S) :
    (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)).obj
        ((SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).obj M) ≅ M := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · exact (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
      (c.hom.hom.app U).hom (RingHom.id _) (by
        exact congrArg RingCat.Hom.hom (congrArg (fun f ↦
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map f).hom.app U)
            c.inv_hom_id).symm) (M.val.obj U)).symm ≪≫
        (ModuleCat.restrictScalarsId _).app (M.val.obj U)
  · intros
    ext x
    rfl

-- Scalar transport and the small-site model require additional elaboration steps.
set_option backward.isDefEq.respectTransparency false in
private theorem identityModule_exists (X : Scheme.{u}) (A : Type u) [CommRing A] :
    ∃ eM : proEtaleIdentityTransportedInverseImage X A ≅
        𝟭 (proEtaleRingModules X (proEtaleConstantRing X A)),
      ∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEt)
        (m : M.val.obj (op U)),
        (eM.inv.app M).val.app (op U) m = proEtaleIdentityModuleCoprojection X A M U m := by
  let R := proEtaleConstantRing X A
  let c := proEtaleConstantRingComparison (𝟙 X) A
  let I := proEtaleModuleInverseImage (𝟙 X) R
  let T := SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)
  have hc : ProEtaleTensorComparison.ringId R = c := by
    apply Iso.ext
    exact identityRingIso_coefficient X A
  have hd (M : proEtaleRingModules X R) :
      ∃ d : I.obj M ≅ (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).obj M,
        ∀ (V : X.ProEt) (s : M.val.obj (op V)),
          d.hom.val.app (op ((proEtaleBaseChange (𝟙 X)).obj V))
            (ProEtaleTensorComparison.inverseSection (𝟙 X) M V s) =
          M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V).op s := by
    change ∃ d : (ProEtaleTensorComparison.inverse (𝟙 X) R).obj M ≅
        (ProEtaleTensorComparison.restrict c.hom).obj M, _
    rw [← hc]
    exact (ProEtaleTensorComparison.moduleId_exists R M).exists
  choose d hd using hd
  let e (M : proEtaleRingModules X R) := T.mapIso (d M) ≪≫ cancelScalarTransport c M
  have he (M : proEtaleRingModules X R) (U : X.ProEt) (m : M.val.obj (op U)) :
      (e M).inv.val.app (op U) m = proEtaleIdentityModuleCoprojection X A M U m := by
    have : IsIso ((e M).hom.val.app (op U)) :=
      inferInstanceAs (IsIso ((SheafOfModules.evaluation _ (op U)).map (e M).hom))
    apply (ConcreteCategory.bijective_of_isIso ((e M).hom.val.app (op U))).1
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun h ↦ h.val.app (op U)) (e M).inv_hom_id) m
    change (e M).hom.val.app (op U) ((e M).inv.val.app (op U) m) = m at hi
    have hnorm : (e M).hom.val.app (op U)
        (proEtaleIdentityModuleCoprojection X A M U m) = m := by
      let p := MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X
      let z := ProEtaleTensorComparison.inverseSection (𝟙 X) M U m
      calc
        _ = M.val.map (p.inv.app U).op
            ((e M).hom.val.app (op ((proEtaleBaseChange (𝟙 X)).obj U)) z) :=
          PresheafOfModules.naturality_apply (e M).hom.val (p.inv.app U).op z
        _ = M.val.map (p.inv.app U).op (M.val.map (p.hom.app U).op m) :=
          congrArg (fun z ↦ M.val.map (p.inv.app U).op z) (hd M U m)
        _ = M.val.map ((p.hom.app U).op ≫ (p.inv.app U).op) m :=
          ConcreteCategory.congr_hom (M.val.map_comp (p.hom.app U).op
            (p.inv.app U).op).symm m
        _ = m := by
          rw [← op_comp, p.inv_hom_id_app]
          exact ConcreteCategory.congr_hom (M.val.map_id (op U)) m
    exact hi.trans hnorm.symm
  let eM : I ⋙ T ≅ 𝟭 _ := (NatIso.ofComponents (fun M ↦ (e M).symm) (by
    intro M N f
    ext U m
    change (e N).inv.val.app U (f.val.app U m) =
      (I.map f).val.app U ((e M).inv.val.app U m)
    erw [he N U.unop, he M U.unop]
    symm
    unfold proEtaleIdentityModuleCoprojection
    have hn := PresheafOfModules.naturality_apply (I.map f).val
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U.unop).op
      (ProEtaleTensorComparison.inverseSection (𝟙 X) M U.unop m)
    refine hn.trans ?_
    apply congrArg (fun z ↦ (I.obj N).val.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app U.unop).op z)
    exact (ConcreteCategory.congr_hom (congrArg (fun h ↦ h.val.app
      (AsSmall.up.op.obj U))
        ((SheafOfModules.pullbackPushforwardAdjunction
          (proEtaleModelRingUnit (𝟙 X) R)).unit.naturality
            ((proEtaleModuleToModel ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).map f))) m).symm)).symm
  exact ⟨eM, he⟩

-- Scalar transport and the small-site model require additional elaboration steps.
set_option backward.isDefEq.respectTransparency false in
/-- The specified identity comparison equals the canonical coefficient map, is linear
after scalar transport, and descends termwise to ordinary unbounded derived pullback. -/
theorem proEtaleDerivedPullback_identity (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] :
    ∃ e : proEtaleSheafInverseImage (𝟙 X) CommRingCat.{u + 1} ≅
        𝟭 (Sheaf (ProEt.topology X) CommRingCat.{u + 1}),
      (∀ (F : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : X.ProEt),
        (e.hom.app F).hom.app (op U) =
          ((proEtaleIsoInverseImageIdentification (𝟙 X) CommRingCat.{u + 1}).hom.app F).app
              (op U) ≫
            F.obj.map
              ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X (𝟙 X) rfl).inv.app U).op) ∧
      e.hom.app (proEtaleConstantRing X A) = proEtaleCoefficientInverseImageMap (𝟙 X) A ∧
      ∃ eM : proEtaleIdentityTransportedInverseImage X A ≅
          𝟭 (proEtaleRingModules X (proEtaleConstantRing X A)),
        (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEt)
          (m : M.val.obj (op U)),
          (eM.inv.app M).val.app (op U) m = proEtaleIdentityModuleCoprojection X A M U m) ∧
        ∃ alpha : proEtaleConstantRingPullback.{u} A (𝟙 X) ≅
            𝟭 (proEtaleRingModules X (proEtaleConstantRing X A)),
          (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEtᵒᵖ)
            (m : ((proEtaleModuleInverseImage (𝟙 X) (proEtaleConstantRing X A)).obj M).val.obj U)
            (a : (proEtaleConstantRing X A).obj.obj U),
            (alpha.hom.app M).val.app U (proEtaleIdentityPullbackTmul X A M U m a) =
              a • (eM.hom.app M).val.app U m) ∧
          (∀ (M : proEtaleRingModules X (proEtaleConstantRing X A)) (U : X.ProEtᵒᵖ)
            (m : M.val.obj U),
            (alpha.inv.app M).val.app U m =
              proEtaleIdentityPullbackTmul X A M U ((eM.inv.app M).val.app U m) 1) ∧
          ∃ b : (proEtaleConstantRingPullback.{u} A (𝟙 X)).mapHomologicalComplex
                (ComplexShape.up ℤ) ≅
              𝟭 (CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ),
            (∀ (K : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
              (j : ℤ), (b.hom.app K).f j = alpha.hom.app (K.X j)) ∧
            ∃ gamma : proEtaleConstantRingDerivedPullback.{u} A (𝟙 X) ≅
                𝟭 (proEtaleDerivedCategory X A),
              ∀ K : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ,
                gamma.hom.app ((proEtaleIdentityLocalization X A).obj K) =
                  (proEtaleRingDerivedPullbackFactors (𝟙 X)
                    (proEtaleConstantRing X A) (proEtaleConstantRing X A)
                    (proEtaleConstantRingComparison (𝟙 X) A)).hom.app K ≫
                    (proEtaleIdentityLocalization X A).map (b.hom.app K) := by
  let _ := WeilConjectures.integralCoefficientAbSheafify.{u, u} X
  let _ := WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X
  let R := proEtaleConstantRing X A
  let c := proEtaleConstantRingComparison (𝟙 X) A
  let I := proEtaleModuleInverseImage (𝟙 X) R
  let T := SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)
  obtain ⟨eM, heM⟩ := identityModule_exists X A
  obtain ⟨theta, htheta, hthetaInv, hthetaNat⟩ :=
    SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, u + 1} c
  let F := proEtaleConstantRingPullback.{u} A (𝟙 X)
  let alpha : F ≅ 𝟭 _ := NatIso.ofComponents
    (fun M ↦ theta (I.obj M) ≪≫ eM.app M) (by
      intro M N f
      change F.map f ≫ ((theta (I.obj N)).hom ≫ eM.hom.app N) =
        ((theta (I.obj M)).hom ≫ eM.hom.app M) ≫ f
      have ht : F.map f ≫ (theta (I.obj N)).hom =
          (theta (I.obj M)).hom ≫ T.map (I.map f) := hthetaNat _ _ (I.map f)
      have he : T.map (I.map f) ≫ eM.hom.app N = eM.hom.app M ≫ f :=
        eM.hom.naturality f
      calc
        _ = (F.map f ≫ (theta (I.obj N)).hom) ≫ eM.hom.app N :=
          (Category.assoc _ _ _).symm
        _ = ((theta (I.obj M)).hom ≫ T.map (I.map f)) ≫ eM.hom.app N :=
          congrArg (fun h ↦ h ≫ eM.hom.app N) ht
        _ = (theta (I.obj M)).hom ≫ (eM.hom.app M ≫ f) :=
          (Category.assoc _ _ _).trans (congrArg (fun h ↦ (theta (I.obj M)).hom ≫ h) he)
        _ = _ := (Category.assoc _ _ _).symm)
  let b := NatIso.mapHomologicalComplex alpha (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (proEtaleRingModules X R) (ComplexShape.up ℤ)
  let Q := proEtaleIdentityLocalization X A
  let D := proEtaleConstantRingDerivedPullback.{u} A (𝟙 X)
  let fac := proEtaleRingDerivedPullbackFactors (𝟙 X) R R c
  let W := HomologicalComplex.quasiIso (proEtaleRingModules X R) (ComplexShape.up ℤ)
  let beta : Q ⋙ D ≅ Q ⋙ 𝟭 _ :=
    fac ≪≫ Functor.isoWhiskerRight b Q ≪≫ Q.leftUnitor ≪≫ Q.rightUnitor.symm
  let FF := Localization.fullyFaithfulWhiskeringLeft Q W (proEtaleDerivedCategory X A)
  let gamma : D ≅ 𝟭 _ := FF.preimageIso beta
  refine ⟨identityRingIso X, identityRingIso_normalization X,
    identityRingIso_coefficient X A, eM, heM, alpha, ?_, ?_, b, ?_, gamma, ?_⟩
  · intro M U m a
    change (eM.hom.app M).val.app U
      ((theta (I.obj M)).hom.val.app U
        (SheafOfModules.scalarExtensionRingIsoTmul.{u + 1, u, u + 1, u + 1}
          c.hom (I.obj M) U m a)) = _
    rw [htheta]
    exact ((eM.hom.app M).val.app U).hom.map_smul a m
  · intro M U m
    change (theta (I.obj M)).inv.val.app U ((eM.inv.app M).val.app U m) = _
    exact hthetaInv _ _ _
  · intro K j
    change alpha.hom.app (K.X j) ≫ 𝟙 _ = alpha.hom.app (K.X j)
    exact Category.comp_id _
  · intro K
    have h := congrArg (fun τ ↦ τ.app K) (FF.map_preimage beta.hom)
    change gamma.hom.app (Q.obj K) = beta.hom.app K at h
    rw [h]
    dsimp [beta]
    simp only [Category.comp_id]
    rfl

end AlgebraicGeometry.Scheme
