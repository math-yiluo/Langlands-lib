/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison

import WeilConjectures.AlgebraicGeometry.SmoothPurity.AmbTateRootProjectionReduction
import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualTowerCore

/-! # Fixed-scalar presentation of the finite root projection

Source: Stacks Project, Tags 03CY, 03EK and 03PK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u c v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.Scheme

-- Pin the existing coefficient-size instances to avoid an unconstrained maximum universe.
attribute [local instance] WeilConjectures.sfAbSheafify
attribute [local instance] AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify
attribute [local instance] WeilConjectures.sfAbBijective
attribute [local instance] WeilConjectures.instEssentiallySmallProEt_weilConjectures
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
open scoped ChangeOfRings
local instance (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    HasSheafify (ProEt.topology T) (ModuleCat.{u + 1} A) :=
  ConstantScalarRestriction.fixedSheafify.{u + 1, u} (ProEt.topology T) A
attribute [local semireducible] finiteRootProModule finiteRootProTensor finiteRootProGenerator

private def rootsAddHomEquiv (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (N : SheafOfModules.{u + 1} (purTwistRing T (purTwistFiniteRing T l r))) :
    (purTwistRootsModule T l r ⟶ N) ≃
      (proEtaleRootsOfUnitySheaf T (l ^ (r + 1)) ⟶
        (SheafOfModules.toSheaf _).obj N) where
  toFun f := (SheafOfModules.toSheaf _).map f
  invFun f := by
    let F := ConstantScalarRestriction.restriction (ProEt.topology T)
      (ULift.{u + 1} (ZMod (l ^ (r + 1))))
    have : F.IsEquivalence := inferInstance
    exact F.preimage { hom := {
      app := fun U ↦ ModuleCat.ofHom
        (X := (F.obj (purTwistRootsModule T l r)).obj.obj U)
        (Y := (F.obj N).obj.obj U) {
        toFun := f.hom.app U
        map_add' := map_add _
        map_smul' := by
          intro a x
          obtain ⟨z, hz⟩ := ZMod.intCast_surjective a.down
          have ha : (z : ULift.{u + 1} (ZMod (l ^ (r + 1)))) = a :=
            ULift.ext hz
          rw [← ha]
          exact map_intCast_smul (show
            (F.obj (purTwistRootsModule T l r)).obj.obj U →+ (F.obj N).obj.obj U
            from (f.hom.app U).hom)
            (ULift.{u + 1} (ZMod (l ^ (r + 1))))
            (ULift.{u + 1} (ZMod (l ^ (r + 1)))) z x }
      naturality := by
        intro U V g
        ext x
        exact ConcreteCategory.congr_hom (f.hom.naturality g) x } }
  left_inv f := by
    apply (ConstantScalarRestriction.restriction (ProEt.topology T)
      (ULift.{u + 1} (ZMod (l ^ (r + 1))))).map_injective
    rw [Functor.map_preimage]
    ext U x
    rfl
  right_inv f := by
    let F := ConstantScalarRestriction.restriction (ProEt.topology T)
      (ULift.{u + 1} (ZMod (l ^ (r + 1))))
    ext U x
    exact congrArg (fun g : F.obj (purTwistRootsModule T l r) ⟶ F.obj N ↦
      g.hom.app U x) (F.map_preimage _)

private def scalarHomEquiv {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    {R S : Sheaf J CommRingCat.{w}} (α : R ⟶ S)
    (M : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (N : SheafOfModules.{w} ((sheafCompose J
      (forget₂ CommRingCat.{w} RingCat.{w})).obj S)) :
    (SheafOfModules.changeOfRingsOfUniverses.{v, c, w, w} α M ⟶ N) ≃
      (M ⟶ (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map α)).obj N) where
  toFun f := SheafOfModules.scalarExtensionEmbedding.{c, v, w, w}
    α M ≫
      (SheafOfModules.restrictScalars.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map α)).map f
  invFun f := SheafOfModules.scalarExtensionLift.{c, v, w, w}
    α M N f
  left_inv f := by
    apply SheafOfModules.scalarExtension_hom_ext.{c, v, w, w} α
      M
    intro U a x
    rw [SheafOfModules.scalarExtensionLift_tmul.{c, v, w, w}]
    change a • f.val.app U
      (SheafOfModules.scalarExtensionSection.{c, v, w, w} α
        M U 1 x) = _
    exact ((f.val.app U).hom.map_smul a _).symm.trans
      (congrArg (fun y ↦ f.val.app U y)
        ((SheafOfModules.scalarExtensionSection_smul.{c, v, w, w}
          α M U a 1 x).trans (by rw [mul_one])))
  right_inv f := by
    ext U x
    change (SheafOfModules.scalarExtensionLift.{c, v, w, w} _ _ _ f).val.app U
      (SheafOfModules.scalarExtensionSection.{c, v, w, w} α
        M U 1 x) = _
    rw [SheafOfModules.scalarExtensionLift_tmul.{c, v, w, w}, one_smul]

private def extensionHomEquiv (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (r : AmbTateLevel l E n)
    (N : SheafOfModules.{u + 1} (integralCoefficientSheaf l E T n)) :=
  scalarHomEquiv.{u + 1, u, u + 1} (ambTateFiniteScalar l E n T r) (purTwistRootsModule T l r.val) N

private def ringTensorHomEquiv (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (r : AmbTateLevel l E n)
    (N : SheafOfModules.{u + 1} (integralCoefficientSheaf l E T n)) :
    ((finiteTateConstantRestriction l E n T).obj (ambTateFiniteRoots l E n T r) ⟶
      (finiteTateConstantRestriction l E n T).obj N) ≃
      (proEtaleRootsOfUnitySheaf T (l ^ (r.val + 1)) ⟶
        (SheafOfModules.toSheaf _).obj N) := by
  let F := finiteTateConstantRestriction l E n T
  have : F.IsEquivalence :=
    ConstantScalarRestriction.isEquivalence (ProEt.topology T) (finiteTateCoefficient l E n)
  exact (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm.trans
    ((extensionHomEquiv T l E n r N).trans (rootsAddHomEquiv T l r.val _))

private theorem ringTensorHomEquiv_generator (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (r : AmbTateLevel l E n)
    (N : SheafOfModules.{u + 1} (integralCoefficientSheaf l E T n))
    (f : (finiteTateConstantRestriction l E n T).obj (ambTateFiniteRoots l E n T r) ⟶
      (finiteTateConstantRestriction l E n T).obj N)
    (W : T.ProEtᵒᵖ) (z : (proEtaleRootsOfUnitySheaf T (l ^ (r.val + 1))).obj.obj W) :
    (ringTensorHomEquiv T l E n r N f).hom.app W z =
      f.hom.app W (ambTateFinitePure l E n T r W.unop 1 z) := by
  let F := finiteTateConstantRestriction l E n T
  have : F.IsEquivalence :=
    ConstantScalarRestriction.isEquivalence (ProEt.topology T) (finiteTateCoefficient l E n)
  change (F.preimage f).val.app W
    (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
      (ambTateFiniteScalar l E n T r) (purTwistRootsModule T l r.val) W 1 z) = _
  exact congrArg (fun g : F.obj (ambTateFiniteRoots l E n T r) ⟶ F.obj N ↦
    g.hom.app W (ambTateFinitePure l E n T r W.unop 1 z)) (F.map_preimage f)

private theorem ringTensorHomEquiv_comp (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (r : AmbTateLevel l E n)
    {N M : SheafOfModules.{u + 1} (integralCoefficientSheaf l E T n)}
    (f : (finiteTateConstantRestriction l E n T).obj (ambTateFiniteRoots l E n T r) ⟶
      (finiteTateConstantRestriction l E n T).obj N)
    (g : (finiteTateConstantRestriction l E n T).obj N ⟶
      (finiteTateConstantRestriction l E n T).obj M) :
    ringTensorHomEquiv T l E n r M (f ≫ g) =
      ringTensorHomEquiv T l E n r N f ≫
        (sheafCompose (ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} (finiteTateCoefficient l E n))
            AddCommGrpCat.{u + 1})).map g := by
  ext W z
  rw [ringTensorHomEquiv_generator]
  change g.hom.app W (f.hom.app W _) =
    g.hom.app W ((ringTensorHomEquiv T l E n r N f).hom.app W z)
  rw [ringTensorHomEquiv_generator]

private def fixedToRingTensor (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (r : AmbTateLevel l E n)
    (hA : ((l ^ (r.val + 1) : ℕ) : finiteTateCoefficient l E n) = 0) :
    finiteRootProTensor (finiteTateCoefficient l E n) (l ^ (r.val + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hA T ⟶
        (finiteTateConstantRestriction l E n T).obj (ambTateFiniteRoots l E n T r) :=
  (proLineHomEquiv T _ (pow_pos (Fact.out : l.Prime).pos _)
    (finiteTateCoefficient l E n) hA _).symm
      (ringTensorHomEquiv T l E n r (ambTateFiniteRoots l E n T r) (𝟙 _))

private theorem fixedToRingTensor_comp (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (r : AmbTateLevel l E n)
    (hA : ((l ^ (r.val + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (N : SheafOfModules.{u + 1} (integralCoefficientSheaf l E T n))
    (f : (finiteTateConstantRestriction l E n T).obj (ambTateFiniteRoots l E n T r) ⟶
      (finiteTateConstantRestriction l E n T).obj N) :
    proLineHomEquiv T _ (pow_pos (Fact.out : l.Prime).pos _)
      (finiteTateCoefficient l E n) hA _ (fixedToRingTensor T l E n r hA ≫ f) =
        ringTensorHomEquiv T l E n r N f := by
  rw [proLineHomEquiv_comp, fixedToRingTensor, Equiv.apply_symm_apply]
  exact (ringTensorHomEquiv_comp T l E n r (𝟙 _) f).symm.trans
    (congrArg (ringTensorHomEquiv T l E n r N) (Category.id_comp f))

private theorem fixedToRingTensor_isIso (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (r : AmbTateLevel l E n)
    (hA : ((l ^ (r.val + 1) : ℕ) : finiteTateCoefficient l E n) = 0) :
    IsIso (fixedToRingTensor T l E n r hA) := by
  let F := finiteTateConstantRestriction l E n T
  have : F.IsEquivalence :=
    ConstantScalarRestriction.isEquivalence (ProEt.topology T) (finiteTateCoefficient l E n)
  apply isIso_of_coyoneda_map_bijective
  intro P
  obtain ⟨N, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage F P
  let e := (Iso.homCongr (Iso.refl _) i.symm).trans
    ((ringTensorHomEquiv T l E n r N).trans
      ((proLineHomEquiv T _ (pow_pos (Fact.out : l.Prime).pos _)
        (finiteTateCoefficient l E n) hA _).symm.trans
          (Iso.homCongr (Iso.refl _) i)))
  suffices (fun g ↦ fixedToRingTensor T l E n r hA ≫ g) = e by
    rw [this]
    exact e.bijective
  funext g
  apply (Iso.homCongr (Iso.refl _) i.symm).injective
  apply (proLineHomEquiv T _ (pow_pos (Fact.out : l.Prime).pos _)
    (finiteTateCoefficient l E n) hA _).injective
  simp only [e, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.symm_hom, Iso.refl_inv, Category.id_comp, Category.assoc]
  change (proLineHomEquiv T _ (pow_pos (Fact.out : l.Prime).pos _)
    (finiteTateCoefficient l E n) hA (F.obj N))
      (fixedToRingTensor T l E n r hA ≫ g ≫ i.inv) =
    (proLineHomEquiv T _ (pow_pos (Fact.out : l.Prime).pos _)
      (finiteTateCoefficient l E n) hA (F.obj N))
        (((proLineHomEquiv T _ (pow_pos (Fact.out : l.Prime).pos _)
          (finiteTateCoefficient l E n) hA (F.obj N)).symm
            (ringTensorHomEquiv T l E n r N (g ≫ i.inv)) ≫ i.hom) ≫ i.inv)
  rw [Category.assoc, i.hom_inv_id, Category.comp_id]
  exact (fixedToRingTensor_comp T l E n r hA N (g ≫ i.inv)).trans
    ((proLineHomEquiv T _ (pow_pos (Fact.out : l.Prime).pos _)
      (finiteTateCoefficient l E n) hA (F.obj N)).apply_symm_apply _).symm

private theorem restricted_smul (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (N : SheafOfModules.{u + 1} (integralCoefficientSheaf l E T n)) (W : T.ProEtᵒᵖ)
    (a : finiteTateCoefficient l E n) (x : N.val.obj W) :
    a • (show ((finiteTateConstantRestriction l E n T).obj N).obj.obj W from x) =
      (show (integralCoefficientSheaf l E T n).obj.obj W from
        (realizationRingUnit (ProEt.topology T) (finiteTateCoefficient l E n)).app W a) •
          x := by
  let J := ProEt.topology T
  let A := finiteTateCoefficient l E n
  have hc := toSheafify_naturality J
    (Functor.constComp T.ProEtᵒᵖ (CommRingCat.of A)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv
  have hu : ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) ≫
      ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of A)).hom).app W) a =
      (realizationRingUnit J A).app W a := by
    change ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) ≫
      sheafifyMap J (Functor.constComp T.ProEtᵒᵖ (CommRingCat.of A)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv ≫
      (sheafifyComposeIso J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of A))).hom).app W) a = _
    erw [← Category.assoc, ← hc, Category.assoc, sheafComposeIso_hom_fac]
    rfl
  change (show (integralCoefficientSheaf l E T n).obj.obj W from
    ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) ≫
      ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of A)).hom).app W) a) • x = _
  exact congrArg (fun b : (integralCoefficientSheaf l E T n).obj.obj W ↦ b • x) hu

private theorem fixedToRingTensor_generator (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (r : AmbTateLevel l E n)
    (hA : ((l ^ (r.val + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (W : T.ProEtᵒᵖ) (a : finiteTateCoefficient l E n)
    (z : (proEtaleRootsOfUnitySheaf T (l ^ (r.val + 1))).obj.obj W) :
    (fixedToRingTensor T l E n r hA).hom.app W
      (finiteRootProGenerator (finiteTateCoefficient l E n) (l ^ (r.val + 1))
        (pow_pos (Fact.out : l.Prime).pos _) hA T W a z) =
    ambTateFinitePure l E n T r W.unop
      ((realizationRingUnit (ProEt.topology T) (finiteTateCoefficient l E n)).app W a) z := by
  let F := finiteTateConstantRestriction l E n T
  let D := ambTateFiniteRoots l E n T r
  let p := proLineHomEquiv T _ (pow_pos (Fact.out : l.Prime).pos _)
    (finiteTateCoefficient l E n) hA (F.obj D)
  have h := congrArg (fun f ↦ f.hom.app W z)
    (p.apply_symm_apply (ringTensorHomEquiv T l E n r D (𝟙 _)))
  change (proLineHomEquiv T _ (pow_pos (Fact.out : l.Prime).pos _)
    (finiteTateCoefficient l E n) hA _ (fixedToRingTensor T l E n r hA)).hom.app W z = _ at h
  rw [proLineHomEquiv_generator] at h
  have h1 := h.trans
    (ringTensorHomEquiv_generator T l E n r D (𝟙 _) W z)
  change (fixedToRingTensor T l E n r hA).hom.app W
    (finiteRootProGenerator (finiteTateCoefficient l E n) (l ^ (r.val + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hA T W 1 z) =
      ambTateFinitePure l E n T r W.unop 1 z at h1
  have hs : finiteRootProGenerator (finiteTateCoefficient l E n) (l ^ (r.val + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hA T W a z =
    a • finiteRootProGenerator (finiteTateCoefficient l E n) (l ^ (r.val + 1))
      (pow_pos (Fact.out : l.Prime).pos _) hA T W 1 z := by
    let η := (toSheafify (ProEt.topology T)
      ((finiteRootProModule T (l ^ (r.val + 1))
        (pow_pos (Fact.out : l.Prime).pos _)).obj ⋙
          ModuleCat.extendScalars (finiteEtaleTwistScalar (l ^ (r.val + 1))
            (finiteTateCoefficient l E n) hA))).app W
    let z' : (finiteRootProModule T (l ^ (r.val + 1))
      (pow_pos (Fact.out : l.Prime).pos _)).obj.obj W := z
    let φ := finiteEtaleTwistScalar (l ^ (r.val + 1)) (finiteTateCoefficient l E n) hA
    have hmul := η.hom.map_smul a
      ((1 : finiteTateCoefficient l E n) ⊗ₜ[ZMod (l ^ (r.val + 1)), φ] z')
    change η (a ⊗ₜ[ZMod (l ^ (r.val + 1)), φ] z') =
      a • η ((1 : finiteTateCoefficient l E n) ⊗ₜ[ZMod (l ^ (r.val + 1)), φ] z')
    change η ((a * 1) ⊗ₜ[ZMod (l ^ (r.val + 1)), φ] z') =
      a • η ((1 : finiteTateCoefficient l E n) ⊗ₜ[ZMod (l ^ (r.val + 1)), φ] z') at hmul
    exact (congrArg (fun b : finiteTateCoefficient l E n ↦
      η (b ⊗ₜ[ZMod (l ^ (r.val + 1)), φ] z')) (mul_one a)).symm.trans hmul
  rw [hs, map_smul, h1]
  exact (restricted_smul T l E n D W a
    (ambTateFinitePure l E n T r W.unop 1 z)).trans (by
      change (show (integralCoefficientSheaf l E T n).obj.obj W from
        (realizationRingUnit (ProEt.topology T) (finiteTateCoefficient l E n)).app W a) •
          (show D.val.obj W from ambTateFinitePure l E n T r W.unop 1 z) =
            (show D.val.obj W from ambTateFinitePure l E n T r W.unop
              ((realizationRingUnit (ProEt.topology T)
                (finiteTateCoefficient l E n)).app W a) z)
      have he (b : (integralCoefficientCommRingSheaf l E T n).obj.obj W) :
          ambTateFinitePure l E n T r W.unop b z =
            SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
              (ambTateFiniteScalar l E n T r) (purTwistRootsModule T l r.val) W b z := by
        unfold ambTateFinitePure purScalarSection SheafOfModules.scalarExtensionSection
        rfl
      rw [he, he]
      have hm := SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}
        (ambTateFiniteScalar l E n T r) (purTwistRootsModule T l r.val) W
        ((realizationRingUnit (ProEt.topology T) (finiteTateCoefficient l E n)).app W a)
        1 z
      rw [mul_one] at hm
      convert hm using 1 <;> rfl)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (n : ℕ)

/-- The root projection identifies the first finite coefficient twist with the
fixed-scalar extension of the finite roots module, retaining its tensor formula.
Source: Stacks 03CY, 03EK and 03PK; the first step of
`lem-amb-finite-tate-normalized-comparisons`.
(blueprint: lem-amb-finite-tate-root-tensor-presentation).

Proof: map the global unit hypothesis to each stalk and lower the annihilation
identity through `ULift.down`. Apply `ambTateRootProjectionReduction` and restrict
its theta to constant coefficients. The restricted ringed scalar extension and
`finiteRootProTensor` both represent additive maps from the finite root sheaf:
additive maps are linear for lifted ZMod scalars since every scalar is an integer
cast; fullness of constant-scalar restriction upgrades this to sheaf-ring linearity.
Compose the scalar-extension and sheafification Hom equivalences to construct a
comparison. Precomposition with it is bijective for every target, so it is invertible.
Its formula on `1` tensors comes from the Hom equivalences and its formula on general
tensors from linearity. Sheafification naturality identifies the RingCat constant unit
with the CommRingCat unit in the prescribed generator. Compose theta with the inverse
comparison. The `j_pure` formula at integral scalar `1` and `theta_pure` then give the
required generator equation. No primitive root, flatness or nonempty-base hypothesis
is used, so the construction includes the empty scheme and zero coefficients. -/
theorem finite_tate_root_tensor_presentation (T : Scheme.{u})
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) :
    ∃ e : finiteTateProSheaf l E n T 1 ≅
      finiteRootProTensor (finiteTateCoefficient l E n) (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) hA T,
      ∀ (W : T.ProEtᵒᵖ) (a : finiteTateCoefficient l E n)
        (x : (purTwistZlOne T l).obj.obj W),
        e.hom.hom.app W (finiteTateProGenerator l E n T W a x) =
          finiteRootProGenerator (finiteTateCoefficient l E n) (l ^ (r + 1))
            (pow_pos (Fact.out : l.Prime).pos _) hA T W a
            ((limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime))
              (op r)).hom.app W x) := by
  obtain ⟨d⟩ := ambTateRootProjectionReduction l E n
  let T' : AmbTateBase l := ⟨T, fun x ↦ by
    simpa using hT.map (T.presheaf.germ ⊤ x (by trivial)).hom⟩
  let r' : AmbTateLevel l E n := ⟨r, by
    exact congrArg ULift.down hA⟩
  have : IsIso (fixedToRingTensor T l E n r' hA) :=
    fixedToRingTensor_isIso T l E n r' hA
  let e := (finiteTateConstantRestriction l E n T).mapIso (d.theta T' r') ≪≫
    (asIso (fixedToRingTensor T l E n r' hA)).symm
  refine ⟨e, ?_⟩
  intro W a x
  apply (ModuleCat.mono_iff_injective
    ((fixedToRingTensor T l E n r' hA).hom.app W)).mp inferInstance
  rw [fixedToRingTensor_generator]
  have h := d.j_pure T' W.unop
    ((realizationRingUnit (ProEt.topology T) (finiteTateCoefficient l E n)).app W a) 1 x
  simp only [map_one, mul_one] at h
  have hj : (d.j T').inv.val.app W
      (ambTateReducedPure l E n T W.unop
        ((realizationRingUnit (ProEt.topology T) (finiteTateCoefficient l E n)).app W a) x) =
      finiteTateProGenerator l E n T W a x := by
    rw [← h]
    exact congrArg (fun f ↦ f.val.app W
      (ambTateSourcePure l E n T W.unop
        ((realizationRingUnit (ProEt.topology T) (finiteTateCoefficient l E n)).app W a) 1 x))
      (d.j T').hom_inv_id
  have ht := d.theta_pure T' r' W.unop
    ((realizationRingUnit (ProEt.topology T) (finiteTateCoefficient l E n)).app W a) x
  rw [hj] at ht
  change (fixedToRingTensor T l E n r' hA).hom.app W
    ((inv (fixedToRingTensor T l E n r' hA)).hom.app W
      ((d.theta T' r').hom.val.app W (finiteTateProGenerator l E n T W a x))) = _
  have hc := congrArg (fun f ↦ f.hom.app W
    ((d.theta T' r').hom.val.app W (finiteTateProGenerator l E n T W a x)))
      (IsIso.inv_hom_id (fixedToRingTensor T l E n r' hA))
  exact hc.trans ht

end AlgebraicGeometry.Scheme
