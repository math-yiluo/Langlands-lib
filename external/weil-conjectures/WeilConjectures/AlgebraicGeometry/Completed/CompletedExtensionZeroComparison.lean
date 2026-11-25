/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import all WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.PreservesSheafification

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
/-! # Completed open-immersion base change

Source: blueprint order 1587; Stacks Tags 03DI, 09BP, 099N
(blueprint: lem-cbc-completed-extension-zero-comparison).
All extension functors below are the specified direct-sum presheaf followed by
module sheafification, transported along the ringed slice-site identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
/-- The counit equation determining a derived exchange on specified representatives.
Naming the generic condition avoids repeated expansion in its concrete module instances.
Source: universal derived counits (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def CategoryTheory.Functor.DerivedExchangeCounitNormalization
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    [Abelian C] [Abelian C'] [Abelian D] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory C']
    [HasDerivedCategory D] [HasDerivedCategory D']
    (F : C ⥤ C') (G : D ⥤ D') (J : C ⥤ D) (J' : C' ⥤ D')
    [F.Additive] [G.Additive] [J.Additive] [J'.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    (LF : DerivedCategory C ⥤ DerivedCategory C')
    (LG : DerivedCategory D ⥤ DerivedCategory D')
    (ε : ∀ P : CochainComplex C ℤ, LF.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : ∀ P : CochainComplex D ℤ, LG.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
    (b : F ⋙ J' ⟶ J ⋙ G) (Good : CochainComplex C ℤ → Prop)
    (α : LF ⋙ J'.mapDerivedCategory ⟶ J.mapDerivedCategory ⋙ LG) : Prop :=
  ∀ P, Good P → α.app (DerivedCategory.Q.obj P) ≫
      LG.map (J.mapDerivedCategoryFactors.hom.app P) ≫
      δ ((J.mapHomologicalComplex (.up ℤ)).obj P) =
    J'.mapDerivedCategory.map (ε P) ≫
      J'.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex b (.up ℤ)).app P)

/-- Derive a square using exact presentations and their normalized counits.
Source: composition-factorization equations for exact derived functors
(blueprint: lem-cbc-completed-extension-zero-comparison). -/
private theorem exactExchange_normalization
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    [Abelian C] [Abelian C'] [Abelian D] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory C']
    [HasDerivedCategory D] [HasDerivedCategory D']
    (F : C ⥤ C') (G : D ⥤ D') (J : C ⥤ D) (J' : C' ⥤ D')
    [F.Additive] [G.Additive] [J.Additive] [J'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    (LF : DerivedCategory C ⥤ DerivedCategory C')
    (LG : DerivedCategory D ⥤ DerivedCategory D')
    (ε : ∀ P : CochainComplex C ℤ, LF.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : ∀ P : CochainComplex D ℤ, LG.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
    (e : LF ≅ F.mapDerivedCategory) (f : LG ≅ G.mapDerivedCategory)
    (he : ∀ P, e.hom.app (DerivedCategory.Q.obj P) ≫
      F.mapDerivedCategoryFactors.hom.app P = ε P)
    (hf : ∀ P, f.hom.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategoryFactors.hom.app P = δ P)
    (b : F ⋙ J' ≅ J ⋙ G) (Good : CochainComplex C ℤ → Prop) :
    Functor.DerivedExchangeCounitNormalization F G J J' LF LG ε δ b.hom Good
      (Functor.whiskerRight e.hom J'.mapDerivedCategory ≫
        (Functor.mapDerivedCategorySquareIso b).hom ≫
        Functor.whiskerLeft J.mapDerivedCategory f.inv) := by
  intro P _
  have hs : (Functor.mapDerivedCategorySquareIso b).hom.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (J.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((J.mapHomologicalComplex (.up ℤ)).obj P) =
    J'.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      J'.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex b.hom (.up ℤ)).app P) := by
    dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app]
    simp only [Category.assoc]
    rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
      Functor.mapDerivedCategoryNatIso_fac,
      ← Functor.mapDerivedCategoryCompIso_hom_app_factors F J' P]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← hf]
  have hn := f.inv.naturality (J.mapDerivedCategoryFactors.hom.app P)
  simp only [Category.assoc]
  rw [← reassoc_of% hn]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hs, ← Functor.map_comp_assoc, he]

/-- A normalized exchange is invertible if the counits and the underived exchange are.
Source: cancellation and naturality on derived representatives
(blueprint: lem-cbc-completed-extension-zero-comparison). -/
private theorem derivedExchange_isIso
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    [Abelian C] [Abelian C'] [Abelian D] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory C']
    [HasDerivedCategory D] [HasDerivedCategory D']
    (F : C ⥤ C') (G : D ⥤ D') (J : C ⥤ D) (J' : C' ⥤ D')
    [F.Additive] [G.Additive] [J.Additive] [J'.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    (LF : DerivedCategory C ⥤ DerivedCategory C')
    (LG : DerivedCategory D ⥤ DerivedCategory D')
    (ε : ∀ P : CochainComplex C ℤ, LF.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : ∀ P : CochainComplex D ℤ, LG.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
    (b : F ⋙ J' ⟶ J ⋙ G) [IsIso b] (Good : CochainComplex C ℤ → Prop)
    (hε : ∀ P, IsIso (ε P)) (hδ : ∀ P, IsIso (δ P))
    (hrep : ∀ K, ∃ P, Good P ∧ Nonempty (DerivedCategory.Q.obj P ≅ K))
    (α : LF ⋙ J'.mapDerivedCategory ⟶ J.mapDerivedCategory ⋙ LG)
    (hα : Functor.DerivedExchangeCounitNormalization F G J J' LF LG ε δ b Good α) :
    IsIso α := by
  have hP (P : CochainComplex C ℤ) (hP : Good P) :
      IsIso (α.app (DerivedCategory.Q.obj P)) := by
    have := hε P
    have := hδ ((J.mapHomologicalComplex (.up ℤ)).obj P)
    have : IsIso ((NatTrans.mapHomologicalComplex b (.up ℤ)).app P) := by
      change IsIso ((NatIso.mapHomologicalComplex (asIso b) (.up ℤ)).hom.app P)
      infer_instance
    have : IsIso (α.app (DerivedCategory.Q.obj P) ≫
        LG.map (J.mapDerivedCategoryFactors.hom.app P) ≫
        δ ((J.mapHomologicalComplex (.up ℤ)).obj P)) := by
      rw [hα P hP]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (LG.map (J.mapDerivedCategoryFactors.hom.app P) ≫
        δ ((J.mapHomologicalComplex (.up ℤ)).obj P))
  have (K : DerivedCategory C) : IsIso (α.app K) := by
    obtain ⟨P, hflat, ⟨e⟩⟩ := hrep K
    have := hP P hflat
    have : IsIso ((LF ⋙ J'.mapDerivedCategory).map e.hom ≫ α.app K) := by
      rw [α.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left ((LF ⋙ J'.mapDerivedCategory).map e.hom) _
  exact NatIso.isIso_of_isIso_app _

private theorem ringAdj_second
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (e : C ≌ D) [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
    {R : Sheaf J RingCat.{t + 1}} {S : Sheaf K RingCat.{t + 1}}
    (φ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat J K).obj S) [IsIso φ]
    (ψ : S ⟶ (e.inverse.sheafPushforwardContinuous RingCat K J).obj R)
    (h : ψ.hom ≫ e.inverse.op.whiskerLeft φ.hom =
      Functor.whiskerRight (NatTrans.op e.counit) S.obj) :
    φ.hom ≫ e.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.unit) R.obj = 𝟙 R.obj := by
  apply NatTrans.ext
  funext W
  apply (cancel_mono (φ.hom.app W)).mp
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.op_app, NatTrans.id_app]
  rw [Category.id_comp]
  have hn := φ.hom.naturality (e.unit.app W.unop).op
  have hh := NatTrans.congr_app h (e.functor.op.obj W)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.op_app] at hh
  simp only [Category.assoc]
  erw [hn, ← Category.assoc (ψ.hom.app _) (φ.hom.app _) _, hh]
  change φ.hom.app W ≫ S.obj.map (e.counit.app (e.functor.obj W.unop)).op ≫
    S.obj.map (e.functor.map (e.unit.app W.unop)).op = φ.hom.app W
  rw [← S.obj.map_comp, ← op_comp]
  have ht : e.functor.map (e.unit.app W.unop) ≫
      e.counit.app (e.functor.obj W.unop) = 𝟙 _ := e.functor_unitIso_comp W.unop
  erw [ht]
  change φ.hom.app W ≫ S.obj.map (𝟙 (e.functor.op.obj W)) = φ.hom.app W
  exact (congrArg (fun k : S.obj.obj (e.functor.op.obj W) ⟶
    S.obj.obj (e.functor.op.obj W) ↦ φ.hom.app W ≫ k)
      (S.obj.map_id (e.functor.op.obj W))).trans (Category.comp_id _)

namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Positive quotients retain the finiteness in the arithmetic datum, at size t+1.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
instance cbcQuotient_finite (n : ℕ) : Finite (A ⧸ d.ideal ^ (n + 1)) :=
  d.quotientFinite n

/-- Direct-image form of the recorded completed coefficient map, without assuming
that the structure map is invertible.
Source: Tag 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompletedCoefficientDirectMap {X Y : Scheme.{t}} (g : X ⟶ Y) :
    completedReductionCoefficient Y d ⟶
      (proEtaleSheafDirectImage g CommRingCat.{t + 1}).obj
        (completedReductionCoefficient X d) :=
  ((proEtaleSheafAdjunction g CommRingCat.{t + 1}).homEquiv _ _)
    (completedCoefficientMap g d)

/-- Sectionwise direct image with the recorded completed scalar action.
Source: Tag 03D7 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompletedModuleDirectImage {X Y : Scheme.{t}} (g : X ⟶ Y) :
    pbcModules X (pbcAdicCompletion X d) ⥤ pbcModules Y (pbcAdicCompletion Y d) :=
  SheafOfModules.pushforward.{t + 1} (F := proEtaleBaseChange g)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    ⟨Functor.whiskerRight (cbcCompletedCoefficientDirectMap d g).hom
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})⟩

/-- The existing module pullback adjunction on the fixed small models. The explicit
continuity witness prevents inference from choosing an unrelated larger model.
Source: Tags 03D2, 03D7 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcModelPullbackAdjunction {X Y : Scheme.{t}} (g : X ⟶ Y) :=
  letI := proEtaleModelBaseChange_isContinuous g
  SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
    (F := proEtaleModelBaseChange g)
    (J := proEtaleModelTopology Y) (K := proEtaleModelTopology X)
    (proEtaleModelRingUnit g (pbcAdicCompletion Y d))

/-- The pullback adjunction is uniquely normalized by the model-site inverse-image
unit followed by the actual sheafified tensor section 1 tensor m.
Source: Tags 03D7, 03EK (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: use the model-site module adjunction followed by scalar extension, whose
unit is the specified pure tensor. Transport back leaves sections unchanged.
The tensor generators and sheafification determine the Hom bijection uniquely,
so the formula determines exactly one adjunction. No coefficient isomorphism is assumed. -/
theorem cbcModulePullbackAdjunction_exists {X Y : Scheme.{t}} (g : X ⟶ Y) :
    ∃! adj : completedModulePullback g d ⊣ cbcCompletedModuleDirectImage d g,
      ∀ (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt)
        (x : M.val.obj (op V)),
        (adj.unit.app M).val.app (op V) x =
          pbcTensorSection (completedCoefficientMap g d)
            ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M)
            (op ((proEtaleBaseChange g).obj V)) 1
            (((cbcModelPullbackAdjunction d g).unit.app
                ((proEtaleModuleToModel
                  (reductionModuleRing Y (pbcAdicCompletion Y d))).obj M)).val.app
                    (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj V)) x) := by
  let R := pbcAdicCompletion Y d
  let ai := proEtaleModuleInverseImageAdjunction g R
  let a := ai.comp (pbcScalarAdjunction (completedCoefficientMap g d))
  let er : (pbcRestrict (completedCoefficientMap g d) ⋙
      proEtaleRingModuleDirectImage g R
        ((proEtaleSheafInverseImage g CommRingCat.{t + 1}).obj R) (Iso.refl _)) ≅
      cbcCompletedModuleDirectImage d g := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      exact PresheafOfModules.isoMk (fun V ↦ Iso.refl _)
        (by intros; rfl)
    · intro M N f
      ext V x
      rfl
  let adj : completedModulePullback g d ⊣ cbcCompletedModuleDirectImage d g :=
    a.ofNatIsoRight er
  have hu (M : pbcModules Y R) (V : Y.ProEt) (x : M.val.obj (op V)) :
      (adj.unit.app M).val.app (op V) x =
        pbcTensorSection (completedCoefficientMap g d)
          ((proEtaleModuleInverseImage g R).obj M)
          (op ((proEtaleBaseChange g).obj V)) 1
          (((cbcModelPullbackAdjunction d g).unit.app
            ((proEtaleModuleToModel (reductionModuleRing Y R)).obj M)).val.app
              (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj V)) x) := by
    change ((pbcScalarAdjunction (completedCoefficientMap g d)).unit.app
        ((proEtaleModuleInverseImage g R).obj M)).val.app
        (op ((proEtaleBaseChange g).obj V)) ((ai.unit.app M).val.app (op V) x) = _
    refine ((pbcScalarAdjunction_exists (completedCoefficientMap g d)).exists.choose_spec
      ((proEtaleModuleInverseImage g R).obj M)
      (op ((proEtaleBaseChange g).obj V)) ((ai.unit.app M).val.app (op V) x)).trans ?_
    congr 1
    change ((proEtaleModuleInverseImage g R).obj M).val.map (𝟙 _)
      ((((cbcModelPullbackAdjunction d g).unit.app
        ((proEtaleModuleToModel (reductionModuleRing Y R)).obj M)).val.app
          (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj V)))
            (M.val.map (𝟙 _) x)) = _
    simp only [PresheafOfModules.map_id]
    rfl
  refine ⟨adj, hu, ?_⟩
  intro adj' hadj'
  apply Adjunction.ext
  ext M V x
  exact (hadj' M V.unop x).trans (hu M V.unop x).symm

/-- The tensor-unit normalized adjunction for the recorded pullback construction.
Source: Tag 03D7 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcModulePullbackAdjunction {X Y : Scheme.{t}} (g : X ⟶ Y) :=
  (cbcModulePullbackAdjunction_exists d g).exists.choose

/-- The recorded strict reduction, tower pullback and Rlim, as a composite functor.
Its object function is exactly completedPullbackObject.
Source: Tag 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
abbrev cbcCompletedPullback {X Y : Scheme.{t}} (g : X ⟶ Y) :=
  completedReductionTower Y d ⋙ completedTowerPullback g d ⋙ completedTowerRlim d X

/-- Naturality of the recorded ordinary-to-completed pullback comparison.
Source: Tag 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the constant-tower/Rlim unit, the normalized constant-pullback comparison,
and the strict quotient augmentation are natural transformations. Functoriality
of Rlim and their three naturality identities give the displayed equality. -/
theorem cbcCompletedPullbackComparison_naturality {X Y : Scheme.{t}} (g : X ⟶ Y)
    {K L : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))} (f : K ⟶ L) :
    (completedOrdinaryPullback g d).map f ≫ completedPullbackComparison g d L =
      completedPullbackComparison g d K ≫ (cbcCompletedPullback d g).map f := by
  let η : completedOrdinaryPullback g d ⟶ cbcCompletedPullback d g :=
    Functor.whiskerLeft (completedOrdinaryPullback g d) (completedConstantRlimUnit d X) ≫
      Functor.whiskerRight ((completedPullbackConstantIso g d).hom ≫
        Functor.whiskerRight (completedReductionTowerUnit d Y) (completedTowerPullback g d))
        (completedTowerRlim d X)
  exact η.naturality f

/-- The recorded completion-unit comparison with its naturality statement.
Source: Tag 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompletedPullbackComparison {X Y : Scheme.{t}} (g : X ⟶ Y) :
    completedOrdinaryPullback g d ⟶ cbcCompletedPullback d g where
  app := completedPullbackComparison g d
  naturality _ _ f := cbcCompletedPullbackComparison_naturality d g f

/-- An open immersion is weakly etale.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: an open immersion is etale, and etale morphisms are weakly etale. -/
theorem cbcOpenWeaklyEtale {U T : Scheme.{t}} (j : U ⟶ T)
    (_hj : IsOpenImmersion j) : WeaklyEtale j := by
  let := _hj
  infer_instance

/-- Forget the ambient structure map in a pro-etale slice object.
Source: Tag 0951 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcSliceFunctor (T : Scheme.{t}) (W : T.ProEt) : Over W ⥤ W.left.ProEt where
  obj V := MorphismProperty.Over.mk ⊤ V.hom.left
    ((ProEt.weaklyEtale_localization.{t, t + 1, t + 1} T W
      (CommRingCat.of (ULift.{t + 1} ℤ))).2.1 V)
  map f := MorphismProperty.Over.homMk f.left.left
    (congrArg (fun h ↦ h.left) f.w)

/-- The concrete localization functor is continuous.
Source: Tags 098K, 094T, 0951 (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the functor keeps the underlying schemes and arrows. The pro-etale covering
condition is the same finite affine fpqc covering condition on those arrows;
therefore inverse images of covering sieves cover. This is exactly the site
identification in weaklyEtale_localization, with its concrete underlying maps. -/
@[instance] theorem cbcSliceFunctor_continuous (T : Scheme.{t}) (W : T.ProEt) :
    (cbcSliceFunctor T W).IsContinuous ((ProEt.topology T).over W)
      (ProEt.topology W.left) := by
  have : (ProEt.sliceEquiv T W).symm.functor.IsCocontinuous (ProEt.topology W.left)
      ((ProEt.topology T).over W) := ProEt.sliceFrom_cocont T W
  exact (ProEt.sliceEquiv T W).symm.toAdjunction.isContinuous_of_isCocontinuous
    (ProEt.topology W.left) ((ProEt.topology T).over W)

-- These private coefficient constructions also occur in RingedOpenStrictReduction.
-- That module imports this one, so we construct them here without importing it.
private local instance sliceFunctor_cocontinuous (T : Scheme.{t}) (W : T.ProEt) :
    (cbcSliceFunctor T W).IsCocontinuous ((ProEt.topology T).over W)
      (ProEt.topology W.left) :=
  ( (ProEt.sliceEquiv T W).toAdjunction.isCocontinuous_iff_coverPreserving
    ((ProEt.topology T).over W) (ProEt.topology W.left)).mpr (ProEt.sliceFrom_cover T W)

private def finiteSliceIso {T : Scheme.{t}} (W : T.ProEt)
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (reductionCoefficient T d n).over W ≅
      ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).obj
          (reductionCoefficient W.left d n) :=
  (((Over.forget W).pushforwardContinuousSheafificationCompatibility CommRingCat.{t + 1}
    ((ProEt.topology T).over W) (ProEt.topology T)).app
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).symm ≪≫
    ((cbcSliceFunctor T W).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{t + 1} ((ProEt.topology T).over W) (ProEt.topology W.left)).app
        (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))

private theorem finiteSliceIso_unit {T : Scheme.{t}} (W : T.ProEt)
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) (V : Over W) :
    (toSheafify (ProEt.topology T)
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).app (op V.left) ≫
        (finiteSliceIso W d n).hom.hom.app (op V) =
    (toSheafify (ProEt.topology W.left)
      (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))).app
        (op ((cbcSliceFunctor T W).obj V)) := by
  have h₁ := (Over.forget W).toSheafify_pullbackSheafificationCompatibility
    CommRingCat.{t + 1} ((ProEt.topology T).over W) (ProEt.topology T)
    (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))
  have h₂ := (cbcSliceFunctor T W).toSheafify_pullbackSheafificationCompatibility
    CommRingCat.{t + 1} ((ProEt.topology T).over W) (ProEt.topology W.left)
    (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))
  have h₁' := NatTrans.congr_app h₁ (op V)
  have h₂' := NatTrans.congr_app h₂ (op V)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₁' h₂'
  dsimp only [finiteSliceIso, Iso.trans_hom, Iso.symm_hom,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  have hid := congrArg (fun f ↦ f.hom.app (op V))
    (((Over.forget W).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{t + 1} ((ProEt.topology T).over W) (ProEt.topology T)).app
        (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).hom_inv_id
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at hid
  let α := ((Over.forget W).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{t + 1} ((ProEt.topology T).over W) (ProEt.topology T)).app
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))
  let β := ((cbcSliceFunctor T W).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{t + 1} ((ProEt.topology T).over W) (ProEt.topology W.left)).app
      (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))
  calc
    _ = ((toSheafify ((ProEt.topology T).over W)
        ((Over.forget W).op ⋙
          AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).app (op V) ≫
        α.hom.hom.app (op V)) ≫ α.inv.hom.app (op V) ≫ β.hom.hom.app (op V) :=
      congrArg (fun f ↦ f ≫ α.inv.hom.app (op V) ≫ β.hom.hom.app (op V)) h₁'.symm
    _ = _ := by
      simp only [Category.assoc] at hid ⊢
      rw [← Category.assoc (α.hom.hom.app _) (α.inv.hom.app _) _, hid,
        Category.id_comp]
      exact h₂'

attribute [local irreducible] finiteSliceIso

/-- The finite ring identification in the slice is fixed by local function sections.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: localization keeps each underlying scheme, so its connected-component
functions agree literally. Their sheafification units induce this unique map.
Localization is an equivalence of sites, hence this map is an isomorphism. -/
theorem cbcFiniteSliceMap_exists (T : Scheme.{t}) (W : T.ProEt) (n : ℕ) :
    ∃! φ : ((reductionCoefficient T d n)).over W ⟶
        ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
          ((ProEt.topology T).over W) (ProEt.topology W.left)).obj
            ((reductionCoefficient W.left d n)),
      ∀ V : Over W,
        (toSheafify (ProEt.topology T)
          (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).app
            (op V.left) ≫ φ.hom.app (op V) =
        (toSheafify (ProEt.topology W.left)
          (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))).app
            (op ((cbcSliceFunctor T W).obj V)) := by
  refine ⟨(finiteSliceIso W d n).hom, finiteSliceIso_unit W d n, ?_⟩
  intro φ hφ
  apply Sheaf.hom_ext
  let α := ((Over.forget W).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{t + 1} ((ProEt.topology T).over W) (ProEt.topology T)).app
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))
  apply (cancel_epi α.hom.hom).mp
  apply sheafify_hom_ext ((ProEt.topology T).over W) _ _
    (((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
      ((ProEt.topology T).over W) (ProEt.topology W.left)).obj
        (reductionCoefficient W.left d n)).property
  have hα := (Over.forget W).toSheafify_pullbackSheafificationCompatibility
    CommRingCat.{t + 1} ((ProEt.topology T).over W) (ProEt.topology T)
    (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))
  apply NatTrans.ext
  funext V
  have hV := NatTrans.congr_app hα V
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hV
  simp only [NatTrans.comp_app, ← Category.assoc]
  exact (congrArg (fun f ↦ f ≫ φ.hom.app V) hV).trans
    (((hφ V.unop).trans (finiteSliceIso_unit W d n V.unop).symm).trans
      (congrArg (fun f ↦ f ≫ (finiteSliceIso W d n).hom.hom.app V) hV.symm))

/-- The finite slice coefficient map with the specified function normalization.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcFiniteSliceMap (T : Scheme.{t}) (W : T.ProEt) (n : ℕ) :=
  (cbcFiniteSliceMap_exists d T W n).exists.choose

private def finiteSliceSystemMap {T : Scheme.{t}} (W : T.ProEt)
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    reductionCoefficientSystem T d ⋙ (ProEt.topology T).overPullback CommRingCat.{t + 1} W ⟶
      reductionCoefficientSystem W.left d ⋙
        (cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
          ((ProEt.topology T).over W) (ProEt.topology W.left) :=
  NatTrans.ofOpSequence (fun n ↦ (finiteSliceIso W d n).hom) (by
    intro n
    simp only [Functor.comp_map, reductionCoefficientSystem,
      AdicCoefficients.ringSystem, Functor.ofOpSequence_map_homOfLE_succ,
      finiteSliceIso, Iso.trans_hom, Iso.symm_hom]
    let α := (Over.forget W).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{t + 1} ((ProEt.topology T).over W) (ProEt.topology T)
    let β := (cbcSliceFunctor T W).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{t + 1} ((ProEt.topology T).over W) (ProEt.topology W.left)
    let f := AdicCoefficients.functionPresheafMap T
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    let g := AdicCoefficients.functionPresheafMap W.left
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    have ha := α.inv.naturality f
    have hb := β.hom.naturality g
    dsimp only [Functor.comp_map] at ha hb
    change _ ≫ (α.inv.app
        (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1))) ≫
        β.hom.app (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))) =
      (α.inv.app (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1 + 1))) ≫
        β.hom.app (AdicCoefficients.functionPresheaf W.left
          (A ⧸ d.ideal ^ (n + 1 + 1)))) ≫ _
    let a₀ := α.inv.app
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))
    let a₁ := α.inv.app
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1 + 1)))
    let b₀ := β.hom.app
      (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))
    let b₁ := β.hom.app
      (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1 + 1)))
    let m := (presheafToSheaf ((ProEt.topology T).over W) CommRingCat.{t + 1}).map
      (Functor.whiskerLeft (Over.forget W).op f)
    have ha' : ((ProEt.topology T).overPullback CommRingCat.{t + 1} W).map
        (AdicCoefficients.coefficientMap T (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) ≫
        a₀ = a₁ ≫ m := ha
    have hb' : m ≫ b₀ = b₁ ≫
        ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
          ((ProEt.topology T).over W) (ProEt.topology W.left)).map
            (AdicCoefficients.coefficientMap W.left
              (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) := hb
    calc
      _ = (_ ≫ a₀) ≫ b₀ := (Category.assoc _ _ _).symm
      _ = (a₁ ≫ m) ≫ b₀ := congrArg (fun t ↦ t ≫ b₀) ha'
      _ = a₁ ≫ (m ≫ b₀) := Category.assoc _ _ _
      _ = a₁ ≫ (b₁ ≫ _) := congrArg (fun t ↦ a₁ ≫ t) hb'
      _ = _ := (Category.assoc _ _ _).symm)

private theorem finiteSliceMap_eq {T : Scheme.{t}} (W : T.ProEt)
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    cbcFiniteSliceMap d T W n = (finiteSliceIso W d n).hom :=
  (cbcFiniteSliceMap_exists d T W n).unique
    (cbcFiniteSliceMap_exists d T W n).exists.choose_spec (finiteSliceIso_unit W d n)

private local instance overRing_limits {T : Scheme.{t}} (W : T.ProEt) :
    PreservesLimitsOfShape ℕᵒᵖ ((ProEt.topology T).overPullback CommRingCat.{t + 1} W) := by
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf ((ProEt.topology T).over W) CommRingCat.{t + 1})

private local instance sliceRing_limits {T : Scheme.{t}} (W : T.ProEt) :
    PreservesLimitsOfShape ℕᵒᵖ
      ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)) := by
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf ((ProEt.topology T).over W) CommRingCat.{t + 1})

private def completedSliceIso {T : Scheme.{t}} (W : T.ProEt)
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (completedReductionCoefficient T d).over W ≅
      ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).obj
          (completedReductionCoefficient W.left d) :=
  letI (n : ℕᵒᵖ) : IsIso ((finiteSliceSystemMap W d).app n) := by
    change IsIso (finiteSliceIso W d n.unop).hom
    infer_instance
  letI : IsIso (finiteSliceSystemMap W d) := NatIso.isIso_of_isIso_app _
  preservesLimitIso ((ProEt.topology T).overPullback CommRingCat.{t + 1} W)
      (reductionCoefficientSystem T d) ≪≫
    lim.mapIso (asIso (finiteSliceSystemMap W d)) ≪≫
    (preservesLimitIso ((cbcSliceFunctor T W).sheafPushforwardContinuous
      CommRingCat.{t + 1} ((ProEt.topology T).over W) (ProEt.topology W.left))
        (reductionCoefficientSystem W.left d)).symm

private theorem completedSliceIso_projection {T : Scheme.{t}} (W : T.ProEt)
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (completedSliceIso W d).hom ≫
      ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).map
          (completedReductionProjection W.left d n) =
    ((ProEt.topology T).overPullback CommRingCat.{t + 1} W).map
        (completedReductionProjection T d n) ≫ cbcFiniteSliceMap d T W n := by
  simp only [completedSliceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    completedReductionProjection, preservesLimitIso_inv_π, lim_map, limMap_π,
    Functor.mapIso_hom, asIso_hom, finiteSliceMap_eq]
  rw [← Category.assoc, preservesLimitIso_hom_π]
  rfl

/-- The completed coefficient identification is fixed by every finite projection.
Source: Tags 098K, 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: localization commutes with limits since it keeps sections. The finite maps
commute with quotient maps since they identify the same functions. Take their
inverse limit; joint monicity of its projections proves uniqueness. -/
theorem cbcCompletedSliceMap_exists (T : Scheme.{t}) (W : T.ProEt) :
    ∃! φ : ((completedReductionCoefficient T d)).over W ⟶
        ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
          ((ProEt.topology T).over W) (ProEt.topology W.left)).obj
            ((completedReductionCoefficient W.left d)),
      ∀ n : ℕ, φ ≫
        ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
          ((ProEt.topology T).over W) (ProEt.topology W.left)).map
            ((completedReductionProjection W.left d n)) =
        ((ProEt.topology T).overPullback CommRingCat.{t + 1} W).map
          ((completedReductionProjection T d n)) ≫ cbcFiniteSliceMap d T W n := by
  refine ⟨(completedSliceIso W d).hom, completedSliceIso_projection W d, ?_⟩
  intro φ hφ
  apply (isLimitOfPreserves
    ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
      ((ProEt.topology T).over W) (ProEt.topology W.left))
    (limit.isLimit (reductionCoefficientSystem W.left d))).hom_ext
  intro n
  exact (hφ n.unop).trans (completedSliceIso_projection W d n.unop).symm

/-- The completed ring map identifying the ringed slice site.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompletedSliceMap (T : Scheme.{t}) (W : T.ProEt) :=
  (cbcCompletedSliceMap_exists d T W).exists.choose

/-- A module over the open's completed ring, viewed on the ambient ringed slice.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcModuleToSlice (T : Scheme.{t}) (W : T.ProEt) :
    (pbcModules W.left (pbcAdicCompletion W.left d)) ⥤ SheafOfModules.{t + 1}
      ((reductionModuleRing T (completedReductionCoefficient T d)).over W) :=
  SheafOfModules.pushforward.{t + 1} (F := cbcSliceFunctor T W)
    (J := (ProEt.topology T).over W) (K := ProEt.topology W.left)
    ((sheafCompose ((ProEt.topology T).over W) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      (cbcCompletedSliceMap d T W))

/-- The pro-etale object supplied by an open immersion.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOpenObject {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j) : T.ProEt :=
  letI := hj
  MorphismProperty.Over.mk ⊤ j (inferInstance : WeaklyEtale j)

/-- Extension by zero is the recorded module direct-sum presheaf, then sheafification.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOpenShriek {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (pbcModules U (pbcAdicCompletion U d)) ⥤ (pbcModules T (pbcAdicCompletion T d)) :=
  cbcModuleToSlice d T (cbcOpenObject j hj) ⋙
    SheafOfModules.extensionByZeroPresheaf.{t + 1}
      (reductionModuleRing T (completedReductionCoefficient T d)) (cbcOpenObject j hj) ⋙
    PresheafOfModules.sheafification.{t + 1}
      (𝟙 (reductionModuleRing T (completedReductionCoefficient T d)).obj)

/-- Extension by zero is additive.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the slice transport keeps addition of maps; direct sums and module
sheafification are additive. Their composite is therefore additive. -/
@[instance] theorem cbcOpenShriek_additive {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) : (cbcOpenShriek d j hj).Additive := by
  have : (cbcModuleToSlice d T (cbcOpenObject j hj)).Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  change (cbcModuleToSlice d T (cbcOpenObject j hj) ⋙
    SheafOfModules.localizedSystemExtension.{t + 1, t, t + 1}
      (completedReductionCoefficient T d) (cbcOpenObject j hj)).Additive
  infer_instance

/-- Extension by zero is exact, without any quasi-compactness assumption.
Source: Tag 03DJ (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: restriction to a slice is exact and its direct-sum/sheafification left
adjoint is exact. Ringed slice transport is an equivalence. The argument is
unchanged at distinct site object and Hom universes; equivalently transport to
AsSmall at t+1, apply the recorded localization theorem, and transport back. -/
@[instance] theorem cbcOpenShriek_finiteLimits {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) : PreservesFiniteLimits (cbcOpenShriek d j hj) := by
  have : (cbcSliceFunctor T (cbcOpenObject j hj)).IsContinuous
      ((ProEt.topology T).over (cbcOpenObject j hj)) (ProEt.topology U) :=
    cbcSliceFunctor_continuous T (cbcOpenObject j hj)
  let F := cbcModuleToSlice d T (cbcOpenObject j hj)
  let G := SheafOfModules.toSheaf
    ((reductionModuleRing T (completedReductionCoefficient T d)).over (cbcOpenObject j hj))
  have : PreservesFiniteLimits (F ⋙ G) := by
    change PreservesFiniteLimits
      (SheafOfModules.toSheaf (reductionModuleRing U (completedReductionCoefficient U d)) ⋙
        (cbcSliceFunctor T (cbcOpenObject j hj)).sheafPushforwardContinuous
          AddCommGrpCat.{t + 1} ((ProEt.topology T).over (cbcOpenObject j hj))
            (ProEt.topology U))
    infer_instance
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F G
  change PreservesFiniteLimits (F ⋙
    SheafOfModules.localizedSystemExtension.{t + 1, t, t + 1}
      (completedReductionCoefficient T d) (cbcOpenObject j hj))
  infer_instance

/-- Extension by zero preserves finite colimits.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: it is left adjoint to restriction, via the direct-sum Hom bijection and
sheafification. Hence it preserves colimits, in particular finite colimits. -/
@[instance] theorem cbcOpenShriek_finiteColimits {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) : PreservesFiniteColimits (cbcOpenShriek d j hj) := by
  have h : cbcCompletedSliceMap d T (cbcOpenObject j hj) =
      (completedSliceIso (cbcOpenObject j hj) d).hom :=
    (cbcCompletedSliceMap_exists d T (cbcOpenObject j hj)).unique
      (cbcCompletedSliceMap_exists d T (cbcOpenObject j hj)).exists.choose_spec
      (completedSliceIso_projection (cbcOpenObject j hj) d)
  have : IsIso (cbcCompletedSliceMap d T (cbcOpenObject j hj)) := by
    rw [h]
    infer_instance
  have : (cbcSliceFunctor T (cbcOpenObject j hj)).IsEquivalence :=
    inferInstanceAs (ProEt.sliceEquiv T (cbcOpenObject j hj)).functor.IsEquivalence
  let F := cbcModuleToSlice d T (cbcOpenObject j hj)
  have : F.IsLeftAdjoint := by
    dsimp only [F, cbcModuleToSlice]
    infer_instance
  have : PreservesFiniteColimits F := inferInstance
  change PreservesFiniteColimits (F ⋙
    SheafOfModules.localizedSystemExtension.{t + 1, t, t + 1}
      (completedReductionCoefficient T d) (cbcOpenObject j hj))
  infer_instance

/-- The exact extension functor applied termwise and descended to the derived category.
Source: Tag 03DJ (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDerivedOpenShriek {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j) :
    DerivedCategory (pbcModules U (pbcAdicCompletion U d)) ⥤
      DerivedCategory (pbcModules T (pbcAdicCompletion T d)) :=
  (cbcOpenShriek d j hj).mapDerivedCategory

/-- Composition of a pro-etale arrow with the open immersion.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOpenSiteFunctor {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j) :
    U.ProEt ⥤ T.ProEt :=
  letI := hj
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)

/-- Open-site composition is continuous.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: its maps are unchanged scheme arrows and hence preserve the finite-affine
fpqc covering condition. This is the inverse side of slice-site localization. -/
@[instance] theorem cbcOpenSiteFunctor_continuous {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (cbcOpenSiteFunctor j hj).IsContinuous (ProEt.topology U) (ProEt.topology T) := by
  let := hj
  exact ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)

/-- The finite restriction coefficient map identifies the very same local functions.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the composition functor keeps the underlying scheme. Sheafify the identity
on functions on connected components. Localization commutes with sheafification;
the sheafification unit determines the resulting map uniquely. -/
theorem cbcFiniteRestrictionMap_exists {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) (n : ℕ) :
    ∃! φ : (reductionCoefficient U d n) ⟶
        ((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
          (ProEt.topology U) (ProEt.topology T)).obj ((reductionCoefficient T d n)),
      ∀ V : U.ProEtᵒᵖ,
        (toSheafify (ProEt.topology U)
          (AdicCoefficients.functionPresheaf U (A ⧸ d.ideal ^ (n + 1)))).app V ≫
            φ.hom.app V =
        (toSheafify (ProEt.topology T)
          (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).app
            ((cbcOpenSiteFunctor j hj).op.obj V) := by
  let := hj
  have : (cbcOpenSiteFunctor j hj).IsCocontinuous (ProEt.topology U)
      (ProEt.topology T) := ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  let e := ((cbcOpenSiteFunctor j hj).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{t + 1} (ProEt.topology U) (ProEt.topology T)).app
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))
  have he := (cbcOpenSiteFunctor j hj).toSheafify_pullbackSheafificationCompatibility
    CommRingCat.{t + 1} (ProEt.topology U) (ProEt.topology T)
    (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))
  refine ⟨e.hom, ?_, ?_⟩
  · intro V
    exact NatTrans.congr_app he V
  · intro φ hφ
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (ProEt.topology U) _ _
      (((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)).obj (reductionCoefficient T d n)).property
    apply NatTrans.ext
    funext V
    exact (hφ V).trans (NatTrans.congr_app he V).symm

/-- The finite restriction map fixed by local functions.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcFiniteRestrictionMap {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) (n : ℕ) :=
  (cbcFiniteRestrictionMap_exists d j hj n).exists.choose

private local instance openSiteFunctor_cocontinuous {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (cbcOpenSiteFunctor j hj).IsCocontinuous (ProEt.topology U) (ProEt.topology T) :=
  ProEt.isCocontinuous_overMap (cbcOpenWeaklyEtale j hj)

private def finiteRestrictionIso {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) (n : ℕ) :
    reductionCoefficient U d n ≅
      ((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)).obj (reductionCoefficient T d n) :=
  ((cbcOpenSiteFunctor j hj).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{t + 1} (ProEt.topology U) (ProEt.topology T)).app
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))

private theorem finiteRestrictionIso_unit {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) (n : ℕ) :
    toSheafify (ProEt.topology U)
        (AdicCoefficients.functionPresheaf U (A ⧸ d.ideal ^ (n + 1))) ≫
      (finiteRestrictionIso d j hj n).hom.hom =
    Functor.whiskerLeft (cbcOpenSiteFunctor j hj).op
      (toSheafify (ProEt.topology T)
        (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))) :=
  (cbcOpenSiteFunctor j hj).toSheafify_pullbackSheafificationCompatibility
    CommRingCat.{t + 1} (ProEt.topology U) (ProEt.topology T)
    (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))

private theorem finiteRestrictionMap_eq {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) (n : ℕ) :
    cbcFiniteRestrictionMap d j hj n = (finiteRestrictionIso d j hj n).hom :=
  (cbcFiniteRestrictionMap_exists d j hj n).unique
    (cbcFiniteRestrictionMap_exists d j hj n).exists.choose_spec
    (fun V ↦ NatTrans.congr_app (finiteRestrictionIso_unit d j hj n) V)

private def finiteRestrictionSystemMap {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    reductionCoefficientSystem U d ⟶ reductionCoefficientSystem T d ⋙
      (cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T) :=
  NatTrans.ofOpSequence (fun n ↦ (finiteRestrictionIso d j hj n).hom) (by
    intro n
    simp only [Functor.comp_map, reductionCoefficientSystem, AdicCoefficients.ringSystem,
      Functor.ofOpSequence_map_homOfLE_succ, finiteRestrictionIso]
    exact ((cbcOpenSiteFunctor j hj).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{t + 1} (ProEt.topology U) (ProEt.topology T)).hom.naturality
        (AdicCoefficients.functionPresheafMap T
          (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))

private local instance openRing_limits {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    PreservesLimitsOfShape ℕᵒᵖ
      ((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)) := by
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (ProEt.topology U) CommRingCat.{t + 1})

private def completedRestrictionIso {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    completedReductionCoefficient U d ≅
      ((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)).obj (completedReductionCoefficient T d) :=
  have (n : ℕᵒᵖ) : IsIso ((finiteRestrictionSystemMap d j hj).app n) :=
    inferInstanceAs (IsIso (finiteRestrictionIso d j hj n.unop).hom)
  have : IsIso (finiteRestrictionSystemMap d j hj) := NatIso.isIso_of_isIso_app _
  lim.mapIso (asIso (finiteRestrictionSystemMap d j hj)) ≪≫
    (preservesLimitIso ((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous
      CommRingCat.{t + 1} (ProEt.topology U) (ProEt.topology T))
        (reductionCoefficientSystem T d)).symm

private theorem completedRestrictionIso_projection {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) (n : ℕ) :
    (completedRestrictionIso d j hj).hom ≫
      ((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)).map (completedReductionProjection T d n) =
    completedReductionProjection U d n ≫ cbcFiniteRestrictionMap d j hj n := by
  simp only [completedRestrictionIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    completedReductionProjection, preservesLimitIso_inv_π, lim_map, limMap_π,
    Functor.mapIso_hom, asIso_hom, finiteRestrictionMap_eq]
  rfl

/-- The completed restriction map is fixed by its finite projections.
Source: Tags 098K, 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: restriction computes sections and commutes with limits. The finite maps
are compatible with every quotient transition, so their limit is the uniquely
specified map. This is an isomorphism because all finite slice maps are. -/
theorem cbcCompletedRestrictionMap_exists {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    ∃! φ : (completedReductionCoefficient U d) ⟶
        ((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
          (ProEt.topology U) (ProEt.topology T)).obj ((completedReductionCoefficient T d)),
      ∀ n : ℕ, φ ≫
        ((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
          (ProEt.topology U) (ProEt.topology T)).map ((completedReductionProjection T d n)) =
        (completedReductionProjection U d n) ≫ cbcFiniteRestrictionMap d j hj n := by
  refine ⟨(completedRestrictionIso d j hj).hom,
    completedRestrictionIso_projection d j hj, ?_⟩
  intro φ hφ
  apply (isLimitOfPreserves
    ((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
      (ProEt.topology U) (ProEt.topology T))
    (limit.isLimit (reductionCoefficientSystem T d))).hom_ext
  intro n
  exact (hφ n.unop).trans (completedRestrictionIso_projection d j hj n.unop).symm

/-- The canonical inverse of the open's completed coefficient identification.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompletedRestrictionMap {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :=
  (cbcCompletedRestrictionMap_exists d j hj).exists.choose

/-- Actual restriction of completed-ring modules to the open pro-etale site.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOpenRestriction {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (pbcModules T (pbcAdicCompletion T d)) ⥤ (pbcModules U (pbcAdicCompletion U d)) :=
  SheafOfModules.pushforward.{t + 1} (F := cbcOpenSiteFunctor j hj)
    (J := ProEt.topology U) (K := ProEt.topology T)
    ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      (cbcCompletedRestrictionMap d j hj))

/-- The slice object corresponding to a pro-etale object of the open.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOpenSliceObject {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j)
    (V : U.ProEt) : Over (cbcOpenObject j hj) :=
  Over.mk (@id ((cbcOpenSiteFunctor j hj).obj V ⟶ cbcOpenObject j hj)
    (MorphismProperty.Over.homMk V.hom rfl))

private theorem finiteOpenSlice_inverse {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) (n : ℕ) :
    (cbcFiniteRestrictionMap d j hj n).hom ≫
      Functor.whiskerLeft (ProEt.sliceFrom T (cbcOpenObject j hj)).op
        (cbcFiniteSliceMap d T (cbcOpenObject j hj) n).hom =
      𝟙 (reductionCoefficient U d n).obj := by
  apply sheafify_hom_ext (ProEt.topology U) _ _ (reductionCoefficient U d n).property
  apply NatTrans.ext
  funext V
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app,
    ← Category.assoc]
  erw [(cbcFiniteRestrictionMap_exists d j hj n).exists.choose_spec V]
  have h := (cbcFiniteSliceMap_exists d T (cbcOpenObject j hj) n).exists.choose_spec
    (cbcOpenSliceObject j hj V.unop)
  change _ ≫ (cbcFiniteSliceMap d T (cbcOpenObject j hj) n).hom.app
    ((ProEt.sliceFrom T (cbcOpenObject j hj)).op.obj V) = _ at h
  exact h.trans (Category.comp_id _).symm

private theorem completedOpenSlice_inverse {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (cbcCompletedRestrictionMap d j hj).hom ≫
      Functor.whiskerLeft (ProEt.sliceFrom T (cbcOpenObject j hj)).op
        (cbcCompletedSliceMap d T (cbcOpenObject j hj)).hom =
      𝟙 (completedReductionCoefficient U d).obj := by
  apply NatTrans.ext
  funext V
  let ev := sheafToPresheaf (ProEt.topology U) CommRingCat.{t + 1} ⋙
    (CategoryTheory.evaluation U.ProEtᵒᵖ CommRingCat.{t + 1}).obj V
  apply (isLimitOfPreserves ev (limit.isLimit (reductionCoefficientSystem U d))).hom_ext
  intro n
  have hb := congrArg (fun f ↦ f.hom.app V)
    ((cbcCompletedRestrictionMap_exists d j hj).exists.choose_spec n.unop)
  have hc := congrArg (fun f ↦ f.hom.app (op (cbcOpenSliceObject j hj V.unop)))
    ((cbcCompletedSliceMap_exists d T (cbcOpenObject j hj)).exists.choose_spec n.unop)
  have hi := NatTrans.congr_app (finiteOpenSlice_inverse d j hj n.unop) V
  change (cbcCompletedRestrictionMap d j hj).hom.app V ≫
      (cbcCompletedSliceMap d T (cbcOpenObject j hj)).hom.app
        (op (cbcOpenSliceObject j hj V.unop)) ≫
          (completedReductionProjection U d n.unop).hom.app V =
      (completedReductionProjection U d n.unop).hom.app V
  change (cbcCompletedRestrictionMap d j hj).hom.app V ≫
      (completedReductionProjection T d n.unop).hom.app
        (op ((cbcOpenSiteFunctor j hj).obj V.unop)) =
    (completedReductionProjection U d n.unop).hom.app V ≫
      (cbcFiniteRestrictionMap d j hj n.unop).hom.app V at hb
  change (cbcCompletedSliceMap d T (cbcOpenObject j hj)).hom.app
        (op (cbcOpenSliceObject j hj V.unop)) ≫
      (completedReductionProjection U d n.unop).hom.app V =
    (completedReductionProjection T d n.unop).hom.app
        (op ((cbcOpenSiteFunctor j hj).obj V.unop)) ≫
      (cbcFiniteSliceMap d T (cbcOpenObject j hj) n.unop).hom.app
        (op (cbcOpenSliceObject j hj V.unop)) at hc
  change (cbcFiniteRestrictionMap d j hj n.unop).hom.app V ≫
      (cbcFiniteSliceMap d T (cbcOpenObject j hj) n.unop).hom.app
        (op (cbcOpenSliceObject j hj V.unop)) = 𝟙 _ at hi
  rw [hc, ← Category.assoc, hb, Category.assoc, hi, Category.comp_id]

private local instance openSliceFrom_continuous {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (ProEt.sliceFrom T (cbcOpenObject j hj)).IsContinuous (ProEt.topology U)
      ((ProEt.topology T).over (cbcOpenObject j hj)) := by
  have : (ProEt.sliceEquiv T (cbcOpenObject j hj)).functor.IsCocontinuous
      ((ProEt.topology T).over (cbcOpenObject j hj)) (ProEt.topology U) :=
    sliceFunctor_cocontinuous T (cbcOpenObject j hj)
  exact (ProEt.sliceEquiv T (cbcOpenObject j hj)).toAdjunction.isContinuous_of_isCocontinuous _ _

private def openSliceAdjunction {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    letI := openSliceFrom_continuous j hj
    cbcModuleToSlice d T (cbcOpenObject j hj) ⊣
      SheafOfModules.pushforward.{t + 1}
        (F := ProEt.sliceFrom T (cbcOpenObject j hj))
        (J := ProEt.topology U) (K := (ProEt.topology T).over (cbcOpenObject j hj))
        ((sheafCompose _ (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
          (cbcCompletedRestrictionMap d j hj)) := by
  letI := openSliceFrom_continuous j hj
  let W := cbcOpenObject j hj
  let e := ProEt.sliceEquiv T W
  let S := reductionModuleRing T (completedReductionCoefficient T d)
  let R := reductionModuleRing U (completedReductionCoefficient U d)
  have : e.functor.IsContinuous ((ProEt.topology T).over W) (ProEt.topology U) :=
    cbcSliceFunctor_continuous T W
  have : e.functor.IsCocontinuous ((ProEt.topology T).over W) (ProEt.topology U) :=
    sliceFunctor_cocontinuous T W
  let φ : S.over W ⟶ (e.functor.sheafPushforwardContinuous RingCat.{t + 1}
      ((ProEt.topology T).over W) (ProEt.topology U)).obj R :=
    (sheafCompose _ (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      (cbcCompletedSliceMap d T W)
  have : e.inverse.IsContinuous (ProEt.topology U) ((ProEt.topology T).over W) :=
    e.toAdjunction.isContinuous_of_isCocontinuous _ _
  let ψ : R ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{t + 1}
      (ProEt.topology U) ((ProEt.topology T).over W)).obj (S.over W) :=
    (sheafCompose _ (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      (cbcCompletedRestrictionMap d j hj)
  have H₁ : Functor.whiskerRight (NatTrans.op e.counit) R.obj =
      ψ.hom ≫ e.inverse.op.whiskerLeft φ.hom := by
    have h := completedOpenSlice_inverse d j hj
    ext V : 2
    change R.obj.map (𝟙 _) = _
    rw [R.obj.map_id]
    exact congrArg (fun f ↦ (forget₂ CommRingCat RingCat).map (f.app V)) h.symm
  have hφ : IsIso φ := by
    have he : cbcCompletedSliceMap d T W = (completedSliceIso W d).hom :=
      (cbcCompletedSliceMap_exists d T W).unique
        (cbcCompletedSliceMap_exists d T W).exists.choose_spec
        (completedSliceIso_projection W d)
    dsimp only [φ]
    rw [he]
    infer_instance
  have H₂ : φ.hom ≫ e.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.unit) (S.over W).obj = 𝟙 (S.over W).obj := by
    exact ringAdj_second e φ ψ H₁.symm
  exact SheafOfModules.pushforwardPushforwardAdj e.toAdjunction φ ψ H₁ H₂

private theorem compAdjunction_homEquiv_apply
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
    (a : F ⊣ G) (b : H ⊣ I) (X : C) (Y : E) (f : (F ⋙ H).obj X ⟶ Y) :
    (a.comp b).homEquiv X Y f = a.homEquiv X (I.obj Y) (b.homEquiv (F.obj X) Y f) :=
  congrArg (fun e ↦ e X Y f) (Adjunction.comp_homEquiv a b)

open Classical in
private theorem extensionSheafAdjunction_homEquiv_apply
    {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{t + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
    (R : Sheaf J RingCat.{t + 1}) (W : C)
    (M : SheafOfModules.{t + 1} (R.over W)) (N : SheafOfModules.{t + 1} R)
    (f : (SheafOfModules.extensionByZeroPresheaf R W ⋙
      PresheafOfModules.sheafification (𝟙 R.obj)).obj M ⟶ N)
    (V : Over W) (x : M.val.obj (op V)) :
    (((SheafOfModules.extensionSheafAdjunction.{t + 1, t, t + 1} R W).homEquiv M N)
      f).val.app (op V) x =
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) f).app (op V.left)
        (DirectSum.of _ V.hom x) := by
  rw [SheafOfModules.extensionSheafAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

private theorem openSliceAdjunction_homEquiv_apply {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j)
    (M : pbcModules U (pbcAdicCompletion U d))
    (N : SheafOfModules.{t + 1}
      ((reductionModuleRing T (completedReductionCoefficient T d)).over (cbcOpenObject j hj)))
    (f : (cbcModuleToSlice d T (cbcOpenObject j hj)).obj M ⟶ N)
    (V : U.ProEt) (x : M.val.obj (op V)) :
    (((openSliceAdjunction d j hj).homEquiv M N) f).val.app (op V) x =
      f.val.app (op (cbcOpenSliceObject j hj V)) x := by
  change f.val.app (op (cbcOpenSliceObject j hj V)) (M.val.map (𝟙 (op V)) x) = _
  rw [PresheafOfModules.map_id]
  rfl

open Classical in
/-- The extension/restriction adjunction is fixed by the direct-sum generator formula.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the sheafification Hom equivalence identifies a map out of j!M with a
presheaf map out of its direct sum. Restricting this map to the summand indexed
by the structure arrow V to U gives exactly the displayed formula. Conversely,
apply a restriction map to each such summand and use the direct-sum universal
property. These operations are inverse, natural, and linear by the coefficient
identifications. The formula fixes the Hom equivalence, hence the adjunction. -/
theorem cbcOpenAdjunction_exists {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    ∃! adj : cbcOpenShriek d j hj ⊣ cbcOpenRestriction d j hj,
      ∀ (M : (pbcModules U (pbcAdicCompletion U d))) (N : (pbcModules T (pbcAdicCompletion T d)))
        (α : (cbcOpenShriek d j hj).obj M ⟶ N) (V : U.ProEt)
        (x : M.val.obj (op V)),
        ((adj.homEquiv M N) α).val.app (op V) x =
          (PresheafOfModules.sheafificationHomEquiv.{t + 1}
            (𝟙 (reductionModuleRing T (completedReductionCoefficient T d)).obj) α).app
            (op ((cbcOpenSiteFunctor j hj).obj V))
              (DirectSum.of _ (cbcOpenSliceObject j hj V).hom x) := by
  let S := reductionModuleRing T (completedReductionCoefficient T d)
  let W := cbcOpenObject j hj
  have : (ProEt.sliceFrom T W).IsContinuous (ProEt.topology U)
      ((ProEt.topology T).over W) := openSliceFrom_continuous j hj
  let a :=
    (openSliceAdjunction d j hj).comp
      (SheafOfModules.extensionSheafAdjunction.{t + 1, t, t + 1} S W)
  -- Compare restriction on sections to avoid unfolding the whole composite functor.
  let er : (SheafOfModules.overFunctor S W ⋙
      SheafOfModules.pushforward.{t + 1}
        (F := ProEt.sliceFrom T W)
        (J := ProEt.topology U) (K := (ProEt.topology T).over W)
        ((sheafCompose _ (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
          (cbcCompletedRestrictionMap d j hj))) ≅ cbcOpenRestriction d j hj := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      exact PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by intros; rfl)
    · intro M N f
      ext V x
      rfl
  let adj : cbcOpenShriek d j hj ⊣ cbcOpenRestriction d j hj := a.ofNatIsoRight er
  have hu (M : pbcModules U (pbcAdicCompletion U d))
      (N : pbcModules T (pbcAdicCompletion T d))
      (α : (cbcOpenShriek d j hj).obj M ⟶ N) (V : U.ProEt)
      (x : M.val.obj (op V)) :
      ((adj.homEquiv M N) α).val.app (op V) x =
        (PresheafOfModules.sheafificationHomEquiv.{t + 1} (𝟙 S.obj) α).app
          (op ((cbcOpenSiteFunctor j hj).obj V))
            (DirectSum.of _ (cbcOpenSliceObject j hj V).hom x) := by
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change ((a.homEquiv M N) α).val.app (op V) x = _
    rw [compAdjunction_homEquiv_apply]
    exact (openSliceAdjunction_homEquiv_apply d j hj M
      ((SheafOfModules.overFunctor S W).obj N)
      ((SheafOfModules.extensionSheafAdjunction.{t + 1, t, t + 1} S W).homEquiv _ N α)
        V x).trans
        (extensionSheafAdjunction_homEquiv_apply S W _ N α (cbcOpenSliceObject j hj V) x)
  refine ⟨adj, hu, ?_⟩
  intro adj' hadj'
  apply Adjunction.ext
  ext M V x
  have h := hadj' M ((cbcOpenShriek d j hj).obj M) (𝟙 _) V.unop x
  have h' := hu M ((cbcOpenShriek d j hj).obj M) (𝟙 _) V.unop x
  rw [Adjunction.homEquiv_id] at h h'
  exact h.trans h'.symm

/-- The generator-normalized extension/restriction adjunction.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOpenAdjunction {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j) :=
  (cbcOpenAdjunction_exists d j hj).exists.choose

private def rightPushforwardTrans
    {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F G : C ⥤ D} [F.IsContinuous J K] [G.IsContinuous J K]
    {R : Sheaf J RingCat.{t + 1}} {S : Sheaf K RingCat.{t + 1}}
    (φ : R ⟶ (G.sheafPushforwardContinuous RingCat J K).obj S)
    (ψ : R ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S)
    (α : F ⟶ G)
    (h : φ ≫ (Functor.sheafPushforwardContinuousNatTrans α _ _ _).app S = ψ) :
    SheafOfModules.pushforward.{t + 1} (F := G) φ ⟶
      SheafOfModules.pushforward.{t + 1} (F := F) ψ :=
  SheafOfModules.pushforwardNatTrans φ α ≫ (SheafOfModules.pushforwardCongr h).hom

private def rightCompositePushforward
    {C D E D' : Type*} [Category C] [Category D] [Category E] [Category D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : GrothendieckTopology E} {K' : GrothendieckTopology D'}
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ D'} {I : D' ⥤ E}
    [F.IsContinuous J K] [G.IsContinuous K L]
    [H.IsContinuous J K'] [I.IsContinuous K' L]
    [(F ⋙ G).IsContinuous J L] [(H ⋙ I).IsContinuous J L]
    {R : Sheaf J RingCat.{t + 1}} {S : Sheaf K RingCat.{t + 1}}
    {T : Sheaf L RingCat.{t + 1}} {S' : Sheaf K' RingCat.{t + 1}}
    (φ : R ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S)
    (ψ : S ⟶ (G.sheafPushforwardContinuous RingCat K L).obj T)
    (φ' : R ⟶ (H.sheafPushforwardContinuous RingCat J K').obj S')
    (ψ' : S' ⟶ (I.sheafPushforwardContinuous RingCat K' L).obj T)
    (α : H ⋙ I ⟶ F ⋙ G)
    (h : (φ ≫ (F.sheafPushforwardContinuous RingCat J K).map ψ) ≫
      (Functor.sheafPushforwardContinuousNatTrans α _ _ _).app T =
        φ' ≫ (H.sheafPushforwardContinuous RingCat J K').map ψ') :
    SheafOfModules.pushforward.{t + 1} ψ ⋙ SheafOfModules.pushforward.{t + 1} φ ⟶
      SheafOfModules.pushforward.{t + 1} ψ' ⋙ SheafOfModules.pushforward.{t + 1} φ' :=
  (SheafOfModules.pushforwardComp φ ψ).hom ≫
    rightPushforwardTrans _ _ α h ≫ (SheafOfModules.pushforwardComp φ' ψ').inv

private theorem rightCompositePushforward_apply
    {C D E D' : Type*} [Category C] [Category D] [Category E] [Category D']
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : GrothendieckTopology E} {K' : GrothendieckTopology D'}
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ D'} {I : D' ⥤ E}
    [F.IsContinuous J K] [G.IsContinuous K L]
    [H.IsContinuous J K'] [I.IsContinuous K' L]
    [(F ⋙ G).IsContinuous J L] [(H ⋙ I).IsContinuous J L]
    {R : Sheaf J RingCat.{t + 1}} {S : Sheaf K RingCat.{t + 1}}
    {T : Sheaf L RingCat.{t + 1}} {S' : Sheaf K' RingCat.{t + 1}}
    (φ : R ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S)
    (ψ : S ⟶ (G.sheafPushforwardContinuous RingCat K L).obj T)
    (φ' : R ⟶ (H.sheafPushforwardContinuous RingCat J K').obj S')
    (ψ' : S' ⟶ (I.sheafPushforwardContinuous RingCat K' L).obj T)
    (α : H ⋙ I ⟶ F ⋙ G)
    (h : (φ ≫ (F.sheafPushforwardContinuous RingCat J K).map ψ) ≫
      (Functor.sheafPushforwardContinuousNatTrans α _ _ _).app T =
        φ' ≫ (H.sheafPushforwardContinuous RingCat J K').map ψ')
    (M : SheafOfModules.{t + 1} T) (V : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward ψ ⋙ SheafOfModules.pushforward φ).obj M).val.obj V) :
    ((rightCompositePushforward φ ψ φ' ψ' α h).app M).val.app V x =
      M.val.map (α.app V.unop).op x := rfl

private abbrev rightFiniteRing (n : ℕ) : CommRingCat.{t + 1} :=
  CommRingCat.of (A ⧸ d.ideal ^ (n + 1))
private def rightFiniteProjection (T : Scheme.{t}) (n : ℕ) :=
  pbcAdicProjection T d n ≫ (pbcLevelConstantComparison T d n).inv

private theorem rightFiniteProjection_pullback {S T : Scheme.{t}} (f : S ⟶ T) (n : ℕ) :
    completedCoefficientMap f d ≫ rightFiniteProjection d S n =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map
        (rightFiniteProjection d T n) ≫
          proEtaleConstantInverseImageMap f CommRingCat.{t + 1} (rightFiniteRing d n) := by
  unfold rightFiniteProjection
  rw [← Category.assoc]
  have h : completedCoefficientMap f d ≫ pbcAdicProjection S d n =
      completedCoefficientComponent f d n := limit.lift_π _ (op n)
  rw [h]
  simp only [completedCoefficientComponent, completedFiniteCoefficientMap,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem rightFiniteProjection_direct {S T : Scheme.{t}} (f : S ⟶ T) (n : ℕ) :
    rightFiniteProjection d T n ≫
        proEtaleConstantDirectImageMap f CommRingCat.{t + 1} (rightFiniteRing d n) =
      cbcCompletedCoefficientDirectMap d f ≫
        (proEtaleSheafDirectImage f CommRingCat.{t + 1}).map
          (rightFiniteProjection d S n) := by
  have he : proEtaleConstantDirectImageMap f CommRingCat.{t + 1} (rightFiniteRing d n) =
      (proEtaleSheafAdjunction f CommRingCat.{t + 1}).homEquiv _ _
        (proEtaleConstantInverseImageMap f CommRingCat.{t + 1} (rightFiniteRing d n)) := by
    exact (Equiv.apply_symm_apply _ _).symm
  rw [he]
  simp only [cbcCompletedCoefficientDirectMap, Adjunction.homEquiv_unit]
  have hn := (proEtaleSheafAdjunction f CommRingCat.{t + 1}).unit.naturality
    (rightFiniteProjection d T n)
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← Functor.map_comp, ← rightFiniteProjection_pullback d f n,
    Functor.map_comp, Category.assoc]
  rfl

private def rightFiniteOpenRing {W T : Scheme.{t}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    (constantSheaf (ProEt.topology W) CommRingCat.{t + 1}).obj (rightFiniteRing d n) ≅
      ((cbcOpenSiteFunctor e he).sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology W) (ProEt.topology T)).obj
        ((constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).obj
          (rightFiniteRing d n)) := by
  have : (cbcOpenSiteFunctor e he).IsCocontinuous
      (ProEt.topology W) (ProEt.topology T) :=
    ProEt.isCocontinuous_overMap (cbcOpenWeaklyEtale e he)
  exact ((cbcOpenSiteFunctor e he).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{t + 1} (ProEt.topology W) (ProEt.topology T)).app
      ((Functor.const T.ProEtᵒᵖ).obj (rightFiniteRing d n))

private theorem rightFiniteOpenRing_unit {W T : Scheme.{t}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    toSheafify (ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (rightFiniteRing d n)) ≫
      (rightFiniteOpenRing d e he n).hom.hom =
    Functor.whiskerLeft (cbcOpenSiteFunctor e he).op
      (toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (rightFiniteRing d n))) := by
  have : (cbcOpenSiteFunctor e he).IsCocontinuous
      (ProEt.topology W) (ProEt.topology T) :=
    ProEt.isCocontinuous_overMap (cbcOpenWeaklyEtale e he)
  exact (cbcOpenSiteFunctor e he).toSheafify_pullbackSheafificationCompatibility
    CommRingCat.{t + 1} (ProEt.topology W) (ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj (rightFiniteRing d n))

attribute [local irreducible] rightFiniteOpenRing

private theorem rightFiniteOpenRing_projection {W T : Scheme.{t}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    rightFiniteProjection d W n ≫ (rightFiniteOpenRing d e he n).hom =
      cbcCompletedRestrictionMap d e he ≫
        ((cbcOpenSiteFunctor e he).sheafPushforwardContinuous CommRingCat.{t + 1}
          (ProEt.topology W) (ProEt.topology T)).map (rightFiniteProjection d T n) := by
  let G := (cbcOpenSiteFunctor e he).sheafPushforwardContinuous CommRingCat.{t + 1}
    (ProEt.topology W) (ProEt.topology T)
  have hfin : (pbcLevelConstantComparison W d n).hom ≫
        cbcFiniteRestrictionMap d e he n =
      (rightFiniteOpenRing d e he n).hom ≫ G.map (pbcLevelConstantComparison T d n).hom := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _
      (G.obj (reductionCoefficient T d n)).property
    ext V b
    change (cbcFiniteRestrictionMap d e he n).hom.app V
        ((pbcLevelConstantComparison W d n).hom.hom.app V
          ((toSheafify (ProEt.topology W)
            ((Functor.const W.ProEtᵒᵖ).obj (rightFiniteRing d n))).app V b)) =
      (pbcLevelConstantComparison T d n).hom.hom.app
        ((cbcOpenSiteFunctor e he).op.obj V)
        ((rightFiniteOpenRing d e he n).hom.hom.app V
          ((toSheafify (ProEt.topology W)
            ((Functor.const W.ProEtᵒᵖ).obj (rightFiniteRing d n))).app V b))
    erw [(pbcLevelConstantComparison_exists W d n).exists.choose_spec V b]
    have hc := ConcreteCategory.congr_hom (congr_app (rightFiniteOpenRing_unit d e he n) V) b
    change (rightFiniteOpenRing d e he n).hom.hom.app V
        ((toSheafify (ProEt.topology W)
          ((Functor.const W.ProEtᵒᵖ).obj (rightFiniteRing d n))).app V b) = _ at hc
    erw [hc, (pbcLevelConstantComparison_exists T d n).exists.choose_spec]
    exact ConcreteCategory.congr_hom
      ((cbcFiniteRestrictionMap_exists d e he n).exists.choose_spec V)
      (pbcQuotientConstant W d n V b ⊥)
  have hcomp := (cbcCompletedRestrictionMap_exists d e he).exists.choose_spec n
  change cbcCompletedRestrictionMap d e he ≫
      G.map (pbcAdicProjection T d n) =
    pbcAdicProjection W d n ≫ cbcFiniteRestrictionMap d e he n at hcomp
  unfold rightFiniteProjection
  apply (cancel_mono (G.map (pbcLevelConstantComparison T d n).hom)).mp
  change (pbcAdicProjection W d n ≫ (pbcLevelConstantComparison W d n).inv ≫
      (rightFiniteOpenRing d e he n).hom) ≫ G.map (pbcLevelConstantComparison T d n).hom =
    (cbcCompletedRestrictionMap d e he ≫ G.map
      (pbcAdicProjection T d n ≫ (pbcLevelConstantComparison T d n).inv)) ≫
        G.map (pbcLevelConstantComparison T d n).hom
  rw [G.map_comp]
  simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id, Category.comp_id]
  rw [hcomp]
  erw [← hfin]
  change pbcAdicProjection W d n ≫
      ((pbcLevelConstantComparison W d n).inv ≫
        (pbcLevelConstantComparison W d n).hom ≫ cbcFiniteRestrictionMap d e he n) = _
  rw [Iso.inv_hom_id_assoc]

private theorem rightFiniteDirect_unit {S T : Scheme.{t}} (f : S ⟶ T) (n : ℕ) :
    toSheafify (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (rightFiniteRing d n)) ≫
      (proEtaleConstantDirectImageMap f CommRingCat.{t + 1} (rightFiniteRing d n)).hom =
    (proEtaleBaseChange f).op.whiskerLeft
      (toSheafify (ProEt.topology S)
        ((Functor.const S.ProEtᵒᵖ).obj (rightFiniteRing d n))) :=
  (sheafificationAdjunction (ProEt.topology T) CommRingCat.{t + 1}).homEquiv
    _ _ |>.apply_symm_apply _

variable {U' U X' X : Scheme.{t}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : AlgebraicGeometry.OpenImmersionSquare gU j' j g)

private theorem rightFiniteSquare (n : ℕ) :
    (rightFiniteOpenRing d j sq.isOpenImmersion n).hom.hom ≫
      (cbcOpenSiteFunctor j sq.isOpenImmersion).op.whiskerLeft
        (proEtaleConstantDirectImageMap g CommRingCat.{t + 1}
          (rightFiniteRing d n)).hom ≫
      Functor.whiskerRight
        (NatTrans.op (MorphismProperty.Over.pullbackMapComparison
          (cbcOpenWeaklyEtale j sq.isOpenImmersion)
          (cbcOpenWeaklyEtale j' sq.isOpenImmersion') sq.toCommSq))
        ((constantSheaf (ProEt.topology X') CommRingCat.{t + 1}).obj
          (rightFiniteRing d n)).obj =
    (proEtaleConstantDirectImageMap gU CommRingCat.{t + 1} (rightFiniteRing d n)).hom ≫
      (proEtaleBaseChange gU).op.whiskerLeft
        (rightFiniteOpenRing d j' sq.isOpenImmersion' n).hom.hom := by
  let := Functor.isContinuous_comp (proEtaleBaseChange gU)
    (cbcOpenSiteFunctor j' sq.isOpenImmersion') (ProEt.topology U)
      (ProEt.topology U') (ProEt.topology X')
  apply sheafify_hom_ext (ProEt.topology U) _ _
    (((proEtaleBaseChange gU ⋙
      cbcOpenSiteFunctor j' sq.isOpenImmersion').sheafPushforwardContinuous
        CommRingCat.{t + 1} (ProEt.topology U)
        (ProEt.topology X')).obj
          ((constantSheaf (ProEt.topology X') CommRingCat.{t + 1}).obj
            (rightFiniteRing d n))).property
  apply NatTrans.ext
  funext V
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.op_app]
  have ho := NatTrans.congr_app
    (rightFiniteOpenRing_unit d j sq.isOpenImmersion n) V
  have hd := NatTrans.congr_app (rightFiniteDirect_unit d g n)
    ((cbcOpenSiteFunctor j sq.isOpenImmersion).op.obj V)
  have hdu := NatTrans.congr_app (rightFiniteDirect_unit d gU n) V
  have hou := NatTrans.congr_app (rightFiniteOpenRing_unit d j' sq.isOpenImmersion' n)
    ((proEtaleBaseChange gU).op.obj V)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at ho hd hdu hou
  erw [← Category.assoc, ho, ← Category.assoc, hd]
  erw [← Category.assoc, hdu, hou]
  have hn := (toSheafify (ProEt.topology X')
    ((Functor.const X'.ProEtᵒᵖ).obj (rightFiniteRing d n))).naturality
      ((MorphismProperty.Over.pullbackMapComparison
        (cbcOpenWeaklyEtale j sq.isOpenImmersion)
        (cbcOpenWeaklyEtale j' sq.isOpenImmersion') sq.toCommSq).app V.unop).op
  exact hn.symm.trans (Category.id_comp _)

private theorem rightCompletedSquare :
    (cbcCompletedRestrictionMap d j sq.isOpenImmersion).hom ≫
      (cbcOpenSiteFunctor j sq.isOpenImmersion).op.whiskerLeft
        (cbcCompletedCoefficientDirectMap d g).hom ≫
      Functor.whiskerRight
        (NatTrans.op (MorphismProperty.Over.pullbackMapComparison
          (cbcOpenWeaklyEtale j sq.isOpenImmersion)
          (cbcOpenWeaklyEtale j' sq.isOpenImmersion') sq.toCommSq))
        (completedReductionCoefficient X' d).obj =
    (cbcCompletedCoefficientDirectMap d gU).hom ≫
      (proEtaleBaseChange gU).op.whiskerLeft
        (cbcCompletedRestrictionMap d j' sq.isOpenImmersion').hom := by
  apply NatTrans.ext
  funext V
  let B := op ((proEtaleBaseChange gU ⋙
    cbcOpenSiteFunctor j' sq.isOpenImmersion').obj V.unop)
  let ev := sheafToPresheaf (ProEt.topology X') CommRingCat.{t + 1} ⋙
    (CategoryTheory.evaluation X'.ProEtᵒᵖ CommRingCat.{t + 1}).obj B
  apply (isLimitOfPreserves ev (limit.isLimit (reductionCoefficientSystem X' d))).hom_ext
  intro n
  apply (cancel_mono ((pbcLevelConstantComparison X' d n.unop).inv.hom.app B)).mp
  let α := (MorphismProperty.Over.pullbackMapComparison
    (cbcOpenWeaklyEtale j sq.isOpenImmersion)
    (cbcOpenWeaklyEtale j' sq.isOpenImmersion') sq.toCommSq).app V.unop
  have hn := (rightFiniteProjection d X' n.unop).hom.naturality α.op
  have hd := congrArg (fun z ↦ z.hom.app
    ((cbcOpenSiteFunctor j sq.isOpenImmersion).op.obj V))
      (rightFiniteProjection_direct d g n.unop)
  have ho := congrArg (fun z ↦ z.hom.app V)
    (rightFiniteOpenRing_projection d j sq.isOpenImmersion n.unop)
  have hdu := congrArg (fun z ↦ z.hom.app V)
    (rightFiniteProjection_direct d gU n.unop)
  have hou := congrArg (fun z ↦ z.hom.app ((proEtaleBaseChange gU).op.obj V))
    (rightFiniteOpenRing_projection d j' sq.isOpenImmersion' n.unop)
  have hf := NatTrans.congr_app (rightFiniteSquare d sq n.unop) V
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.op_app, ObjectProperty.FullSubcategory.comp_hom] at hd ho hdu hou hf ⊢
  change ((cbcCompletedRestrictionMap d j sq.isOpenImmersion).hom.app V ≫
      (cbcCompletedCoefficientDirectMap d g).hom.app
        ((cbcOpenSiteFunctor j sq.isOpenImmersion).op.obj V) ≫
      (completedReductionCoefficient X' d).obj.map α.op) ≫
        (rightFiniteProjection d X' n.unop).hom.app B =
    ((cbcCompletedCoefficientDirectMap d gU).hom.app V ≫
      (cbcCompletedRestrictionMap d j' sq.isOpenImmersion').hom.app
        ((proEtaleBaseChange gU).op.obj V)) ≫
      (rightFiniteProjection d X' n.unop).hom.app B
  simp only [Category.assoc]
  erw [hn]
  erw [← reassoc_of% hd]
  erw [← reassoc_of% ho]
  erw [hf]
  erw [reassoc_of% hdu]
  erw [hou]
  rfl

-- Elaborating all four completed scalar-restriction functors needs a larger budget.
/-- The right-adjoint exchange is uniquely fixed by restriction along the canonical
cartesian comparison of pro-etale objects, with its actual completed scalar action.
Source: blueprint order 1587, Step 7 (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: for V over U, the cartesian comparison from V times_U U' to V times_X X'
is an isomorphism. Restrict sections of M along it. The finite coefficient
projection equations show scalar compatibility, and pass to the completed limit.
Naturality is functoriality of restriction. Equality on every section proves uniqueness. -/
theorem cbcRightExchange_exists :
    ∃! γ : cbcCompletedModuleDirectImage d g ⋙ cbcOpenRestriction d j sq.isOpenImmersion ⟶
        cbcOpenRestriction d j' sq.isOpenImmersion' ⋙ cbcCompletedModuleDirectImage d gU,
      ∀ (M : (pbcModules X' (pbcAdicCompletion X' d))) (V : U.ProEtᵒᵖ)
        (x : ((cbcCompletedModuleDirectImage d g ⋙
          cbcOpenRestriction d j sq.isOpenImmersion).obj M).val.obj V),
        (γ.app M).val.app V x =
          M.val.map
            ((MorphismProperty.Over.pullbackMapComparison
              (cbcOpenWeaklyEtale j sq.isOpenImmersion)
              (cbcOpenWeaklyEtale j' sq.isOpenImmersion')
              sq.toCommSq).app V.unop).op x := by
  let F := cbcOpenSiteFunctor j sq.isOpenImmersion
  let G := proEtaleBaseChange g
  let H := proEtaleBaseChange gU
  let I := cbcOpenSiteFunctor j' sq.isOpenImmersion'
  let : (F ⋙ G).IsContinuous (ProEt.topology U) (ProEt.topology X') :=
    Functor.isContinuous_comp F G _ (ProEt.topology X) _
  let : (H ⋙ I).IsContinuous (ProEt.topology U) (ProEt.topology X') :=
    Functor.isContinuous_comp H I _ (ProEt.topology U') _
  let α : H ⋙ I ⟶ F ⋙ G := MorphismProperty.Over.pullbackMapComparison
    (cbcOpenWeaklyEtale j sq.isOpenImmersion)
    (cbcOpenWeaklyEtale j' sq.isOpenImmersion') sq.toCommSq
  let φ := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      (cbcCompletedRestrictionMap d j sq.isOpenImmersion)
  let ψ : reductionModuleRing X (completedReductionCoefficient X d) ⟶
      (G.sheafPushforwardContinuous RingCat.{t + 1}
        (ProEt.topology X) (ProEt.topology X')).obj
          (reductionModuleRing X' (completedReductionCoefficient X' d)) :=
    ⟨Functor.whiskerRight (cbcCompletedCoefficientDirectMap d g).hom
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})⟩
  let φ' : reductionModuleRing U (completedReductionCoefficient U d) ⟶
      (H.sheafPushforwardContinuous RingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology U')).obj
          (reductionModuleRing U' (completedReductionCoefficient U' d)) :=
    ⟨Functor.whiskerRight (cbcCompletedCoefficientDirectMap d gU).hom
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})⟩
  let ψ' := (sheafCompose (ProEt.topology U')
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      (cbcCompletedRestrictionMap d j' sq.isOpenImmersion')
  let c := φ ≫ (F.sheafPushforwardContinuous RingCat.{t + 1}
    (ProEt.topology U) (ProEt.topology X)).map ψ
  let c' := φ' ≫ (H.sheafPushforwardContinuous RingCat.{t + 1}
    (ProEt.topology U) (ProEt.topology U')).map ψ'
  have he : c ≫ (Functor.sheafPushforwardContinuousNatTrans α _ _ _).app
      (reductionModuleRing X' (completedReductionCoefficient X' d)) = c' := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact congrArg (fun z ↦ (forget₂ CommRingCat RingCat).map (z.app V))
      (rightCompletedSquare d sq)
  let γ : cbcCompletedModuleDirectImage d g ⋙
      cbcOpenRestriction d j sq.isOpenImmersion ⟶
        cbcOpenRestriction d j' sq.isOpenImmersion' ⋙
          cbcCompletedModuleDirectImage d gU :=
    rightCompositePushforward (J := ProEt.topology U) (K := ProEt.topology X)
      (L := ProEt.topology X') (K' := ProEt.topology U')
      (F := F) (G := G) (H := H) (I := I)
      (R := reductionModuleRing U (completedReductionCoefficient U d))
      (S := reductionModuleRing X (completedReductionCoefficient X d))
      (T := reductionModuleRing X' (completedReductionCoefficient X' d))
      (S' := reductionModuleRing U' (completedReductionCoefficient U' d)) φ ψ φ' ψ' α he
  refine ⟨γ, ?_, ?_⟩
  · intro M V x
    exact rightCompositePushforward_apply (J := ProEt.topology U) (K := ProEt.topology X)
      (L := ProEt.topology X') (K' := ProEt.topology U')
      (F := F) (G := G) (H := H) (I := I)
      (R := reductionModuleRing U (completedReductionCoefficient U d))
      (S := reductionModuleRing X (completedReductionCoefficient X d))
      (T := reductionModuleRing X' (completedReductionCoefficient X' d))
      (S' := reductionModuleRing U' (completedReductionCoefficient U' d)) φ ψ φ' ψ' α he M V x
  · intro γ' hγ'
    ext M V x
    exact (hγ' M V x).trans
      (rightCompositePushforward_apply (J := ProEt.topology U) (K := ProEt.topology X)
      (L := ProEt.topology X') (K' := ProEt.topology U')
      (F := F) (G := G) (H := H) (I := I)
      (R := reductionModuleRing U (completedReductionCoefficient U d))
      (S := reductionModuleRing X (completedReductionCoefficient X d))
      (T := reductionModuleRing X' (completedReductionCoefficient X' d))
      (S' := reductionModuleRing U' (completedReductionCoefficient U' d)) φ ψ φ' ψ' α he M V x).symm

/-- The cartesian comparison on actual section modules.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcRightExchange := (cbcRightExchange_exists d sq).exists.choose

/-- The canonical underived inverse exchange is the adjoint conjugate of right exchange.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcUnderivedInverseExchange :
    completedModulePullback gU d ⋙ cbcOpenShriek d j' sq.isOpenImmersion' ⟶
      cbcOpenShriek d j sq.isOpenImmersion ⋙ completedModulePullback g d :=
  (conjugateEquiv
    ((cbcOpenAdjunction d j sq.isOpenImmersion).comp
      (cbcModulePullbackAdjunction d g))
    ((cbcModulePullbackAdjunction d gU).comp
      (cbcOpenAdjunction d j' sq.isOpenImmersion'))).symm (cbcRightExchange d sq)

/-- Ordinary open base change is invertible for the cartesian square.
Source: blueprint order 1587, Step 7 (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: right exchange restricts along the cartesian comparison isomorphism, hence
is invertible. Its adjoint conjugate is invertible. This is the usual finite
coefficient open base-change map, with completed coefficient scalar actions. -/
@[instance] theorem cbcUnderivedInverseExchange_isIso :
    IsIso (cbcUnderivedInverseExchange d sq) := by
  have hsq := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback
    sq.hom_fst sq.hom_snd
  have := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (cbcOpenWeaklyEtale j sq.isOpenImmersion)
    (cbcOpenWeaklyEtale j' sq.isOpenImmersion') hsq
  have hη (M : pbcModules X' (pbcAdicCompletion X' d)) (V : U.ProEtᵒᵖ) :
      IsIso (((cbcRightExchange d sq).app M).val.app V) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hb := ConcreteCategory.bijective_of_isIso
      (M.val.presheaf.map
        ((MorphismProperty.Over.pullbackMapComparison
          (cbcOpenWeaklyEtale j sq.isOpenImmersion)
          (cbcOpenWeaklyEtale j' sq.isOpenImmersion') sq.toCommSq).app V.unop).op)
    have he : ⇑(((cbcRightExchange d sq).app M).val.app V) =
        ⇑(M.val.presheaf.map
          ((MorphismProperty.Over.pullbackMapComparison
            (cbcOpenWeaklyEtale j sq.isOpenImmersion)
            (cbcOpenWeaklyEtale j' sq.isOpenImmersion') sq.toCommSq).app V.unop).op) := by
      funext x
      exact (cbcRightExchange_exists d sq).exists.choose_spec M V x
    exact he ▸ hb
  have hM (M : pbcModules X' (pbcAdicCompletion X' d)) :
      IsIso ((cbcRightExchange d sq).app M) := by
    let e := PresheafOfModules.isoMk
      (fun V ↦ asIso (((cbcRightExchange d sq).app M).val.app V))
      (fun {_ _} f ↦ ((cbcRightExchange d sq).app M).val.naturality f)
    have he : e.hom = ((cbcRightExchange d sq).app M).val := by
      ext V x
      rfl
    have : IsIso ((SheafOfModules.forget _).map ((cbcRightExchange d sq).app M)) := by
      change IsIso (((cbcRightExchange d sq).app M).val)
      rw [← he]
      infer_instance
    exact isIso_of_reflects_iso ((cbcRightExchange d sq).app M) (SheafOfModules.forget _)
  have : IsIso (cbcRightExchange d sq) := NatIso.isIso_of_isIso_app _
  dsimp only [cbcUnderivedInverseExchange]
  infer_instance

/-- The K-flat counit condition determining the derived inverse exchange.
Naming the condition shares the predicate used by its unique choice.
Source: blueprint order 1587, Steps 2, 3, 7
(blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDerivedInverseExchangeNormalization
    (α : completedOrdinaryPullback gU d ⋙ cbcDerivedOpenShriek d j' sq.isOpenImmersion' ⟶
        cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ completedOrdinaryPullback g d) : Prop :=
  Functor.DerivedExchangeCounitNormalization
    (completedModulePullback gU d) (completedModulePullback g d)
    (cbcOpenShriek d j sq.isOpenImmersion) (cbcOpenShriek d j' sq.isOpenImmersion')
    (completedOrdinaryPullback gU d) (completedOrdinaryPullback g d)
    (completedOrdinaryPullbackComplexCounit gU d)
    (completedOrdinaryPullbackComplexCounit g d) (cbcUnderivedInverseExchange d sq)
    (CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d)) α

/-- Exactness makes the ordinary pullback counit invertible on every complex.
Source: universal left-derived uniqueness
(blueprint: lem-cbc-completed-extension-zero-comparison). -/
private theorem ordinaryComplexCounit_isIso {S T : Scheme.{t}} (f : S ⟶ T)
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    IsIso (completedOrdinaryPullbackComplexCounit f d P) := by
  have := completedModulePullback_finiteLimits f d
  have := completedModulePullback_finiteColimits f d
  have := pullbackOrdinaryUniversal f d
  have := exactPullbackCounit_isIso (completedModulePullback f d)
    (completedOrdinaryPullback f d) (completedOrdinaryPullbackCounit f d)
  exact exactComplexCounit_isIso (completedModulePullback f d)
    (completedOrdinaryPullback f d) (completedOrdinaryPullbackCounit f d) P

/-- The derived inverse exchange is fixed by the actual underived exchange on
K-flat representatives and the universal pullback counits.
Source: blueprint order 1587, Steps 2, 3, 7
(blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the recorded completed module pullbacks are exact. Universal left-derived
uniqueness compares them with their termwise exact derived functors, compatibly
with their counits. Derive the underived adjoint mate and conjugate by these
comparisons. Composition factorization and naturality give the displayed counit
normalization. Every derived object has a K-flat representative. On those
representatives cancel the invertible target counit to prove uniqueness, then
transport the equality to every object by naturality. -/
theorem cbcDerivedInverseExchange_exists :
    ∃! α : completedOrdinaryPullback gU d ⋙ cbcDerivedOpenShriek d j' sq.isOpenImmersion' ⟶
        cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ completedOrdinaryPullback g d,
      cbcDerivedInverseExchangeNormalization d sq α := by
  let F := completedModulePullback gU d
  let G := completedModulePullback g d
  let J := cbcOpenShriek d j sq.isOpenImmersion
  let J' := cbcOpenShriek d j' sq.isOpenImmersion'
  let LF := completedOrdinaryPullback gU d
  let LG := completedOrdinaryPullback g d
  have := completedModulePullback_finiteLimits gU d
  have := completedModulePullback_finiteColimits gU d
  have := completedModulePullback_finiteLimits g d
  have := completedModulePullback_finiteColimits g d
  have := pullbackOrdinaryUniversal gU d
  have := pullbackOrdinaryUniversal g d
  let e := (exactDerivedCounitComparison F LF
    (completedOrdinaryPullbackCounit gU d)).exists.choose
  let f := (exactDerivedCounitComparison G LG
    (completedOrdinaryPullbackCounit g d)).exists.choose
  let b := asIso (cbcUnderivedInverseExchange d sq)
  let α : LF ⋙ J'.mapDerivedCategory ⟶ J.mapDerivedCategory ⋙ LG :=
    Functor.whiskerRight e.hom J'.mapDerivedCategory ≫
      (Functor.mapDerivedCategorySquareIso b).hom ≫
      Functor.whiskerLeft J.mapDerivedCategory f.inv
  have hα : cbcDerivedInverseExchangeNormalization d sq α :=
    exactExchange_normalization F G J J' LF LG
      (completedOrdinaryPullbackComplexCounit gU d)
      (completedOrdinaryPullbackComplexCounit g d) e f
      (exactDerivedCounitComparison F LF
        (completedOrdinaryPullbackCounit gU d)).exists.choose_spec
      (exactDerivedCounitComparison G LG
        (completedOrdinaryPullbackCounit g d)).exists.choose_spec b _
  refine ⟨α, hα, ?_⟩
  intro β hβ
  change LF ⋙ J'.mapDerivedCategory ⟶ J.mapDerivedCategory ⋙ LG at β
  apply NatTrans.ext
  funext K
  let : EssentiallySmall.{t + 1} U.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let : HasSheafify (ProEt.topology U) AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{t, 0} U
  let : (ProEt.topology U).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} U
  obtain ⟨P, hP, ⟨eP⟩⟩ := independentKFlatRepresentatives (pbcAdicCompletion U d) K
  have he : β.app (DerivedCategory.Q.obj P) = α.app (DerivedCategory.Q.obj P) := by
    have := ordinaryComplexCounit_isIso d g ((J.mapHomologicalComplex (.up ℤ)).obj P)
    apply (cancel_mono (LG.map (J.mapDerivedCategoryFactors.hom.app P) ≫
      completedOrdinaryPullbackComplexCounit g d
        ((J.mapHomologicalComplex (.up ℤ)).obj P))).1
    exact (hβ P hP).trans (hα P hP).symm
  apply (cancel_epi ((LF ⋙ J'.mapDerivedCategory).map eP.hom)).1
  rw [β.naturality, α.naturality, he]

/-- The canonical derived inverse exchange.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDerivedInverseExchange := (cbcDerivedInverseExchange_exists d sq).exists.choose

/-- The derived mate remains an isomorphism.
Source: blueprint order 1587, Step 7 (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: on each K-flat representative the normalized derived exchange is a
composition of invertible counits and the termwise underived base-change
isomorphism. Every derived object has such a representative; hence every
component is an isomorphism, so the natural transformation is an isomorphism. -/
@[instance] theorem cbcDerivedInverseExchange_isIso :
    IsIso (cbcDerivedInverseExchange d sq) := by
  have hrep (K : DerivedCategory (pbcModules U (pbcAdicCompletion U d))) :
      ∃ P, CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K) := by
    let : EssentiallySmall.{t + 1} U.ProEt := essentiallySmallSelf.{0, t, t + 1} _
    let : HasSheafify (ProEt.topology U) AddCommGrpCat.{t + 1} :=
      WeilConjectures.integralCoefficientAbSheafify.{t, 0} U
    let : (ProEt.topology U).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
      WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} U
    exact independentKFlatRepresentatives (pbcAdicCompletion U d) K
  exact derivedExchange_isIso (completedModulePullback gU d)
    (completedModulePullback g d) (cbcOpenShriek d j sq.isOpenImmersion)
    (cbcOpenShriek d j' sq.isOpenImmersion') (completedOrdinaryPullback gU d)
    (completedOrdinaryPullback g d) (completedOrdinaryPullbackComplexCounit gU d)
    (completedOrdinaryPullbackComplexCounit g d) (cbcUnderivedInverseExchange d sq)
    (CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d))
    (ordinaryComplexCounit_isIso d gU) (ordinaryComplexCounit_isIso d g) hrep
    (cbcDerivedInverseExchange d sq) (cbcDerivedInverseExchange_exists d sq).exists.choose_spec

/-- Ordinary derived exchange in the direction used by the completed comparison.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOrdinaryExchange :
    cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ completedOrdinaryPullback g d ⟶
      completedOrdinaryPullback gU d ⋙ cbcDerivedOpenShriek d j' sq.isOpenImmersion' :=
  inv (cbcDerivedInverseExchange d sq)

/-- The intrinsic complete-object predicate, using any finite generating tuple of I.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompleteProperty (T : Scheme.{t}) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal) :
    ObjectProperty (DerivedCategory ((pbcModules T (pbcAdicCompletion T d)))) :=
  fun K ↦ IsDerivedCompleteIntrinsic T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)

/-- Extension by zero along a quasi-compact open immersion preserves intrinsic
derived completeness. The completed base-change map is the unique natural map
compatible with ordinary base change and the specified completion units. It is
an isomorphism, and both sides are derived complete.

Source: blueprint order 1587, node lem-cbc-completed-extension-zero-comparison;
Stacks Tags 03DI, 09BP, 099N
(blueprint: lem-cbc-completed-extension-zero-comparison).

Proof plan: identify completed coefficients on the two ringed slice sites by
the projection-normalized localization maps. Exact extension by zero commutes
with tensor after restriction, preserving K-flat complexes and their strict
quotient reduction towers, including every transition. For a quasi-compact open,
recollement expresses j! as the kernel of j* to i*i^-1j*. Both direct images
preserve products, and closed inverse image preserves products on the pro-etale
site; thus j! preserves all products, including the empty one. Exact countable
products identify Rlim with the signed Roos fibre, naturally for maps of strict
towers. Applying j! to that fibre gives its canonical Rlim comparison, compatible
with structure maps. Apply this first to the finite free Koszul tower and its
unit: j!K is complete when K is. Finite coefficient base-change is the inverse
adjoint mate above; its local-section formulas commute with quotient transitions.
Apply functorial Rlim to those strict tower maps and use the j'! Rlim comparison.
This constructs the displayed completed map. It commutes with ordinary-to-completed
units by the quotient-unit normalization. Source and target are complete, so the
completion universal property proves uniqueness. The finite maps and the Rlim
comparison are isomorphisms; so is the completed map. Completeness of completed
pullback and the first assertion for j' give completeness of both sides. -/
theorem cbcCompletedExchange_exists [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    ∃! β : (cbcCompleteProperty d U r a ha).ι ⋙
        cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ cbcCompletedPullback d g ⟶
      (cbcCompleteProperty d U r a ha).ι ⋙ cbcCompletedPullback d gU ⋙
        cbcDerivedOpenShriek d j' sq.isOpenImmersion',
      ∀ K : (cbcCompleteProperty d U r a ha).FullSubcategory,
        (cbcCompletedPullbackComparison d g).app
            ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ≫ β.app K =
          (cbcOrdinaryExchange d sq).app K.obj ≫
            (cbcDerivedOpenShriek d j' sq.isOpenImmersion').map
              ((cbcCompletedPullbackComparison d gU).app K.obj) := by
  sorry

/-- The canonical completed base-change map, natural on the full complete subcategory.
It is fixed by the ordinary adjoint mate and the strict quotient completion units.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompletedExchange [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :=
  (cbcCompletedExchange_exists d sq r a ha).exists.choose

/-- Completed extension by zero commutes with pullback, naturally in complete K.
It preserves completeness and both sides of the canonical exchange are complete.
Source: blueprint order 1587; Tags 09BP, 099N
(blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: exact extension by zero commutes with tensor after restricting the other
factor, hence with strict finite reduction including quotient transitions.
Quasi-compactness and ringed open/closed recollement give product preservation
by expressing extension by zero as the kernel of two product-preserving functors.
Exact countable products identify Rlim with the functorial signed Roos fibre;
therefore extension by zero commutes with that Rlim and its structure maps.
Apply this to the Koszul tower and its unit to obtain preservation of intrinsic
completeness. Apply it to the pulled strict quotient tower and the finite
coefficient adjoint-mate base-change isomorphisms to obtain a natural isomorphism.
Its quotient units agree with the specified ordinary-to-completed comparison,
so uniqueness in cbcCompletedExchange_exists identifies it with the displayed
canonical map. Completed pullback is complete; applying completeness preservation
to the base-changed quasi-compact open gives completeness of the second side. -/
theorem completedExtensionZeroComparison [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    IsIso (cbcCompletedExchange d sq r a ha) ∧
      (∀ K : (cbcCompleteProperty d U r a ha).FullSubcategory,
        cbcCompleteProperty d X r a ha
            ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ∧
          cbcCompleteProperty d X' r a ha
            ((cbcCompletedPullback d g).obj
              ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj)) ∧
          cbcCompleteProperty d X' r a ha
            ((cbcDerivedOpenShriek d j' sq.isOpenImmersion').obj
              ((cbcCompletedPullback d gU).obj K.obj))) := by
  sorry

end AlgebraicGeometry.Scheme
