/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Creates
public import WeilConjectures.CategoryTheory.TwistedActionRingedSiteData

/-! # The ringed site of a site automorphism

Source: Stacks, Sites, Tag 00W0 is motivation for the agent-formulated twisted
construction (blueprint: def-sf-twisted-action-presentation-data).

The presentation below characterizes the integer-labelled arrows, the topology,
the coefficient ring, the two restriction functors, and the orbit-sum adjunction.
No object is selected from the existence theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite

/-- The objects are a copy of the objects of the original site.
Source: the twisted variant of Stacks 00W0
(blueprint: lem-sf-twisted-action-ringed-site). -/
structure Object (C : Type u) where
  /-- The original site object. -/
  base : C


/-- The recorded tensor on morphisms, with the same resolved coefficient.
Source: Stacks 03EK (blueprint: lem-sf-twisted-action-ringed-site). -/
noncomputable abbrev tensorMap {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}} {M M' N N' : Modules R}
    (f : M ⟶ M') (g : N ⟶ N') : tensorObj M N ⟶ tensorObj M' N' := f ⊗ₘ g

/-- Ordinary sheaf evaluation, from the recorded tensor-Hom adjunction.
Source: Stacks 03EK and 04TT (blueprint: lem-sf-twisted-action-ringed-site). -/
noncomputable def evaluationMap {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}} (M N : Modules R) :
    tensorObj M (SheafOfModules.homObj (R := R) M N) ⟶ N :=
  (SheafOfModules.tensorHomEquiv (R := R) M
    (SheafOfModules.homObj (R := R) M N) N).symm (𝟙 _)

/-- The full subcategory of endofunctor algebras with invertible structure map.
Source: the fixed-pair dependency's exact Mathlib specialization
(blueprint: lem-sf-twisted-action-ringed-site). -/
abbrev Pairs {A : Type (u + 1)} [Category.{u} A] (T : A ⥤ A) :=
  ObjectProperty.FullSubcategory (fun M : Endofunctor.Algebra T ↦ IsIso M.str)

/-- Forgetting a fixed pair uses the recorded algebra-forgetful construction.
Source: the fixed-pair dependency (blueprint: lem-sf-twisted-action-ringed-site). -/
def forgetPairs {A : Type (u + 1)} [Category.{u} A] (T : A ⥤ A) : Pairs T ⥤ A :=
  ObjectProperty.ι _ ⋙ Endofunctor.Algebra.forget T

/-- The isomorphism already contained in a fixed pair.
Source: the fixed-pair dependency (blueprint: lem-sf-twisted-action-ringed-site). -/
noncomputable def pairIso {A : Type (u + 1)} [Category.{u} A] {T : A ⥤ A}
    (M : Pairs T) : T.obj M.obj.a ≅ M.obj.a :=
  @asIso A _ _ _ M.obj.str M.property

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

/-- Translation of modules along the chosen inverse, with scalars transported by a.
This is the actual precomposition-and-restriction-of-scalars functor.
Source: twisted Stacks 00W0; Stacks 03D6
(blueprint: lem-sf-twisted-action-ringed-site). -/
noncomputable def sigma : Modules R ⥤ Modules R :=
  SheafOfModules.pushforward
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a.inv)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- All the data and normalizations asserted by the twisted ringed-site lemma.
Source: the agent-formulated twisted version of Stacks 00W0
(blueprint: lem-sf-twisted-action-ringed-site).

Powers of a chosen equivalence are associated only up to their displayed natural
isomorphisms; the arrow-composition equation includes this necessary associator.
Every comparison below is a sheaf morphism or natural isomorphism.
-/
structure Site where
  /-- The semidirect category on the original objects. -/
  [category : SmallCategory (Object C)]
  /-- Inclusion of the degree-zero arrows. -/
  inclusion : C ⥤ Object C
  /-- No new objects are introduced. -/
  inclusion_obj (X : C) : inclusion.obj X = ⟨X⟩
  /-- Integer-labelled base arrows, with no extra identifications. -/
  arrows (X Y : C) :
    (inclusion.obj X ⟶ inclusion.obj Y) ≃ Σ n : ℤ, X ⟶ (s ^ n).functor.obj Y
  /-- The chosen coherent association of the integer powers. -/
  powerComp (n m : ℤ) :
    (s ^ m).functor ⋙ (s ^ n).functor ≅ (s ^ (n + m)).functor
  /-- The identity is the degree-zero identity. -/
  arrows_id (X : C) : arrows X X (𝟙 _) = ⟨0, 𝟙 X⟩
  /-- The specified composition of integer-labelled arrows. -/
  arrows_comp (X Y Z : C) (n m : ℤ)
      (f : X ⟶ (s ^ n).functor.obj Y) (g : Y ⟶ (s ^ m).functor.obj Z) :
    arrows X Z ((arrows X Y).symm ⟨n, f⟩ ≫ (arrows Y Z).symm ⟨m, g⟩) =
      ⟨n + m, f ≫ (s ^ n).functor.map g ≫ (powerComp n m).hom.app Z⟩
  /-- The inclusion keeps every degree-zero base arrow. -/
  arrows_inclusion {X Y : C} (f : X ⟶ Y) : arrows X Y (inclusion.map f) = ⟨0, f⟩
  /-- The topology generated by the old covering sieves on degree-zero arrows. -/
  topology : GrothendieckTopology (Object C)
  /-- Precise generated-topology normalization. -/
  topology_eq : topology =
    sInf {K : GrothendieckTopology (Object C) |
      ∀ (X : C) (S : Sieve X), S ∈ J X → S.functorPushforward inclusion ∈ K (inclusion.obj X)}
  /-- Restriction along the inclusion takes sheaves to sheaves. -/
  [inclusion_continuous : inclusion.IsContinuous J topology]
  /-- The commutative coefficient ring on the action site. -/
  coefficient : Sheaf topology CommRingCat.{u}
  /-- Its degree-zero restriction is the original ring. -/
  coefficientRestriction :
    (inclusion.sheafPushforwardContinuous CommRingCat.{u} J topology).obj coefficient ≅ R
  /-- The ring restriction on a generator of degree minus one is the given a.
  Functoriality and the composition rule then determine every integer iterate. -/
  coefficient_generator (X : C) (r : coefficient.obj.obj (op (inclusion.obj X))) :
    (coefficientRestriction.hom.hom.app (op (s.inverse.obj X)))
      (coefficient.obj.map
        ((arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op r) =
      (a.inv.hom.app (op X))
        ((coefficientRestriction.hom.hom.app (op X)) r)
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The module and set presentations and the geometric restriction.
Source: the agent-formulated twisted version of Stacks 00W0
(blueprint: lem-sf-twisted-action-ringed-site). -/
structure RestrictionPresentation extends Site J s R a where
  /-- The translation is an autoequivalence, not an arbitrary endofunctor. -/
  translation : Modules R ≌ Modules R
  /-- Its forward functor is the explicitly defined module translation. -/
  translation_eq : translation.functor = sigma J s R a
  /-- Module sheaves on the constructed site are exactly the fixed pairs. -/
  modules : Modules coefficient ≌ Pairs (sigma J s R a)
  /-- Restriction is exactly forgetting the pair, naturally. -/
  restriction :
    modules.functor ⋙ forgetPairs (sigma J s R a) ≅
      SheafOfModules.pushforward
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map coefficientRestriction.inv)
  /-- The structure isomorphism is recovered from the degree-minus-one generator. -/
  module_generator (M : Modules coefficient) (X : C)
      (x : ((sigma J s R a).obj (modules.functor.obj M).obj.a).val.obj (op X)) :
    (restriction.hom.app M).val.app (op (s.inverse.obj X)) x =
      M.val.map ((arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op
        ((restriction.hom.app M).val.app (op X)
          ((modules.functor.obj M).obj.str.val.app (op X) x))
  /-- Addition is the inherited addition of underlying module morphisms. -/
  modules_add {M N : Modules coefficient} (f g : M ⟶ N) :
    (modules.functor.map (f + g)).hom.f =
      (modules.functor.map f).hom.f + (modules.functor.map g).hom.f
  /-- The set-sheaf version presents invertible translation actions. -/
  sets : Sheaf topology (Type u) ≌
    Pairs (s.inverse.sheafPushforwardContinuous (Type u) J J)
  /-- Forgetting the set action is ordinary restriction. -/
  setsRestriction : sets.functor ⋙
      forgetPairs (s.inverse.sheafPushforwardContinuous (Type u) J J) ≅
    inclusion.sheafPushforwardContinuous (Type u) J topology
  /-- The set action too is recovered from the degree-minus-one generator. -/
  set_generator (M : Sheaf topology (Type u)) (X : C)
      (x : (sets.functor.obj M).obj.a.obj.obj (op (s.inverse.obj X))) :
    (setsRestriction.hom.app M).hom.app (op (s.inverse.obj X)) x =
      M.obj.map ((arrows (s.inverse.obj X) X).symm ⟨-1, 𝟙 _⟩).op
        ((setsRestriction.hom.app M).hom.app (op X)
          ((sets.functor.obj M).obj.str.hom.app (op X) x))
  /-- The geometric morphism has the direction Sh(C) to Sh(C semidirect Z). -/
  geometric : RingedToposMorphism (ring R) (ring coefficient)
  /-- Its inverse image is the set restriction functor. -/
  geometric_inverse : geometric.inverse =
    inclusion.sheafPushforwardContinuous (Type u) J topology
  /-- The structural map is the ring restriction isomorphism on underlying sets. -/
  structural : IsIso geometric.ringMap
  /-- Under the displayed inverse-image equality the structural ring map is restriction. -/
  structural_eq : geometric.ringMap =
    (eqToHom geometric_inverse).app ((sheafCompose topology (forget RingCat)).obj
      (ring coefficient)) ≫
      (sheafCompose J (forget RingCat)).map
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map coefficientRestriction.hom)
  /-- Module restriction is its module pullback by the adjunction universal property. -/
  modulePullback : (modules.functor ⋙ forgetPairs (sigma J s R a)) ⊣ geometric.modules
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Restriction together with its created limits, colimits, and exactness.
Source: step 5 of the twisted action-site construction
(blueprint: lem-sf-twisted-action-ringed-site). -/
structure ModulePresentation extends RestrictionPresentation J s R a where
  /-- Forgetting the module action is conservative. -/
  conservative : (forgetPairs (sigma J s R a)).ReflectsIsomorphisms
  /-- Forgetting creates all limits in the fixed universe. -/
  createsLimits : CreatesLimitsOfSize.{u, u} (forgetPairs (sigma J s R a))
  /-- Forgetting creates all colimits in the fixed universe. -/
  createsColimits : CreatesColimitsOfSize.{u, u} (forgetPairs (sigma J s R a))
  /-- Exactness, expressed without a second abelian structure on fixed pairs. -/
  exact_limits : PreservesFiniteLimits (forgetPairs (sigma J s R a))
  /-- Exactness includes cokernels as well as kernels. -/
  exact_colimits : PreservesFiniteColimits (forgetPairs (sigma J s R a))
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The exact orbit-sum induction on the displayed action site.
Source: the agent-formulated twisted version of Stacks 00W0
(blueprint: lem-sf-twisted-action-ringed-site). -/
structure OrbitPresentation extends ModulePresentation J s R a where
  /-- The orbit-sum LEFT adjoint. -/
  induction : Modules R ⥤ Pairs (sigma J s R a)
  /-- The orbit-sum adjunction. -/
  inductionAdjunction : induction ⊣ forgetPairs (sigma J s R a)
  /-- The underlying object is the coproduct of all integer translates. -/
  inductionSum (M : Modules R) :
    ∐ (fun n : ℤ ↦ (translation ^ n).functor.obj M) ≅ (induction.obj M).obj.a
  /-- Translation commutes with an integer iterate by its canonical association. -/
  translationStep (n : ℤ) :
    (translation ^ n).functor ⋙ sigma J s R a ≅ (translation ^ (n + 1)).functor
  /-- The structure map reindexes the n-th summand to the (n+1)-st summand. -/
  induction_shift (M : Modules R) (n : ℤ) :
    (sigma J s R a).map
        (Sigma.ι (fun k : ℤ ↦ (translation ^ k).functor.obj M) n ≫
          (inductionSum M).hom) ≫ (induction.obj M).obj.str =
      (translationStep n).hom.app M ≫
        Sigma.ι (fun k : ℤ ↦ (translation ^ k).functor.obj M) (n + 1) ≫
          (inductionSum M).hom
  /-- Restriction to the summand zero determines the adjunction. -/
  induction_zero (M : Modules R) (N : Pairs (sigma J s R a))
      (f : induction.obj M ⟶ N) :
    inductionAdjunction.homEquiv M N f =
      Sigma.ι (fun k : ℤ ↦ (translation ^ k).functor.obj M) 0 ≫
        (inductionSum M).hom ≫ f.hom.f
  /-- Induction is additive on the actual underlying module maps. -/
  induction_add {M N : Modules R} (f g : M ⟶ N) :
    (induction.map (f + g)).hom.f =
      (induction.map f).hom.f + (induction.map g).hom.f
  /-- Exactness of the left adjoint, including preservation of kernels. -/
  induction_limits : PreservesFiniteLimits induction
  /-- Exactness also includes preservation of cokernels. -/
  induction_colimits : PreservesFiniteColimits induction
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The full presentation, including canonical tensor and internal Hom comparisons.
Source: the agent-formulated twisted version of Stacks 00W0
(blueprint: lem-sf-twisted-action-ringed-site). -/
structure Presentation extends OrbitPresentation J s R a where
  /-- The restriction of the sheaf tensor is the ordinary sheaf tensor. -/
  tensor (M N : Modules coefficient) :
    (modules.functor.obj (tensorObj M N)).obj.a ≅
      tensorObj (modules.functor.obj M).obj.a (modules.functor.obj N).obj.a
  /-- Translation's tensor comparison. -/
  sigmaTensor (M N : Modules R) :
    (sigma J s R a).obj (tensorObj M N) ≅
      tensorObj ((sigma J s R a).obj M) ((sigma J s R a).obj N)
  /-- Restriction keeps the local pure tensors that define the sheaf tensor. -/
  tensor_pure (M N : Modules coefficient) (X : Cᵒᵖ)
      (x : (modules.functor.obj M).obj.a.val.obj X)
      (y : (modules.functor.obj N).obj.a.val.obj X) :
    (restriction.hom.app (tensorObj M N)).val.app X
        ((tensor M N).inv.val.app X
          (pureTensor (modules.functor.obj M).obj.a (modules.functor.obj N).obj.a X x y)) =
      pureTensor M N (inclusion.op.obj X)
        ((restriction.hom.app M).val.app X x) ((restriction.hom.app N).val.app X y)
  /-- Translation's tensor comparison has the canonical pure-tensor normalization. -/
  sigmaTensor_pure (M N : Modules R) (X : Cᵒᵖ)
      (x : M.val.obj (s.inverse.op.obj X)) (y : N.val.obj (s.inverse.op.obj X)) :
    (sigmaTensor M N).hom.val.app X (pureTensor M N (s.inverse.op.obj X) x y) =
      pureTensor ((sigma J s R a).obj M) ((sigma J s R a).obj N) X x y
  /-- The tensor action is the diagonal action under these comparisons. -/
  tensor_action (M N : Modules coefficient) :
    (modules.functor.obj (tensorObj M N)).obj.str ≫ (tensor M N).hom =
      (sigma J s R a).map (tensor M N).hom ≫
        (sigmaTensor (modules.functor.obj M).obj.a (modules.functor.obj N).obj.a).hom ≫
          tensorMap (modules.functor.obj M).obj.str (modules.functor.obj N).obj.str
  /-- The tensor unit restricts to R. -/
  unit : (modules.functor.obj (𝟙_ (Modules coefficient))).obj.a ≅ 𝟙_ (Modules R)
  /-- On the unit, the comparison is the coefficient restriction itself. -/
  unit_sections (X : Cᵒᵖ)
      (x : (modules.functor.obj (𝟙_ (Modules coefficient))).obj.a.val.obj X) :
    unit.hom.val.app X x =
      (coefficientRestriction.hom.hom.app X)
        ((restriction.hom.app (𝟙_ (Modules coefficient))).val.app X x)
  /-- The action on the unit is the originally chosen ring action. -/
  sigmaUnit : (sigma J s R a).obj (𝟙_ (Modules R)) ≅ 𝟙_ (Modules R)
  /-- The original ring isomorphism specifies the unit action on local sections. -/
  sigmaUnit_sections (X : C) (r : R.obj.obj (op (s.inverse.obj X))) :
    sigmaUnit.hom.val.app (op X) r = (a.hom.hom.app (op X)) r
  /-- The unit comparison intertwines precisely this action. -/
  unit_action : (modules.functor.obj (𝟙_ (Modules coefficient))).obj.str ≫ unit.hom =
    (sigma J s R a).map unit.hom ≫ sigmaUnit.hom
  /-- The internal Hom restricts as an isomorphism of sheaves of modules. -/
  hom (M N : Modules coefficient) :
    (modules.functor.obj (SheafOfModules.homObj (R := coefficient) M N)).obj.a ≅
      SheafOfModules.homObj (R := R) (modules.functor.obj M).obj.a (modules.functor.obj N).obj.a
  /-- Translation's internal Hom comparison. -/
  sigmaHom (M N : Modules R) :
    (sigma J s R a).obj (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := R) ((sigma J s R a).obj M) ((sigma J s R a).obj N)
  /-- Translation's Hom comparison is the unique one preserving ordinary evaluation. -/
  sigmaHom_evaluation (M N : Modules R) :
    (sigma J s R a).map (evaluationMap M N) =
      (sigmaTensor M (SheafOfModules.homObj (R := R) M N)).hom ≫
        tensorMap (𝟙 _) (sigmaHom M N).hom ≫
          evaluationMap ((sigma J s R a).obj M) ((sigma J s R a).obj N)
  /-- The internal Hom action is theta_N sigma(f) theta_M inverse. -/
  hom_action (M N : Modules coefficient) :
    (modules.functor.obj (SheafOfModules.homObj (R := coefficient) M N)).obj.str ≫ (hom M N).hom =
      (sigma J s R a).map (hom M N).hom ≫
        (sigmaHom (modules.functor.obj M).obj.a (modules.functor.obj N).obj.a).hom ≫
          SheafOfModules.homObjMap (R := R) (pairIso (modules.functor.obj M)).inv
            (modules.functor.obj N).obj.str
  /-- The tensor identifications are natural in both sheaves. -/
  tensor_naturality {M M' N N' : Modules coefficient} (f : M ⟶ M') (g : N ⟶ N') :
    (modules.functor.map (tensorMap f g)).hom.f ≫ (tensor M' N').hom =
      (tensor M N).hom ≫
        tensorMap (modules.functor.map f).hom.f (modules.functor.map g).hom.f
  /-- The internal Hom identifications are natural in both sheaves. -/
  hom_naturality {M M' N N' : Modules coefficient} (f : M' ⟶ M) (g : N ⟶ N') :
    (modules.functor.map (SheafOfModules.homObjMap (R := coefficient) f g)).hom.f ≫
        (hom M' N').hom =
      (hom M N).hom ≫
        SheafOfModules.homObjMap (R := R)
          (modules.functor.map f).hom.f (modules.functor.map g).hom.f
  /-- Tensor symmetry is respected. -/
  symmetry (M N : Modules coefficient) :
    (modules.functor.map (β_ M N).hom).hom.f ≫ (tensor N M).hom =
      (tensor M N).hom ≫ (β_ (modules.functor.obj M).obj.a
        (modules.functor.obj N).obj.a).hom
  /-- Evaluation is the same evaluation of the restricted sheaves. -/
  evaluation (M N : Modules coefficient) :
    (modules.functor.map (evaluationMap M N)).hom.f =
      (tensor M (SheafOfModules.homObj (R := coefficient) M N)).hom ≫
        tensorMap (𝟙 _) (hom M N).hom ≫
          evaluationMap (modules.functor.obj M).obj.a (modules.functor.obj N).obj.a

end CategoryTheory.TwistedActionRingedSite
