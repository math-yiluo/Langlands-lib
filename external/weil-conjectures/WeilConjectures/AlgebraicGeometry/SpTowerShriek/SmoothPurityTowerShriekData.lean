/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Interface for compact-support operations on varying-coefficient towers

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-bound,
`sk-lem-sp-tower-bound-operations.md`, clauses (1)--(3)
(blueprint: def-sp-tower-shriek-data).

Index n denotes the positive exponent n+1. All localizations are ordinary derived
categories of strict semilinear systems, never diagrams in derived categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

/-- The actual ell-power quotient, retaining the recorded tower's indexing.
Source: blueprint coefficient convention (blueprint: def-sp-tower-shriek-data). -/
abbrev R (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing constant commutative ring sheaf, at the paper's positive level n+1.
Source: blueprint coefficient convention (blueprint: def-sp-tower-shriek-data). -/
abbrev B (T : Scheme.{u}) (n : ℕ) :
    Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  Scheme.proEtaleConstantRing T (R l E n)

/-- The actual adjacent quotient map, not a chosen ring map.
Source: blueprint coefficient convention (blueprint: def-sp-tower-shriek-data). -/
def tau (T : Scheme.{u}) (n : ℕ) : B l E T (n + 1) ⟶ B l E T n :=
  (spCoefficientCommRings l E T).map (homOfLE (Nat.le_succ n)).op

/-- The original small pro-etale site fits in the coefficient universe, with its
object and morphism universes unchanged. Source: blueprint size convention
(blueprint: def-sp-tower-shriek-data). -/
instance (priority := 2000) small (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _

/-- The published ringed sequence-site model of these strict varying-ring systems.
Source: blueprint clause (2), semilinear section model
(blueprint: def-sp-tower-shriek-data). -/
abbrev S (T : Scheme.{u}) :=
  SemilinearSections.Systems.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (B l E T) (tau l E T)

/-- The ordinary unbounded localization of the actual system category.
Source: blueprint clauses (2)--(3) (blueprint: def-sp-tower-shriek-data). -/
abbrev D (T : Scheme.{u}) :=
  SemilinearSections.DS.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (B l E T) (tau l E T)

/-- Exact ordinary evaluation in the published sequence-site model.
Source: blueprint clauses (1)--(3) (blueprint: def-sp-tower-shriek-data). -/
abbrev ev (T : Scheme.{u}) (n : ℕ) :=
  SemilinearSections.evaluation.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (B l E T) (tau l E T) n

/-- Its exact derived evaluation, defined on all unbounded complexes.
Source: blueprint clauses (1)--(3) (blueprint: def-sp-tower-shriek-data). -/
abbrev Ev (T : Scheme.{u}) (n : ℕ) :=
  SemilinearSections.e.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (B l E T) (tau l E T) n

/-- Canonically normalized presentations of the recorded tower category and its tensor.
The equivalence fixes every section and map; the tensor is the existing signed K-flat
sequence-site tensor. Source: blueprint clauses (1)--(3)
(blueprint: def-sp-tower-shriek-data). -/
class Base where
  /-- Ramification index of the specified uniformizer. -/
  ramification : ℕ
  /-- The ramification index is positive. -/
  ramification_positive : 0 < ramification
  /-- The unit in ell = unit times uniformizer^e. -/
  ramificationUnit : (Padic.coefficientExtensionIntegers l E)ˣ
  /-- This is the equation in the actual ring of integers. -/
  ramification_eq : (l : Padic.coefficientExtensionIntegers l E) =
    ramificationUnit * Padic.coefficientExtensionUniformizer l E ^ ramification
  /-- Equality of the actual ideals, so coefficient transport is quotient congruence. -/
  ideals : ∀ n : ℕ, spEllIdeal l E ^ (n + 1) =
    Padic.coefficientExtensionIdeal l E (ramification * (n + 1))
  /-- The positive ell-power quotients are finite. -/
  [finite : ∀ n : ℕ, Finite (R l E n)]
  /-- The sequence-site presentation changes no section module. -/
  realization : ∀ T : Scheme.{u}, spCoefficientTowers l E T ≌ S l E T
  /-- The presentation preserves the additive structure of the abelian category. -/
  [realizationAdditive : ∀ T : Scheme.{u}, (realization T).functor.Additive]
  /-- The presentation is literally the same module at each (n,U). -/
  sections : ∀ (T : Scheme.{u}) (M : spCoefficientTowers l E T) (n : ℕ)
    (U : T.ProEtᵒᵖ),
    HEq (((realization T).functor.obj M).val.obj (op (n, U.unop)))
      (M.obj.obj (op (n, U.unop)))
  /-- The presentation retains all restriction and quotient-transition maps. -/
  restrictions : ∀ (T : Scheme.{u}) (M : spCoefficientTowers l E T)
    {U V : (ℕ × T.ProEt)ᵒᵖ} (a : U ⟶ V),
    HEq (((realization T).functor.obj M).val.map a) (M.obj.map a)
  /-- It retains all linear components of tower maps. -/
  morphisms : ∀ (T : Scheme.{u}) {M N : spCoefficientTowers l E T} (a : M ⟶ N)
    (U : (ℕ × T.ProEt)ᵒᵖ),
    HEq (((realization T).functor.map a).val.app U) (a.hom.app U)
  /-- The already published ordinary unbounded derived calculus. -/
  calculus : ∀ T : Scheme.{u},
    SemilinearSections.Data.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (B l E T) (tau l E T)
  /-- The recorded signed K-flat constraints are normalized on the same closed structure.
  Binary tensor/Hom models alone do not impose this associator and unit normalization. -/
  tensorNormalization : ∀ T : Scheme.{u},
    Nonempty { M : SemilinearSections.NormalizedTensorModel.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T))
      (SemilinearSections.systemRing.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (B l E T) (tau l E T)) //
        M.closed = (calculus T).closed }
  /-- Resolutions on the system site, without normalizing the input tower. -/
  [kinjective : ∀ T : Scheme.{u}, Abelian.HasKInjectiveResolutions (S l E T)]

attribute [instance] Base.finite Base.kinjective

/-- The existing K-flat tensor on the actual ringed sequence site.
Source: blueprint clause (2) (blueprint: def-sp-tower-shriek-data). -/
abbrev tensor (b : Base l E) (T : Scheme.{u}) := (b.calculus T).closed.tensor

/-- Horizontal compatibility expressed for a supplied family of finite adjunctions.
Keeping these adjunctions as parameters avoids unfolding their sheafification models
while checking the formula. The auxiliary section y and its HEq premise express
the unchanged carrier of coefficient restriction without unfolding its scalar action.
Source: actual termwise inverse image (blueprint: def-sp-tower-shriek-data). -/
@[irreducible] def OrdinaryUnitTransitionModel {X Y : Scheme.{u}}
    (P : ∀ n : ℕ, SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (B l E Y n) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (B l E X n))
    (Q : ∀ n : ℕ, SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (B l E X n) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1}
          (Scheme.ProEt.topology Y) (B l E Y n))
    (adj : ∀ n : ℕ, P n ⊣ Q n)
    (EY : ∀ n : ℕ, S l E Y ⥤ SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (B l E Y n))
    (EX : ∀ n : ℕ, S l E X ⥤ SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (B l E X n))
    (RY : ∀ {m n : ℕ} (_h : n ≤ m),
      SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (B l E Y n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (B l E Y m))
    (RX : ∀ {m n : ℕ} (_h : n ≤ m),
      SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (B l E X n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (B l E X m))
    (tY : ∀ {m n : ℕ} (h : n ≤ m), EY m ⟶ EY n ⋙ RY h)
    (tX : ∀ {m n : ℕ} (h : n ≤ m), EX m ⟶ EX n ⋙ RX h)
    (F : S l E Y ⥤ S l E X)
    (e : ∀ n : ℕ, F ⋙ EX n ≅ EY n ⋙ P n) : Prop :=
  ∀ (M : S l E Y) {m n : ℕ} (h : n ≤ m)
    (U : Y.ProEtᵒᵖ) (x : ((EY m).obj M).val.obj U)
    (y : ((EY n).obj M).val.obj U),
    HEq (((tY h).app M).val.app U x) y →
    HEq ((((adj m).homEquiv _ _)
      ((e m).inv.app M ≫ (tX h).app (F.obj M) ≫
        (RX h).map ((e n).hom.app M))).val.app U x)
      (((adj n).unit.app ((EY n).obj M)).val.app U y)

/-- The horizontal compatibility of the actual constant-ring finite adjunction units.
The generic formula is specialized to the specified finite functors and adjunctions,
not to arbitrarily supplied underlying-sheaf identifications.
Source: actual termwise inverse image (blueprint: def-sp-tower-shriek-data). -/
@[irreducible] def OrdinaryUnitTransition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : S l E Y ⥤ S l E X)
    (e : ∀ n : ℕ, F ⋙ ev l E X n ≅
      ev l E Y n ⋙ proEtaleConstantRingPullback (R l E n) f) : Prop :=
  OrdinaryUnitTransitionModel l E
    (fun n ↦ proEtaleConstantRingPullback (R l E n) f)
    (fun n ↦ proEtaleConstantRingPushforward (R l E n) f)
    (fun n ↦ proEtaleConstantRingAdjunction (R l E n) f)
    (ev l E Y) (ev l E X)
    (fun h ↦ SemilinearSections.res.{u + 1, u, u + 1}
      (SemilinearSections.coefficientMap.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) h))
    (fun h ↦ SemilinearSections.res.{u + 1, u, u + 1}
      (SemilinearSections.coefficientMap.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (B l E X) (tau l E X) h))
    (fun h ↦ SemilinearSections.transition.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) h)
    (fun h ↦ SemilinearSections.transition.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (B l E X) (tau l E X) h) F e

/-- Geometric operations in the fixed constant-coefficient coordinates. The HEq fields
are transports of the *specified* generic geometric calculus, whose units, counits,
coefficient mates and signed K-flat tensor comparisons are normalized before evaluation.
Source: blueprint proof, paragraphs (1)--(2); Zheng 4.10
(blueprint: def-sp-tower-shriek-data). -/
structure Geometry (b : Base l E) {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The source of the normalization, on the actual small pro-etale topoi. -/
  generic : SemilinearSections.Geometry.{u + 1, u, u + 1}
    (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
    (Scheme.ProEt.topology X)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1)))
  /-- The specified counit-mate coefficient transitions for total direct image. -/
  transitionFormula : generic.TransitionFormula
    (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
    (Scheme.ProEt.topology X)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1)))
  /-- The inverse-image transition uses the same coefficient comparison. -/
  pullTransitionFormula : generic.PullTransitionFormula
    (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
    (Scheme.ProEt.topology X)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1)))
  /-- Projection evaluation is the generic normalized counit-transpose equation. -/
  projectionEvaluation : generic.ProjectionEvaluation
    (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) (b.calculus Y)
    (Scheme.ProEt.topology X)
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1)))
  /-- Inverse image of the constant ring is identified by its constant sections. -/
  coefficients : generic.coefficients = B l E X
  /-- The identifications retain the quotient homomorphisms. -/
  transitions : HEq generic.coefficientTransition (tau l E X)
  /-- The target tensor is the same fixed K-flat tensor. -/
  target : HEq generic.target (b.calculus X)
  /-- Ordinary inverse image of systems. -/
  pull : S l E Y ⥤ S l E X
  /-- Ordinary direct image of systems. -/
  push : S l E X ⥤ S l E Y
  /-- The coordinate changes above transport the actual generic inverse image. -/
  pull_eq : HEq pull generic.pull
  /-- They transport the actual generic direct image. -/
  push_eq : HEq push generic.push
  /-- Exact additive inverse image. -/
  [pullAdditive : pull.Additive]
  /-- Preservation of kernels. -/
  [pullLimits : PreservesFiniteLimits pull]
  /-- Preservation of cokernels. -/
  [pullColimits : PreservesFiniteColimits pull]
  /-- Additive direct image. -/
  [pushAdditive : push.Additive]
  /-- The ordinary normalized geometric adjunction. -/
  ordinaryAdjunction : pull ⊣ push
  /-- No second choice of the adjunction is made. -/
  ordinaryAdjunction_eq : HEq ordinaryAdjunction generic.ordinaryAdjunction
  /-- Its derived adjunction is the canonical localization of this ordinary pair. -/
  derivedAdjunction_eq :
    HEq ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction generic.adjunction
  /-- Ordinary component comparison, retaining the generic section normalization. -/
  ordinaryPullEvaluation : ∀ n : ℕ, pull ⋙ ev l E X n ≅
    ev l E Y n ⋙ proEtaleConstantRingPullback (R l E n) f
  ordinaryPullEvaluation_eq : ∀ n : ℕ,
    HEq (ordinaryPullEvaluation n) (generic.ordinaryPullEvaluation n)
  /-- The actual finite adjunction units commute with horizontal restrictions,
  independently of the auxiliary generic underlying-sheaf comparisons. -/
  ordinaryUnitTransition : OrdinaryUnitTransition l E f pull ordinaryPullEvaluation
  /-- Exact inverse-image evaluation. -/
  pullEvaluation : ∀ n : ℕ,
    pull.mapDerivedCategory ⋙ Ev l E X n ≅
      Ev l E Y n ⋙ proEtaleConstantRingDerivedPullback (R l E n) f
  /-- The specified generic comparison is retained. -/
  pullEvaluation_eq : ∀ n : ℕ, HEq (pullEvaluation n) (generic.pullEvaluation n)
  /-- Ordinary direct image retains the sectionwise generic realization. -/
  ordinaryPushEvaluation : ∀ n : ℕ, push ⋙ ev l E Y n ≅
    ev l E X n ⋙ proEtaleConstantRingPushforward (R l E n) f
  ordinaryPushEvaluation_eq : ∀ n : ℕ,
    HEq (ordinaryPushEvaluation n) (generic.ordinaryPushEvaluation n)
  /-- Both level functors and their adjunction are the specified constant-section
  operations. Bundling the functors retains their identities under coefficient transport. -/
  levelAdjunction_eq : ∀ n : ℕ,
    HEq
      (⟨(generic.inverseImage n).modules, generic.levelPush n, generic.levelAdjunction n⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (generic.coefficients n),
        Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (generic.coefficients n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P)
      (⟨proEtaleConstantRingPullback (R l E n) f,
        proEtaleConstantRingPushforward (R l E n) f,
        proEtaleConstantRingAdjunction (R l E n) f⟩ :
        Σ L : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n),
        Σ P : SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (B l E X n) ⥤
          SemilinearSections.Mod.{u + 1, u, u + 1}
            (Scheme.ProEt.topology Y) (B l E Y n), L ⊣ P)
  /-- Total right derived direct image evaluation, including on D+. -/
  pushEvaluation : ∀ n : ℕ,
    push.rightDerivedFunctor ⋙ Ev l E Y n ≅
      Ev l E X n ⋙ (proEtaleConstantRingPushforward (R l E n) f).rightDerivedFunctor
  /-- This is the generic comparison normalized by the derived adjunction. -/
  pushEvaluation_eq : ∀ n : ℕ, HEq (pushEvaluation n) (generic.pushEvaluation n)
  /-- Derived inverse image preserves the actual derived tensor. -/
  tensorPullback : tensor l E b Y ⋙ pull.mapDerivedCategory ≅
    (pull.mapDerivedCategory.prod pull.mapDerivedCategory) ⋙ tensor l E b X
  /-- Its pure-tensor and signed representative normalization is the generic one. -/
  tensorPullback_eq : HEq tensorPullback generic.tensorPullback

attribute [instance] Geometry.pullAdditive Geometry.pullLimits Geometry.pullColimits
  Geometry.pushAdditive

/-- The inverse-image functor, by exact termwise localization.
Source: blueprint clause (2) (blueprint: def-sp-tower-shriek-data). -/
abbrev pull (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y} (g : Geometry l E b f) :=
  g.pull.mapDerivedCategory

/-- The direct-image functor, by total right derivation on the system category.
Source: blueprint clause (1) (blueprint: def-sp-tower-shriek-data). -/
abbrev push (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y} (g : Geometry l E b f) :=
  g.push.rightDerivedFunctor

/-- The canonical derived adjunction, prior to every evaluation.
Source: blueprint proof, geometric mate construction
(blueprint: def-sp-tower-shriek-data). -/
def adjunction (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : Geometry l E b f) : pull l E b g ⊣ push l E b g :=
  g.ordinaryAdjunction.mapDerivedCategoryRightDerivedAdjunction

/-- Exact termwise descent of a transformation of actual tower functors.
Source: blueprint clause (2c), localization of complexes
(blueprint: def-sp-tower-shriek-data). -/
def deriveMap {T T' : Scheme.{u}} {F G : S l E T ⥤ S l E T'}
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex a (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- The finite open adjunction, in the tensor-pullback coordinates fixed above.
Source: blueprint clause (2c), constant-section normalization
(blueprint: def-sp-tower-shriek-data). -/
def finiteOpenAdjunction (b : Base l E) {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (n : ℕ) :
    sfIntrinsicExtensionByZero j (R l E n) ⊣ proEtaleConstantRingPullback (R l E n) j :=
  (sfIntrinsicOpenAdjunction (R l E n) j).ofNatIsoRight
    (openSquarePullbackModel (R l E n) j).symm

/-- The exact open operation on strict systems, with its actual termwise adjunction.
The two ordinary evaluation equations fix the adjunction, hence do not posit a lift
of any family of derived maps. Source: blueprint clauses (1) and (2c)
(blueprint: def-sp-tower-shriek-data). -/
structure Open (b : Base l E) {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (g : Geometry l E b j) where
  extension : S l E U ⥤ S l E T
  [additive : extension.Additive]
  [limits : PreservesFiniteLimits extension]
  [colimits : PreservesFiniteColimits extension]
  ordinaryAdjunction : extension ⊣ g.pull
  evaluation : ∀ n : ℕ, extension ⋙ ev l E T n ≅
    ev l E U n ⋙ sfIntrinsicExtensionByZero j (R l E n)
  ordinaryPullEvaluation : ∀ n : ℕ, g.pull ⋙ ev l E U n ≅
    ev l E T n ⋙ proEtaleConstantRingPullback (R l E n) j
  ordinaryPullEvaluation_eq : ∀ n : ℕ,
    HEq (ordinaryPullEvaluation n) (g.generic.ordinaryPullEvaluation n)
  unit_evaluation : ∀ (n : ℕ) (M : S l E U),
    (ev l E U n).map (ordinaryAdjunction.unit.app M) ≫
        (ordinaryPullEvaluation n).hom.app (extension.obj M) ≫
        (proEtaleConstantRingPullback (R l E n) j).map ((evaluation n).hom.app M) =
      (finiteOpenAdjunction l E b j n).unit.app ((ev l E U n).obj M)
  counit_evaluation : ∀ (n : ℕ) (M : S l E T),
    (evaluation n).inv.app (g.pull.obj M) ≫
        (ev l E T n).map (ordinaryAdjunction.counit.app M) =
      (sfIntrinsicExtensionByZero j (R l E n)).map
          ((ordinaryPullEvaluation n).hom.app M) ≫
        (finiteOpenAdjunction l E b j n).counit.app ((ev l E T n).obj M)
  derivedAdjunction : extension.mapDerivedCategory ⊣ pull l E b g
  unit_termwise : derivedAdjunction.unit =
    (Functor.mapDerivedCategoryIdIso _).inv ≫
      deriveMap l E ordinaryAdjunction.unit ≫
      (Functor.mapDerivedCategoryCompIso extension g.pull).inv
  counit_termwise : derivedAdjunction.counit =
    (Functor.mapDerivedCategoryCompIso g.pull extension).hom ≫
      deriveMap l E ordinaryAdjunction.counit ≫
      (Functor.mapDerivedCategoryIdIso _).hom

attribute [instance] Open.additive Open.limits Open.colimits

/-- Exact derived open extension, on unbounded tower complexes.
Source: blueprint clause (1) (blueprint: def-sp-tower-shriek-data). -/
abbrev openD (b : Base l E) {U T : Scheme.{u}} {j : U ⟶ T} [IsOpenImmersion j]
    {g : Geometry l E b j} (o : Open l E b j g) := o.extension.mapDerivedCategory

/-- Its natural finite evaluation is termwise localization of the ordinary comparison.
Source: blueprint clause (1) (blueprint: def-sp-tower-shriek-data). -/
def openEvaluation (b : Base l E) {U T : Scheme.{u}} {j : U ⟶ T}
    [IsOpenImmersion j] {g : Geometry l E b j} (o : Open l E b j g) (n : ℕ) :
    openD l E b o ⋙ Ev l E T n ≅
      Ev l E U n ⋙ sfIntrinsicDerivedOpen (R l E n) j := by
  letI : Finite (R l E n) := b.finite n
  letI := sfIntrinsicExtensionByZero_additive j (R l E n)
  letI := sfIntrinsicExtensionByZero_preservesFiniteLimits j (R l E n)
  letI := sfIntrinsicExtensionByZero_preservesFiniteColimits j (R l E n)
  exact Functor.mapDerivedCategoryCompIso o.extension (ev l E T n) ≪≫
    Functor.mapDerivedCategoryNatIso (o.evaluation n) ≪≫
    (Functor.mapDerivedCategoryCompIso (ev l E U n)
      (sfIntrinsicExtensionByZero j (R l E n))).symm

/-- Actual geometric operations and canonical comparisons on the fixed sequence sites.
Composition is fixed by its finite comparisons and by the underlying ordinary sheaf
operations; open projection and base change are fixed as adjunction mates below.
Source: blueprint clause (2), specified maps (blueprint: def-sp-tower-shriek-data). -/
structure Operations (b : Base l E) where
  geometry : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Geometry l E b f
  openOp : ∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j],
    Open l E b j (geometry j)
  ordinaryComp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    (geometry g).pull ⋙ (geometry f).pull ≅ (geometry (f ≫ g)).pull
  comp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    pull l E b (geometry g) ⋙ pull l E b (geometry f) ≅
      pull l E b (geometry (f ≫ g))
  comp_termwise : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    comp f g = Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (ordinaryComp f g)
  comp_evaluation : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (K : D l E Z),
    (Ev l E X n).map ((comp f g).hom.app K) ≫
        ((geometry (f ≫ g)).pullEvaluation n).hom.app K =
      ((geometry f).pullEvaluation n).hom.app ((pull l E b (geometry g)).obj K) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) f).map
          (((geometry g).pullEvaluation n).hom.app K) ≫
        (proEtaleConstantRingPullbackComposition f g (R l E n)).hom.app
          ((Ev l E Z n).obj K)
  openTensor : ∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : D l E U) (L : D l E T),
    (tensor l E b T).obj ((openD l E b (openOp j)).obj K, L) ≅
      (openD l E b (openOp j)).obj
        ((tensor l E b U).obj (K, (pull l E b (geometry j)).obj L))
  openTensor_mate : ∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : D l E U) (L : D l E T),
    ((openOp j).derivedAdjunction.homEquiv _ _) ((openTensor j K L).inv) =
      (tensor l E b U).map
          (Prod.mkHom ((openOp j).derivedAdjunction.unit.app K) (𝟙 _)) ≫
        ((geometry j).tensorPullback).inv.app
          ((openD l E b (openOp j)).obj K, L)

/-- Compactly supported total direct image for the chosen compactification.
On bounded-below inputs this is Rp_* after the exact termwise j_!.
Source: blueprint clause (1) (blueprint: def-sp-tower-shriek-data). -/
abbrev F (b : Base l E) (o : Operations l E b) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  openD l E b (o.openOp c.i) ⋙ push l E b (o.geometry c.g)

/-- The canonical projection arrow: proper counit transpose, open projection,
then pullback composition. It exists before any Tor or origin hypotheses.
Source: blueprint clause (2a), specified compactification projection
(blueprint: def-sp-tower-shriek-data). -/
def projection (b : Base l E) (o : Operations l E b) {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) (K : D l E X) (L : D l E Y) :
    (tensor l E b Y).obj ((F l E b o c).obj K, L) ⟶
      (F l E b o c).obj ((tensor l E b X).obj
        (K, (pull l E b (o.geometry f)).obj L)) :=
  ((adjunction l E b (o.geometry c.g)).homEquiv _ _)
      (((o.geometry c.g).tensorPullback).hom.app ((F l E b o c).obj K, L) ≫
        (tensor l E b c.Z).map (Prod.mkHom
          ((adjunction l E b (o.geometry c.g)).counit.app
            ((openD l E b (o.openOp c.i)).obj K)) (𝟙 _))) ≫
    (push l E b (o.geometry c.g)).map
      ((o.openTensor c.i K ((pull l E b (o.geometry c.g)).obj L)).hom ≫
        (openD l E b (o.openOp c.i)).map ((tensor l E b X).map
          (Prod.mkHom (𝟙 K) ((o.comp c.i c.g).hom.app L ≫
            (eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h)) c.comm.symm)).hom.app L))))

/-- The pullback-square comparison formed from the specified termwise composition maps.
Source: blueprint clause (2b), geometric exchange (blueprint: def-sp-tower-shriek-data). -/
def square (b : Base l E) (o : Operations l E b) {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (w : g' ≫ f = f' ≫ g) :
    pull l E b (o.geometry g) ⋙ pull l E b (o.geometry f') ≅
      pull l E b (o.geometry f) ⋙ pull l E b (o.geometry g') :=
  o.comp f' g ≪≫
    eqToIso (congrArg (fun h ↦ pull l E b (o.geometry h)) w.symm) ≪≫
    (o.comp g' f).symm

/-- The inverse open exchange as a specified counit transpose of the square comparison.
Source: blueprint clause (2b), open-adjunction mate
(blueprint: def-sp-tower-shriek-data). -/
def openMate (b : Base l E) (o : Operations l E b) {U' U T' T : Scheme.{u}}
    (h : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : h ≫ j = j' ≫ g)
    (K : D l E U) :
    (openD l E b (o.openOp j')).obj ((pull l E b (o.geometry h)).obj K) ⟶
      (pull l E b (o.geometry g)).obj ((openD l E b (o.openOp j)).obj K) :=
  ((o.openOp j').derivedAdjunction.homEquiv _ _).symm
    ((pull l E b (o.geometry h)).map ((o.openOp j).derivedAdjunction.unit.app K) ≫
      (square l E b o h j' j g w).inv.app ((openD l E b (o.openOp j)).obj K))

/-- Base change of exact extension by zero, with its inverse fixed by the open mate.
Source: blueprint clause (2b) (blueprint: def-sp-tower-shriek-data). -/
structure OpenExchange (b : Base l E) (o : Operations l E b) where
  exchange : ∀ {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (_sq : IsPullback h j' j g),
    openD l E b (o.openOp j) ⋙ pull l E b (o.geometry g) ≅
      pull l E b (o.geometry h) ⋙ openD l E b (o.openOp j')
  mate : ∀ {U' U T' T : Scheme.{u}} (h : U' ⟶ U) (j' : U' ⟶ T')
    (j : U ⟶ T) (g : T' ⟶ T) [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (K : D l E U),
    (exchange h j' j g sq).inv.app K = openMate l E b o h j' j g sq.w K

/-- Compact-support exchange: the proper adjunction mate followed by open base change.
Source: blueprint clause (2b), specified formula
(blueprint: def-sp-tower-shriek-data). -/
def exchange (b : Base l E) (o : Operations l E b) (x : OpenExchange l E b o)
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback h f' f g) (c : Compactification f) :
    F l E b o c ⋙ pull l E b (o.geometry g) ⟶
      pull l E b (o.geometry h) ⋙ F l E b o (c.ofIsPullback sq) :=
  CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData
    (openD l E b (o.openOp c.i))
    (openD l E b (o.openOp (c.ofIsPullback sq).i))
    (pull l E b (o.geometry c.g)) (push l E b (o.geometry c.g))
    (adjunction l E b (o.geometry c.g))
    (pull l E b (o.geometry (c.ofIsPullback sq).g))
    (push l E b (o.geometry (c.ofIsPullback sq).g))
    (adjunction l E b (o.geometry (c.ofIsPullback sq).g))
    (pull l E b (o.geometry g)) (pull l E b (o.geometry h))
    (pull l E b (o.geometry (pullback.fst c.g g)))
    (square l E b o (pullback.fst c.g g) (c.ofIsPullback sq).g c.g g
      (pullback.condition))
    (x.exchange h (c.ofIsPullback sq).i c.i (pullback.fst c.g g)
      (c.isPullback_i_ofIsPullback sq))

/-- Finite-level compact support in the same constant-ring coordinates.
Source: blueprint clause (1) (blueprint: def-sp-tower-shriek-data). -/
abbrev finiteF (b : Base l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) :=
  sfIntrinsicDerivedOpen (R l E n) c.i ⋙
    (proEtaleConstantRingPushforward (R l E n) c.g).rightDerivedFunctor

/-- Natural level comparison of the actual compactification composite.
Source: blueprint clause (1) (blueprint: def-sp-tower-shriek-data). -/
def Fcomparison (b : Base l E) (o : Operations l E b) {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    F l E b o c ⋙ Ev l E Y n ≅ Ev l E X n ⋙ finiteF l E b c n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((o.geometry c.g).pushEvaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openEvaluation l E b (o.openOp c.i) n) _ ≪≫
    Functor.associator _ _ _

/-- A retained origin at one level, using the dependency's fixed-scalar witness.
This specifies a witness independently for each n; it imposes no transition equations.
Source: blueprint clauses (2a)--(2b) (blueprint: def-sp-tower-shriek-data). -/
structure Origin (b : Base l E) (T : Scheme.{u}) (n : ℕ) (K : D l E T) where
  level : DerivedCategory.Plus
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))))
  realization : (sfIntrinsicModuleEquivalence T (R l E n)).functor.mapDerivedCategory.obj
    level.obj ≅ (Ev l E T n).obj K
  witness : FixedEtaleOriginWitness T (ULift.{u + 1} (R l E n)) level

/-- Equality transport of quotient coefficients, induced by the identity on O_E.
This is a real functor defined by equality elimination; no equivalence is chosen.
Source: blueprint coefficient equation R_n = A_(E,en)
(blueprint: def-sp-tower-shriek-data). -/
def quotientTransport (T : Scheme.{u})
    (I J : Ideal (Padic.coefficientExtensionIntegers l E)) (h : I = J) :
    proEtaleDerivedCategory T (Padic.coefficientExtensionIntegers l E ⧸ I) ⥤
      proEtaleDerivedCategory T (Padic.coefficientExtensionIntegers l E ⧸ J) :=
  Eq.ndrec (motive := fun J : Ideal (Padic.coefficientExtensionIntegers l E) ↦
    proEtaleDerivedCategory T (Padic.coefficientExtensionIntegers l E ⧸ I) ⥤
      proEtaleDerivedCategory T (Padic.coefficientExtensionIntegers l E ⧸ J)) (𝟭 _) h

/-- Apply the recorded finite-Tor constructibility predicate after the canonical
ell-power/uniformizer-power quotient identification, retaining every positive level.
Source: blueprint clause (2a); definition-constructible-sheaves
(blueprint: def-sp-tower-shriek-data). -/
def GoodLevel (b : Base l E) (T : Scheme.{u}) (n : ℕ) (K : D l E T) : Prop :=
  finiteTorConstructible l E (b.ramification * (n + 1))
    (Nat.mul_pos b.ramification_positive (Nat.succ_pos n)) T
    ((quotientTransport l E T (spEllIdeal l E ^ (n + 1))
      (Padic.coefficientExtensionIdeal l E (b.ramification * (n + 1)))
      (b.ideals n)).obj ((Ev l E T n).obj K))

/-- Exact closed direct image and the open--closed distinguished triangle.
The first two arrows are the termwise localized counit and unit. Exact evaluation
carries this same triangle to a distinguished finite triangle, including its boundary.
Source: blueprint clause (2c), Stacks 09AH and 09BM
(blueprint: def-sp-tower-shriek-data). -/
structure LocalizationData (b : Base l E) (o : Operations l E b)
    {Z U T : Scheme.{u}} (i : Z ⟶ T) (a : U ⟶ T)
    [IsClosedImmersion i] [IsOpenImmersion a] [QuasiCompact a]
    (complement : Set.range a = (Set.range i)ᶜ) where
  [closedLimits : PreservesFiniteLimits (o.geometry i).push]
  [closedColimits : PreservesFiniteColimits (o.geometry i).push]
  triangle : ∀ C : DerivedCategory.Plus (S l E T),
    ∃ δ : ((pull l E b (o.geometry i) ⋙ (o.geometry i).push.mapDerivedCategory).obj
        C.obj ⟶
      ((pull l E b (o.geometry a) ⋙ openD l E b (o.openOp a)).obj C.obj)⟦(1 : ℤ)⟧),
    Triangle.mk ((o.openOp a).derivedAdjunction.counit.app C.obj)
      (((Functor.mapDerivedCategoryIdIso _).inv ≫
        deriveMap l E (o.geometry i).ordinaryAdjunction.unit ≫
        (Functor.mapDerivedCategoryCompIso (o.geometry i).pull
          (o.geometry i).push).inv).app C.obj) δ ∈ distTriang (D l E T) ∧
    ∀ n : ℕ, (Ev l E T n).mapTriangle.obj
      (Triangle.mk ((o.openOp a).derivedAdjunction.counit.app C.obj)
        (((Functor.mapDerivedCategoryIdIso _).inv ≫
          deriveMap l E (o.geometry i).ordinaryAdjunction.unit ≫
          (Functor.mapDerivedCategoryCompIso (o.geometry i).pull
            (o.geometry i).push).inv).app C.obj) δ) ∈
      distTriang (proEtaleDerivedCategory T (R l E n))

/-- The three clauses, including the precise domains of the invertibility claims.
Origin witnesses occur only in the testing hypotheses, never in the construction of
operations or mates. Source: blueprint clauses (1)--(3)
(blueprint: def-sp-tower-shriek-data). -/
structure Laws (b : Base l E) (o : Operations l E b) (x : OpenExchange l E b o) : Prop where
  bounded : ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (C : DerivedCategory.Plus (S l E X)),
    ∃ m : ℤ, ((F l E b o c).obj C.obj).IsGE m
  projection_iso : ∀ (k : FiniteFieldDatum.{u}) (_ : l ≠ k.p)
    (X Y : Over (Spec (CommRingCat.of k.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left)
    (K : DerivedCategory.Plus (S l E X.left))
    (L : DerivedCategory.Plus (S l E Y.left)),
    (∀ n : ℕ, Origin l E b X.left n K.obj) →
    (∀ n : ℕ, Origin l E b Y.left n L.obj) →
    (∀ n : ℕ, GoodLevel l E b X.left n K.obj) →
    (∀ n : ℕ, GoodLevel l E b Y.left n L.obj) →
    IsIso (projection l E b o c K.obj L.obj)
  exchange_iso : ∀ {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback h f' f g) (c : Compactification f)
    (C : DerivedCategory.Plus (S l E X)),
    (∀ n : ℕ, Origin l E b X n C.obj) →
    IsIso ((exchange l E b o x sq c).app C.obj)
  localization : ∀ {Z U T : Scheme.{u}} (i : Z ⟶ T) (a : U ⟶ T)
    [IsClosedImmersion i] [IsOpenImmersion a] [QuasiCompact a]
    (complement : Set.range a = (Set.range i)ᶜ),
    Nonempty (LocalizationData l E b o i a complement)
  detects : ∀ (T : Scheme.{u}) {K L : D l E T} (v : K ⟶ L),
    IsIso v ↔ ∀ n : ℕ, IsIso ((Ev l E T n).map v)

end AlgebraicGeometry.ProEtale.SpTowerShriek

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
