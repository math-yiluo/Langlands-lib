/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.CategoryTheory.SmoothBaseChange.TowerDerivedEvaluationNormalization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement

public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Towers and the derived completion: definitions

Source: literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/det-pbc-complete-derived-completion.md
(blueprint: proposition-proper-base-change-complete-integral).

The natural index `n` denotes the positive exponent `n + 1`. The reduction tower is
constructed as a cone in complexes of towers. Its source has transition multiplication
by the uniformizer and its target is constant. Thus its transition is precisely
`(π, 1)`, including on complexes with torsion. Localization defines the derived
reduction functor; no choice of unrelated levelwise derived arrows is made.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.modulesDerived
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts

namespace CompleteDerivedCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The category of inverse towers of integral modules; level `n` means exponent `n+1`.
Source: blueprint Notation 1 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev Tow (T : Scheme.{u}) := ℕᵒᵖ ⥤ AdicCompletion.Modules l E T

/-- Grothendieckness of the actual tower category, with its inherited abelian structure.
Source: blueprint Assertion 1 (blueprint: proposition-proper-base-change-complete-integral).
Proof: identify internal modules with sheaves of modules, then use the small-diagram
Grothendieck theorem. Kernels, cokernels and filtered colimits are computed levelwise;
the coproduct of the free diagrams on a generator is a generator. -/
@[instance] theorem towerGrothendieck (T : Scheme.{u}) :
    IsGrothendieckAbelian.{u+1} (Tow l E T) := by
  let A := AdicCompletion.Modules l E T
  let : IsGrothendieckAbelian.{u+1} A := inferInstance
  let : HasColimitsOfSize.{u+1, u+1} A := inferInstance
  let : HasColimitsOfSize.{0, u+1} A := hasColimitsOfSizeShrink.{0, u+1, u+1, u+1} A
  change IsGrothendieckAbelian.{u+1} (ℕᵒᵖ ⥤ A)
  have ht (K : Type (u+1)) [SmallCategory K] : IsGrothendieckAbelian.{u+1} (K ⥤ A) := by
    let (_a _b : K) : HasColimitsOfShape (Discrete (_a ⟶ _b)) A :=
      HasColimitsOfShape.of_small.{u+1, u+1} A _
    let : HasColimitsOfSize.{0, u+1} (K ⥤ A) := inferInstance
    let : HasColimitsOfShape (Discrete K) (K ⥤ A) :=
      HasColimitsOfShape.of_small.{u+1, u+1} (K ⥤ A) _
    let G := separator A
    have hG := isSeparator_separator A
    have hS : ObjectProperty.IsSeparating
        (.ofObj fun j : K ↦ (evaluationLeftAdjoint A j).obj G) := by
      intro F F' f g hfg
      apply NatTrans.ext
      funext j
      apply hG.def
      intro a
      let adj := evaluationAdjunctionRight A j
      apply (adj.homEquiv G F').symm.injective
      have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
      exact (adj.homEquiv_naturality_right_symm a f).trans
        (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
    let : HasCoproduct (fun j : K ↦ (evaluationLeftAdjoint A j).obj G) :=
      HasColimitsOfShape.has_colimit _
    let : HasSeparator (K ⥤ A) :=
      ⟨∐ (fun j : K ↦ (evaluationLeftAdjoint A j).obj G), hS.isSeparator_coproduct⟩
    let : HasFilteredColimitsOfSize.{u+1, u+1} (K ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
    let : AB5OfSize.{u+1, u+1} (K ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
    exact {}
  let : IsGrothendieckAbelian.{u+1} (AsSmall.{u+1} ℕᵒᵖ ⥤ A) := ht (AsSmall.{u+1} ℕᵒᵖ)
  exact IsGrothendieckAbelian.of_equivalence
    (Equivalence.congrLeft (AsSmall.equiv : ℕᵒᵖ ≌ AsSmall.{u+1} ℕᵒᵖ).symm)

/-- The unbounded derived category of towers, with small Hom universe `u+1`.
Source: blueprint Notation 1 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev DTow (T : Scheme.{u}) := DerivedCategory.{u+1} (Tow l E T)

/-- Exact evaluation of module towers.
Source: blueprint Notation 1 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev ev (T : Scheme.{u}) (n : ℕ) :=
  (evaluation ℕᵒᵖ (AdicCompletion.Modules l E T)).obj (op n)

/-- Evaluation on the derived category of towers, induced by exact evaluation.
Source: blueprint Assertion 2 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev dev (T : Scheme.{u}) (n : ℕ) := (ev l E T n).mapDerivedCategory

/-- The constant tower functor.
Source: blueprint Notation 1 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev constant (T : Scheme.{u}) := Functor.const ℕᵒᵖ (C := AdicCompletion.Modules l E T)

/-- The constant functor on unbounded derived categories.
Source: blueprint Notation 1 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev dconstant (T : Scheme.{u}) := (constant l E T).mapDerivedCategory

/-- The ordinary inverse limit of module towers, right adjoint to the constant functor.
Source: blueprint Notation 1 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev inverseLimit (T : Scheme.{u}) : Tow l E T ⥤ AdicCompletion.Modules l E T := lim

/-- Additivity of ordinary inverse limit from the additive constant-limit adjunction.
Source: blueprint Notation 1 (blueprint: proposition-proper-base-change-complete-integral).
Proof: the constant functor is additive, and an additive left adjoint has an additive
right adjoint. Apply this to Mathlib's constant-limit adjunction. -/
@[instance] theorem inverseLimit_additive (T : Scheme.{u}) :
    (inverseLimit l E T).Additive := by
  exact (constLimAdj : constant l E T ⊣ inverseLimit l E T).right_adjoint_additive

/-- The total right derived inverse-limit functor, constructed by K-injective resolutions.
Source: blueprint Notation 1 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev rlim (T : Scheme.{u}) := (inverseLimit l E T).rightDerivedFunctor

/-- The canonical derived constant-limit adjunction.
Source: blueprint Notation 4 (blueprint: proposition-proper-base-change-complete-integral). -/
def constantLimitAdjunction (T : Scheme.{u}) : dconstant l E T ⊣ rlim l E T :=
  (constLimAdj : constant l E T ⊣ inverseLimit l E T).mapDerivedCategoryRightDerivedAdjunction

/-- Levelwise ordinary pullback of module towers.
Source: blueprint Notation 2 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev pull {T T' : Scheme.{u}} (f : T' ⟶ T) : Tow l E T ⥤ Tow l E T' :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)

/-- Levelwise ordinary pushforward of module towers.
Source: blueprint Notation 2 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev push {T T' : Scheme.{u}} (f : T' ⟶ T) : Tow l E T' ⥤ Tow l E T :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f)

/-- Exact module pullback on the derived category; no resolution is needed.
Source: blueprint Notation 2 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev dpullModule {T T' : Scheme.{u}} (f : T' ⟶ T) :=
  (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f).mapDerivedCategory

/-- The existing total right derived module direct image.
Source: blueprint Assertion 3 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev rpushModule {T T' : Scheme.{u}} (f : T' ⟶ T) :=
  (CondensedRing.lowerStar (DerivedNakayama.integerRing l E) f).rightDerivedFunctor

/-- Exact pullback on derived towers.
Source: blueprint Notation 2 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev dpull {T T' : Scheme.{u}} (f : T' ⟶ T) := (pull l E f).mapDerivedCategory

/-- Total right derived pushforward on the derived category of towers.
Source: blueprint Notation 2 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev rpush {T T' : Scheme.{u}} (f : T' ⟶ T) := (push l E f).rightDerivedFunctor

/-- The canonical exact-pullback/derived-pushforward module adjunction.
Source: blueprint Assertion 3 (blueprint: proposition-proper-base-change-complete-integral). -/
def moduleAdjunction {T T' : Scheme.{u}} (f : T' ⟶ T) :
    dpullModule l E f ⊣ rpushModule l E f :=
  (CondensedRing.upperStarLowerStarAdjunction (DerivedNakayama.integerRing l E) f)
    |>.mapDerivedCategoryRightDerivedAdjunction

/-- The canonical exact-pullback/derived-pushforward tower adjunction.
Source: blueprint Assertion 3 (blueprint: proposition-proper-base-change-complete-integral). -/
def towerAdjunction {T T' : Scheme.{u}} (f : T' ⟶ T) : dpull l E f ⊣ rpush l E f :=
  ((CondensedRing.upperStarLowerStarAdjunction (DerivedNakayama.integerRing l E) f)
    |>.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction

/-- The canonical pullback-evaluation comparison from exact localization.
Source: blueprint Assertion 3 (blueprint: proposition-proper-base-change-complete-integral). -/
def pullEvaluation {T T' : Scheme.{u}} (f : T' ⟶ T) (n : ℕ) :
    dpull l E f ⋙ dev l E T' n ≅ dev l E T n ⋙ dpullModule l E f :=
  towerDerivedEvaluationInterchange
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f) (op n)

/-- Multiplication by the specified coefficient uniformizer on the regular module.
This choice is determined uniquely: the first property of the cited resolution theorem
specifies its value on every section and every point, so it is not a choice from a bare
existence assertion. Source: blueprint Notation 3 and derived Nakayama resolution
(blueprint: proposition-proper-base-change-complete-integral). -/
def uniformizer : End (Mod.regular (DerivedNakayama.integerRing l E)) :=
  (DerivedNakayama.derived_nakayama_resolution l E).choose

/-- Scalar multiplication by the uniformizer on integral module sheaves.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev scalar (T : Scheme.{u}) :=
  DerivedNakayama.scalarOnModules l E T (uniformizer l E)

/-- The source of the reduction power map: the same module at every level with
uniformizer transitions. Source: blueprint Notation 3
(blueprint: proposition-proper-base-change-complete-integral). -/
def scalarTower (T : Scheme.{u}) : AdicCompletion.Modules l E T ⥤ Tow l E T :=
  (Functor.ofOpSequence (X := fun _ : ℕ ↦ 𝟭 (AdicCompletion.Modules l E T))
    (fun _ ↦ scalar l E T)).flip

/-- The scalar tower functor is additive.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral).
Proof: every component of its map is the original module morphism; addition is
levelwise in a functor category. -/
@[instance] theorem scalarTower_additive (T : Scheme.{u}) : (scalarTower l E T).Additive := by
  refine ⟨?_⟩
  intro M N f g
  apply NatTrans.ext
  funext n
  rfl

/-- The power components commute with the scalar-tower transition.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral).
Proof: at level n the equation is π^(n+2) = π · π^(n+1), the power identity. -/
theorem powerMap_condition (T : Scheme.{u}) (M : AdicCompletion.Modules l E T) (n : ℕ) :
    ((scalarTower l E T).obj M).map (homOfLE (Nat.le_succ n)).op ≫
        End.asHom ((End.of ((scalar l E T).app M)) ^ (n+1)) =
      End.asHom ((End.of ((scalar l E T).app M)) ^ (n+1+1)) ≫
        ((constant l E T).obj M).map (homOfLE (Nat.le_succ n)).op := by
  change ((Functor.ofOpSequence (X := fun _ : ℕ ↦ 𝟭 (AdicCompletion.Modules l E T))
    (fun _ ↦ scalar l E T)).map (homOfLE (Nat.le_succ n)).op).app M ≫
      End.asHom ((End.of ((scalar l E T).app M)) ^ (n+1)) = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  change End.asHom ((End.of ((scalar l E T).app M)) ^ (n+1) *
    End.of ((scalar l E T).app M)) = _
  rw [← pow_succ]
  rfl

/-- The power map on one module, as an actual morphism of towers.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral). -/
def powerMapApp (T : Scheme.{u}) (M : AdicCompletion.Modules l E T) :
    (scalarTower l E T).obj M ⟶ (constant l E T).obj M :=
  NatTrans.ofOpSequence
    (fun n ↦ End.asHom ((End.of ((scalar l E T).app M)) ^ (n+1)))
    (powerMap_condition l E T M)

/-- Naturality of the power map in the module.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral).
Proof: naturality of the scalar action implies naturality of all its powers. -/
theorem powerMap_naturality (T : Scheme.{u})
    {M N : AdicCompletion.Modules l E T} (f : M ⟶ N) :
    (scalarTower l E T).map f ≫ powerMapApp l E T N =
      powerMapApp l E T M ≫ (constant l E T).map f := by
  apply NatTrans.ext
  funext n
  change f ≫ End.asHom ((End.of ((scalar l E T).app N)) ^ (n.unop+1)) =
    End.asHom ((End.of ((scalar l E T).app M)) ^ (n.unop+1)) ≫ f
  have h (k : ℕ) :
      f ≫ End.asHom ((End.of ((scalar l E T).app N)) ^ k) =
        End.asHom ((End.of ((scalar l E T).app M)) ^ k) ≫ f := by
    induction k with
    | zero => simp
    | succ k ih =>
      change f ≫ ((scalar l E T).app N ≫
        End.asHom ((End.of ((scalar l E T).app N)) ^ k)) =
          ((scalar l E T).app M ≫
            End.asHom ((End.of ((scalar l E T).app M)) ^ k)) ≫ f
      have hs : f ≫ (scalar l E T).app N = (scalar l E T).app M ≫ f :=
        (scalar l E T).naturality f
      rw [← Category.assoc, hs, Category.assoc, ih, Category.assoc]
  exact h _

/-- The power map from the scalar tower to the constant tower.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral). -/
def powerMap (T : Scheme.{u}) : scalarTower l E T ⟶ constant l E T where
  app M := powerMapApp l E T M
  naturality _ _ f := powerMap_naturality l E T f

/-- The strict reduction power map on complexes of towers.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev complexPowerMap (T : Scheme.{u}) :=
  NatTrans.mapHomologicalComplex (powerMap l E T) (.up ℤ)

/-- Identity maps induce the identity on the strict cone tower.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral).
Proof: both functors in the defining square send the identity to the identity;
apply the standard mapping-cone identity formula. -/
theorem strictRed_map_id (T : Scheme.{u})
    (M : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    CochainComplex.mappingCone.map ((complexPowerMap l E T).app M)
      ((complexPowerMap l E T).app M)
      (((scalarTower l E T).mapHomologicalComplex (.up ℤ)).map (𝟙 M))
      (((constant l E T).mapHomologicalComplex (.up ℤ)).map (𝟙 M))
      ((complexPowerMap l E T).naturality (𝟙 M)).symm = 𝟙 _ := by
  exact CochainComplex.mappingCone.map_id _

/-- The strict reduction functor, with cone transitions (π,1), on arbitrary complexes.
The cone is taken in complexes of towers, so it includes all coherence automatically.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral). -/
def strictRed (T : Scheme.{u}) :
    CochainComplex (AdicCompletion.Modules l E T) ℤ ⥤ CochainComplex (Tow l E T) ℤ where
  obj M := CochainComplex.mappingCone ((complexPowerMap l E T).app M)
  map {M N} f := CochainComplex.mappingCone.map _ _
    (((scalarTower l E T).mapHomologicalComplex (.up ℤ)).map f)
    (((constant l E T).mapHomologicalComplex (.up ℤ)).map f)
    ((complexPowerMap l E T).naturality f).symm
  map_id M := strictRed_map_id l E T M
  map_comp f g := by
    simp only [Functor.map_comp]
    exact CochainComplex.mappingCone.map_comp _ _ _ _ _
      ((complexPowerMap l E T).naturality f).symm _ _
      ((complexPowerMap l E T).naturality g).symm

/-- Reduction inverts quasi-isomorphisms before passage to derived towers.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral).
Proof: exact evaluation identifies the cone at n with Cone(π^(n+1)); a quasi-isomorphism
on both sides of its defining square induces a quasi-isomorphism of cones. Detect
quasi-isomorphisms in the tower category levelwise. -/
theorem strictRed_inverts (T : Scheme.{u}) :
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)).IsInvertedBy
      (strictRed l E T ⋙ DerivedCategory.Q) := by
  have : PreservesFiniteLimits (scalarTower l E T) :=
    preservesFiniteLimits_of_evaluation _ (fun n ↦ by
      change PreservesFiniteLimits (𝟭 (AdicCompletion.Modules l E T))
      infer_instance)
  have : PreservesFiniteColimits (scalarTower l E T) :=
    preservesFiniteColimits_of_evaluation _ (fun n ↦ by
      change PreservesFiniteColimits (𝟭 (AdicCompletion.Modules l E T))
      infer_instance)
  intro M N f hf
  let : QuasiIso f := hf
  let a := ((scalarTower l E T).mapHomologicalComplex (.up ℤ)).map f
  let b := ((constant l E T).mapHomologicalComplex (.up ℤ)).map f
  have : QuasiIso a := inferInstance
  have : QuasiIso b := inferInstance
  let t := DerivedCategory.Q.mapTriangle.map
    (CochainComplex.mappingCone.triangleMap
      ((complexPowerMap l E T).app M) ((complexPowerMap l E T).app N)
      a b ((complexPowerMap l E T).naturality f).symm)
  exact Pretriangulated.isIso₃_of_isIso₁₂ t
    (DerivedCategory.mappingCone_triangle_distinguished _)
    (DerivedCategory.mappingCone_triangle_distinguished _)
    (by change IsIso (DerivedCategory.Q.map a); infer_instance)
    (by change IsIso (DerivedCategory.Q.map b); infer_instance)

/-- The reduction functor on the unbounded derived category of integral modules.
It is the actual localization of the cone tower, rather than a family of derived cones.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral). -/
def red (T : Scheme.{u}) : DerivedCategory (AdicCompletion.Modules l E T) ⥤ DTow l E T :=
  Localization.lift (strictRed l E T ⋙ DerivedCategory.Q) (strictRed_inverts l E T)
    DerivedCategory.Q

/-- The canonical factorization of the strict cone tower through its localization.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral). -/
def redFactors (T : Scheme.{u}) :
    DerivedCategory.Q ⋙ red l E T ≅ strictRed l E T ⋙ DerivedCategory.Q :=
  Localization.fac _ (strictRed_inverts l E T) DerivedCategory.Q

/-- Register the explicit localization comparison for the reduction tower.
Source: blueprint Notation 3 (blueprint: proposition-proper-base-change-complete-integral). -/
instance red_lifting (T : Scheme.{u}) :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ))
      (strictRed l E T ⋙ DerivedCategory.Q) (red l E T) :=
  ⟨redFactors l E T⟩

/-- The strict degree-zero cone inclusion is natural.
Source: blueprint Notation 4 (blueprint: proposition-proper-base-change-complete-integral).
Proof: the second square map in the definition of strictRed is the constant functor's
map. Naturality is the inr equation for the induced cone map. -/
theorem strictAugmentation_naturality (T : Scheme.{u})
    {M N : CochainComplex (AdicCompletion.Modules l E T) ℤ} (f : M ⟶ N) :
    ((constant l E T).mapHomologicalComplex (.up ℤ)).map f ≫
        CochainComplex.mappingCone.inr ((complexPowerMap l E T).app N) =
      CochainComplex.mappingCone.inr ((complexPowerMap l E T).app M) ≫
        (strictRed l E T).map f := by
  exact (CochainComplex.mappingCone.triangleMap
    ((complexPowerMap l E T).app M) ((complexPowerMap l E T).app N)
    (((scalarTower l E T).mapHomologicalComplex (.up ℤ)).map f)
    (((constant l E T).mapHomologicalComplex (.up ℤ)).map f)
    ((complexPowerMap l E T).naturality f).symm).comm₂.symm

/-- The degree-zero inclusions give a morphism of strict towers of complexes.
Source: blueprint Notation 4 (blueprint: proposition-proper-base-change-complete-integral). -/
def strictAugmentation (T : Scheme.{u}) :
    (constant l E T).mapHomologicalComplex (.up ℤ) ⟶ strictRed l E T where
  app M := CochainComplex.mappingCone.inr ((complexPowerMap l E T).app M)
  naturality _ _ f := strictAugmentation_naturality l E T f

/-- The canonical degree-zero inclusion on derived towers.
Source: blueprint Notation 4 (blueprint: proposition-proper-base-change-complete-integral). -/
def augmentation (T : Scheme.{u}) : dconstant l E T ⟶ red l E T :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E T) (.up ℤ)) _ _
    (dconstant l E T) (red l E T)
    (Functor.whiskerRight (strictAugmentation l E T) DerivedCategory.Q)

/-- Derived completion as Rlim of the strict, localized reduction tower.
Source: blueprint Notation 4 (blueprint: proposition-proper-base-change-complete-integral). -/
def completion (T : Scheme.{u}) := red l E T ⋙ rlim l E T

/-- The canonical completion unit: the constant-limit adjunction unit followed by
Rlim of the degree-zero inclusions. Source: blueprint Notation 4
(blueprint: proposition-proper-base-change-complete-integral). -/
def kappa (T : Scheme.{u}) : 𝟭 (DerivedCategory (AdicCompletion.Modules l E T)) ⟶
    completion l E T :=
  (constantLimitAdjunction l E T).unit ≫
    Functor.whiskerRight (augmentation l E T) (rlim l E T)

/-- The canonical mate of the exact pullback/evaluation comparison.
Source: blueprint Assertion 3 (blueprint: proposition-proper-base-change-complete-integral). -/
def pushEvaluationMap {T T' : Scheme.{u}} (f : T' ⟶ T) (n : ℕ) :
    rpush l E f ⋙ dev l E T n ⟶ dev l E T' n ⋙ rpushModule l E f :=
  (mateEquiv (towerAdjunction l E f) (moduleAdjunction l E f)
    (.mk _ _ _ _ (pullEvaluation l E f n).inv))

/-- The exact-localization comparison between an exact functor and constant towers.
Source: blueprint Assertions 4--5 (blueprint: proposition-proper-base-change-complete-integral). -/
def constantInterchange {T T' : Scheme.{u}}
    (F : AdicCompletion.Modules l E T ⥤ AdicCompletion.Modules l E T')
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    F.mapDerivedCategory ⋙ dconstant l E T' ≅
      dconstant l E T ⋙ ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso F (constant l E T') ≪≫
    Functor.mapDerivedCategoryNatIso (Functor.compConstIso ℕᵒᵖ F) ≪≫
    (Functor.mapDerivedCategoryCompIso (constant l E T)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)).symm

/-- The canonical derived pushforward/limit isomorphism. It is the conjugate of the
constant/pullback comparison under the two composite derived adjunctions, and therefore
has the ordinary limit comparison as its K-injective normalization.
Source: blueprint Assertion 4 (blueprint: proposition-proper-base-change-complete-integral). -/
def pushLimitIso {T T' : Scheme.{u}} (f : T' ⟶ T) :
    rlim l E T' ⋙ rpushModule l E f ≅ rpush l E f ⋙ rlim l E T :=
  conjugateIsoEquiv
    ((moduleAdjunction l E f).comp (constantLimitAdjunction l E T'))
    ((constantLimitAdjunction l E T).comp (towerAdjunction l E f))
    (constantInterchange l E
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)).symm

/-- Total tensor with a constant complex on strict towers, using the pointwise tensor
of module towers and the usual direct-sum total complex.
Source: blueprint Assertion 5 (blueprint: proposition-proper-base-change-complete-integral). -/
def strictTensor (T : Scheme.{u}) (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    CochainComplex (Tow l E T) ℤ ⥤ CochainComplex (Tow l E T) ℤ :=
  ((curriedTensor (Tow l E T)).map₂CochainComplex).flip.obj
    (((constant l E T).mapHomologicalComplex (.up ℤ)).obj P)

/-- Tensoring strict towers with a bounded finite-free complex inverts quasi-isomorphisms.
Source: blueprint Assertion 5 (blueprint: proposition-proper-base-change-complete-integral).
Proof: finite-free terms are flat, and bounded flat complexes are K-flat. Evaluation
computes this tensor levelwise, so its preservation of quasi-isomorphisms follows from
K-flatness at every level and levelwise detection in the tower category. -/
theorem strictTensor_inverts (T : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (_hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (_hf : ∀ j : ℤ, Mod.IsFree (AdicCompletion.ring l E T) (P.X j)) :
    (HomologicalComplex.quasiIso (Tow l E T) (.up ℤ)).IsInvertedBy
      (strictTensor l E T P ⋙ DerivedCategory.Q) := by
  let C : CochainComplex (Tow l E T) ℤ :=
    ((constant l E T).mapHomologicalComplex (.up ℤ)).obj P
  have (N : Tow l E T) : PreservesColimitsOfSize.{0, 0} (tensorRight N) := by
    constructor
    intro J _
    apply preservesColimitsOfShape_of_evaluation
    intro n
    change PreservesColimitsOfShape J
      ((ev l E T n.unop) ⋙ tensorRight (N.obj n))
    infer_instance
  have (N : Tow l E T) : PreservesColimitsOfSize.{0, 0} (tensorLeft N) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N).symm
  have (X₁ X₂ : GradedObject ℤ (Tow l E T)) : GradedObject.HasTensor X₁ X₂ :=
    inferInstance
  have (X₁ X₂ X₃ : GradedObject ℤ (Tow l E T)) :
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
  have (X₁ X₂ X₃ : GradedObject ℤ (Tow l E T)) :
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
  have (X₁ X₂ X₃ X₄ : GradedObject ℤ (Tow l E T)) :
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
  obtain ⟨a, b, ha, hb⟩ := _hb
  let : P.IsStrictlyGE a := ha
  let : P.IsStrictlyLE b := hb
  have : C.IsStrictlyGE a := inferInstance
  have : C.IsStrictlyLE b := inferInstance
  have hflat (j : ℤ) : ObjectProperty.flat (C.X j) := by
    obtain ⟨n, ⟨e⟩⟩ := _hf j
    let e' : C.X j ≅ ⨁ (fun _ : Fin n ↦ (𝟙_ (Tow l E T))) :=
      (constant l E T).mapIso e ≪≫
        (constant l E T).mapBiproduct (fun _ : Fin n ↦ Mod.regular (AdicCompletion.ring l E T))
    apply ObjectProperty.prop_of_iso _ e'.symm
    exact ObjectProperty.prop_of_isLimit _ (biproduct.isLimit _)
      (fun _ ↦ ObjectProperty.prop_unit _)
  have hk := CochainComplex.kFlat_of_bounded_of_flat C a b hflat
  intro X Y f hf
  have : QuasiIso ((strictTensor l E T P).map f) := hk.2 f hf
  change IsIso (DerivedCategory.Q.map ((strictTensor l E T P).map f))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance

/-- The derived tower tensor with a bounded finite-free complex, defined by localization
of the actual total tensor on strict towers.
Source: blueprint Assertion 5 (blueprint: proposition-proper-base-change-complete-integral). -/
def tensorTower (T : Scheme.{u}) (P : CochainComplex (AdicCompletion.Modules l E T) ℤ)
    (hb : ∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b)
    (hf : ∀ j : ℤ, Mod.IsFree (AdicCompletion.ring l E T) (P.X j)) :
    DTow l E T ⥤ DTow l E T :=
  Localization.lift (strictTensor l E T P ⋙ DerivedCategory.Q)
    (strictTensor_inverts l E T P hb hf) DerivedCategory.Q

/-- The derived evaluation transition, including the successor transition and identities.
Source: blueprint Notation 1 (blueprint: proposition-proper-base-change-complete-integral). -/
def transition (T : Scheme.{u}) (n : ℕ) : dev l E T (n+1) ⟶ dev l E T n :=
  towerDerivedEvaluationTransition (AdicCompletion.Modules l E T)
    (homOfLE (Nat.le_succ n)).op

/-- The canonical free diagram left adjoint to evaluation; on level m it is a coproduct
of copies of N indexed by arrows n→m, hence N for m≤n and zero otherwise.
Source: blueprint Assertion 1 (blueprint: proposition-proper-base-change-complete-integral). -/
abbrev freeDiagram (T : Scheme.{u}) (n : ℕ) :=
  evaluationLeftAdjoint (AdicCompletion.Modules l E T) (op n)

end CompleteDerivedCompletion

end AlgebraicGeometry.ProEtale
