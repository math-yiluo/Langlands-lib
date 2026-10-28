import Langlands.AbelianScheme.Tate.WeilPrime
import Langlands.AlgebraicGeometry.Picard.FiniteWeilAlongHomBilinearity
import Mathlib.LinearAlgebra.BilinearMap

/-! # Integral Weil pairings along actual dual-valued homomorphisms -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

private lemma continuous_integralAlongCoordinates {S : Scheme.{u}}
    (G : Grp (Over S)) [IsCommMonObj G.X]
    (T : Over S) (P : ℕ → Prop) (n : GroupScheme.Tate.Index P)
    {C : Type*} [TopologicalSpace C]
    (f : GroupScheme.Tate.Level G T n.val → GroupScheme.Tate.Level G T n.val → C) :
    Continuous (fun z : GroupScheme.Tate.Integral G T P ×
      GroupScheme.Tate.Integral G T P => f (z.1.val n) (z.2.val n)) :=
  (continuous_of_discreteTopology
    (f := fun z : GroupScheme.Tate.Level G T n.val ×
      GroupScheme.Tate.Level G T n.val => f z.1 z.2)).comp
        (((GroupScheme.Tate.continuous_evaluation G T P n).comp continuous_fst).prodMk
          ((GroupScheme.Tate.continuous_evaluation G T P n).comp continuous_snd))

private lemma continuous_primeAlongCoordinates {S : Scheme.{u}}
    (G : Grp (Over S)) [IsCommMonObj G.X]
    (T : Over S) (p : ℕ) [Fact p.Prime] (n : ℕ)
    {C : Type*} [TopologicalSpace C]
    (f : GroupScheme.Tate.Level G T (p ^ n) → GroupScheme.Tate.Level G T (p ^ n) → C) :
    Continuous (fun z : GroupScheme.Tate.PrimeAdic.Integral G T p ×
      GroupScheme.Tate.PrimeAdic.Integral G T p => f (z.1.val n) (z.2.val n)) :=
  (continuous_of_discreteTopology
    (f := fun z : GroupScheme.Tate.Level G T (p ^ n) ×
      GroupScheme.Tate.Level G T (p ^ n) => f z.1 z.2)).comp
        (((GroupScheme.Tate.PrimeAdic.continuous_evaluation G T p n).comp
          continuous_fst).prodMk
          ((GroupScheme.Tate.PrimeAdic.continuous_evaluation G T p n).comp continuous_snd))

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "levelPair" => finiteWeilLevelBilinearMap preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA
local notation "finiteAlong" => finiteWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA

/-- Transporting the finite pullback pairing gives the actual torsion-section value. -/
lemma finiteWeilLevelBilinearMap_alongHom (lam : A ⟶ DA) (n : ℕ) (T : Over S)
    (x y : GroupScheme.Tate.Level A.toGrp T n) :
    levelPair n T x (GroupScheme.Tate.levelMap T (groupHom lam) n y) =
      mu.pointsLevelEquiv n T
        (finiteAlong lam n T
          ((GroupScheme.Tate.kernelLevelEquiv A.toGrp T n).symm x)
          ((GroupScheme.Tate.kernelLevelEquiv A.toGrp T n).symm y)) := by
  obtain ⟨x, rfl⟩ := (GroupScheme.Tate.kernelLevelEquiv A.toGrp T n).surjective x
  obtain ⟨y, rfl⟩ := (GroupScheme.Tate.kernelLevelEquiv A.toGrp T n).surjective y
  rw [← GroupScheme.Tate.kernelLevelEquiv_map]
  change mu.pointsLevelEquiv n T
      (finiteWeilBilinearMap preservation composition unitCoherence associativity comparison
        symmetry stability hA MA evaluationA n T
        ((GroupScheme.Tate.kernelLevelEquiv A.toGrp T n).symm
          (GroupScheme.Tate.kernelLevelEquiv A.toGrp T n x))
        ((GroupScheme.Tate.kernelLevelEquiv (DA).toGrp T n).symm
          (GroupScheme.Tate.kernelLevelEquiv (DA).toGrp T n
            (Additive.ofMul (y.toMul ≫ GroupScheme.Tate.kernelLevelMap (groupHom lam) n))))) = _
  simp only [AddEquiv.symm_apply_apply]
  rfl

variable (compatibility : RelativeFiniteWeilTransitionStatement.{u}) (T : Over S)

local notation "integralPair" => integralWeilBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA MA evaluationA compatibility T

/-- Pull back the second input by the actual Tate map of a dual-valued homomorphism. -/
def integralWeilAlongHomBilinearMap (lam : A ⟶ DA) (P : ℕ → Prop) :
    GroupScheme.Tate.Integral A.toGrp T P →ₗ[Global.ProfiniteIntegerRing]
      GroupScheme.Tate.Integral A.toGrp T P →ₗ[Global.ProfiniteIntegerRing]
        TateTwist.Divisibility.Integral Γ(T.left, ⊤) P :=
  (integralPair P).compl₂ (GroupScheme.Tate.fullLinearMap T P (groupHom lam))

local notation "integralAlong" => integralWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
    compatibility T

/-- The underlying value is precisely e(x, T(lam)(y)). -/
@[simp]
lemma integralWeilAlongHomBilinearMap_apply (lam : A ⟶ DA) (P : ℕ → Prop)
    (x y : GroupScheme.Tate.Integral A.toGrp T P) :
    integralAlong lam P x y =
      integralPair P x (GroupScheme.Tate.map T P (groupHom lam) y) := rfl

/-- Each coordinate agrees with the existing finite pairing along the same homomorphism. -/
lemma evaluation_integralWeilAlongHomBilinearMap (lam : A ⟶ DA) (P : ℕ → Prop)
    (n : GroupScheme.Tate.Index P) (x y : GroupScheme.Tate.Integral A.toGrp T P) :
    TateTwist.Divisibility.evaluation Γ(T.left, ⊤) P n (integralAlong lam P x y) =
      mu.pointsLevelEquiv n.val T
        (finiteAlong lam n.val T
          ((GroupScheme.Tate.kernelLevelEquiv A.toGrp T n.val).symm (x.val n))
          ((GroupScheme.Tate.kernelLevelEquiv A.toGrp T n.val).symm (y.val n))) :=
  finiteWeilLevelBilinearMap_alongHom preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA lam n.val T (x.val n) (y.val n)

/-- The same pullback pairing is bilinear over the away residue scalar ring. -/
def awayWeilAlongHomBilinearMap (lam : A ⟶ DA) (m : ℕ) :
    GroupScheme.Tate.Away A.toGrp T m →ₗ[Global.PrimeToProfiniteIntegerRing m]
      GroupScheme.Tate.Away A.toGrp T m →ₗ[Global.PrimeToProfiniteIntegerRing m]
        TateTwist.Divisibility.Away Γ(T.left, ⊤) m :=
  (awayWeilBilinearMap preservation composition unitCoherence associativity comparison
    symmetry stability hA MA evaluationA compatibility T m).compl₂
      (GroupScheme.Tate.awayLinearMap T m (groupHom lam))

/-- The away scalar bundle retains the selected integral value. -/
@[simp]
lemma awayWeilAlongHomBilinearMap_apply (lam : A ⟶ DA) (m : ℕ)
    (x y : GroupScheme.Tate.Away A.toGrp T m) :
    awayWeilAlongHomBilinearMap preservation composition unitCoherence associativity comparison
      symmetry stability hA geometryA MA evaluationA compatibility T lam m x y =
        integralAlong lam (fun n => Nat.Coprime n m) x y := rfl

/-- Restriction of full orders to away orders commutes with pullback pairing. -/
lemma restrictAway_integralWeilAlongHomBilinearMap (lam : A ⟶ DA) (m : ℕ)
    (x y : GroupScheme.Tate.Full A.toGrp T) :
    TateTwist.Divisibility.restrictAway Γ(T.left, ⊤) m
        (integralAlong lam (fun _ => True) x y) =
      integralAlong lam (fun n => Nat.Coprime n m)
        (GroupScheme.Tate.restrictAway A.toGrp T m x)
        (GroupScheme.Tate.restrictAway A.toGrp T m y) := rfl

/-- Joint continuity follows from the actual finite along-homomorphism coordinates. -/
lemma continuous_integralWeilAlongHomBilinearMap (lam : A ⟶ DA) (P : ℕ → Prop) :
    Continuous (fun z : GroupScheme.Tate.Integral A.toGrp T P ×
      GroupScheme.Tate.Integral A.toGrp T P => integralAlong lam P z.1 z.2) := by
  have hc : Continuous (fun z : GroupScheme.Tate.Integral A.toGrp T P ×
      GroupScheme.Tate.Integral A.toGrp T P =>
        fun n : GroupScheme.Tate.Index P =>
          levelPair n.val T (z.1.val n)
            (GroupScheme.Tate.levelMap T (groupHom lam) n.val (z.2.val n))) :=
    continuous_pi (fun n =>
      continuous_integralAlongCoordinates A.toGrp T P n
        (fun x y => levelPair n.val T x (GroupScheme.Tate.levelMap T (groupHom lam) n.val y)))
  exact hc.subtype_mk _

variable (p : ℕ) [Fact p.Prime]

local notation "primePair" => primeWeilBilinearMap preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA compatibility T p

/-- The corresponding actual prime-adic pullback pairing, bilinear over Z_p. -/
def primeWeilAlongHomBilinearMap (lam : A ⟶ DA) :
    GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p →ₗ[ℤ_[p]]
      GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p →ₗ[ℤ_[p]]
        TateTwist.Integral Γ(T.left, ⊤) p :=
  (primePair).compl₂ (GroupScheme.Tate.PrimeAdic.map T p (groupHom lam))

local notation "primeAlong" => primeWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
    compatibility T p

/-- The prime-adic value also pulls back the second variable by the actual map. -/
@[simp]
lemma primeWeilAlongHomBilinearMap_apply (lam : A ⟶ DA)
    (x y : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p) :
    primeAlong lam x y =
      primePair x (GroupScheme.Tate.PrimeAdic.map T p (groupHom lam) y) := rfl

/-- Prime-power coordinates agree with the same finite along-homomorphism pairing. -/
lemma evaluation_primeWeilAlongHomBilinearMap (lam : A ⟶ DA) (n : ℕ)
    (x y : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p) :
    TateTwist.evaluation Γ(T.left, ⊤) p n (primeAlong lam x y) =
      mu.pointsLevelEquiv (p ^ n) T
        (finiteAlong lam (p ^ n) T
          ((GroupScheme.Tate.kernelLevelEquiv A.toGrp T (p ^ n)).symm (x.val n))
          ((GroupScheme.Tate.kernelLevelEquiv A.toGrp T (p ^ n)).symm (y.val n))) :=
  finiteWeilLevelBilinearMap_alongHom preservation composition unitCoherence associativity
    comparison symmetry stability hA geometryA MA evaluationA lam (p ^ n) T (x.val n) (y.val n)

/-- Prime extraction commutes with the pullback pairing in a selected system. -/
lemma toPrime_integralWeilAlongHomBilinearMap (lam : A ⟶ DA)
    (P : ℕ → Prop) (hP : ∀ n, P (p ^ n))
    (x y : GroupScheme.Tate.Integral A.toGrp T P) :
    TateTwist.Divisibility.toPrime Γ(T.left, ⊤) P p hP (integralAlong lam P x y) =
      primeAlong lam
        (GroupScheme.Tate.PrimeComparison.toPrime A.toGrp T P p hP x)
        (GroupScheme.Tate.PrimeComparison.toPrime A.toGrp T P p hP y) := rfl

/-- The actual prime-adic pullback pairing is jointly continuous. -/
lemma continuous_primeWeilAlongHomBilinearMap (lam : A ⟶ DA) :
    Continuous (fun z : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p ×
      GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p => primeAlong lam z.1 z.2) := by
  have hc : Continuous (fun z : GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p ×
      GroupScheme.Tate.PrimeAdic.Integral A.toGrp T p =>
        fun n : ℕ => levelPair (p ^ n) T (z.1.val n)
          (GroupScheme.Tate.levelMap T (groupHom lam) (p ^ n) (z.2.val n))) :=
    continuous_pi (fun n =>
      continuous_primeAlongCoordinates A.toGrp T p n
        (fun x y => levelPair (p ^ n) T x
          (GroupScheme.Tate.levelMap T (groupHom lam) (p ^ n) y)))
  exact hc.subtype_mk _

end Langlands.AbelianScheme
