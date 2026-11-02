import Langlands.Global.Factors.MeromorphicPoleComparisonStatement
import Langlands.VirtualRepresentation.DescentStatement

/-!
# From local pair-factor poles to a generated integral isometry

The pair-factor pole formulas and all analytic comparison inputs remain
hypotheses. Integral relation descent and positivity are reused from the
published virtual-lattice branch.
-/

noncomputable section

open Filter
open scoped Topology

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation

universe u v w x y

/-- Actual local pair functions and the finite factors omitted when comparing
their completed germs. The two place types are independent. -/
structure PairFactorComparisonData (J : Type w) (A : Type x) (B : Type y) where
  left : J → J → ℂ → ℂ
  right : J → J → ℂ → ℂ
  leftPlaces : J → J → Finset A
  rightPlaces : J → J → Finset B
  leftOmitted : J → J → A → ℂ → ℂ
  rightOmitted : J → J → B → ℂ → ℂ
  leftBoundary : J → J → ℂ → ℂ
  rightBoundary : J → J → ℂ → ℂ

/-- Each supplied pair-factor germ is meromorphic; its omitted local factors
and its separate boundary function are holomorphic and nonzero. The completed
germs, rather than the distinguished pair factors, are assumed equal. -/
def RegularPairComparisonsAt {J : Type w} {A : Type x} {B : Type y}
    (d : PairFactorComparisonData J A B) (z : ℂ) : Prop :=
  ∀ j k,
    MeromorphicAt (d.left j k) z ∧
    MeromorphicAt (d.right j k) z ∧
    OmittedUnitsAt (d.leftPlaces j k) (d.leftOmitted j k) z ∧
    OmittedUnitsAt (d.rightPlaces j k) (d.rightOmitted j k) z ∧
    HolomorphicUnitAt (d.leftBoundary j k) z ∧
    HolomorphicUnitAt (d.rightBoundary j k) z ∧
    (completedProduct (d.leftPlaces j k) (d.left j k) (d.leftOmitted j k)
        (d.leftBoundary j k) =ᶠ[𝓝[≠] z]
      completedProduct (d.rightPlaces j k) (d.right j k) (d.rightOmitted j k)
        (d.rightBoundary j k))

/-- The representation-theoretic pole formula required of a supplied family.
The factors in applications pair the first object with the dual of the second.
The order is the negative of the integer coefficient pairing. -/
def RealizesPairingAtZero {ι : Type u} {J : Type w}
    (family : J → IntegralLattice ι) (factor : J → J → ℂ → ℂ) : Prop :=
  ∀ j k, meromorphicOrderAt (factor j k) 0 =
    ((-pairing (family j) (family k) : ℤ) : WithTop ℤ)

/-- Completed-germ comparison and actual pole formulas imply Gram equality. -/
def PoleGramComparisonStatement (ι : Type u) (κ : Type v) (J : Type w)
    (A : Type x) (B : Type y) : Prop :=
  ∀ (left : J → IntegralLattice ι) (right : J → IntegralLattice κ)
    (d : PairFactorComparisonData J A B),
    RegularPairComparisonsAt d 0 →
    RealizesPairingAtZero left d.left →
    RealizesPairingAtZero right d.right →
    ∀ j k, pairing (left j) (left k) = pairing (right j) (right k)

/-- The desired comparison of generated spans, including positive basis
extraction. No spanning of either ambient lattice or surjectivity on basis
indices is asserted. -/
def GeneratedPositiveIsometry {ι : Type u} {κ : Type v} {J : Type w}
    (left : J → IntegralLattice ι) (right : J → IntegralLattice κ)
    (sourceWeight : ι → ℕ) (targetWeight : κ → ℕ)
    (T : generated left ≃ₗ[ℤ] generated right) : Prop :=
  (∀ j, T (evaluateGenerators left (generator j)) =
    evaluateGenerators right (generator j)) ∧
  (∀ x y : generated left,
    pairing (T x : IntegralLattice κ) (T y : IntegralLattice κ) =
      pairing (x : IntegralLattice ι) (y : IntegralLattice ι)) ∧
  (∀ x : generated left,
    degree targetWeight (T x : IntegralLattice κ) =
      degree sourceWeight (x : IntegralLattice ι)) ∧
  (∀ x : generated left,
    pairing (x : IntegralLattice ι) (x : IntegralLattice ι) = 1 →
    0 < degree sourceWeight (x : IntegralLattice ι) →
    ∃! i : κ, (T x : IntegralLattice κ) = generator i)

/-- A common positive rank for corresponding generators, local pole formulas,
and regular completed comparisons give the unique generated-span isometry
preserving degree and the positive norm-one basis condition. -/
def PoleGeneratedDescentStatement (ι : Type u) (κ : Type v) (J : Type w)
    (A : Type x) (B : Type y) : Prop :=
  ∀ (left : J → IntegralLattice ι) (right : J → IntegralLattice κ)
    (sourceWeight : ι → ℕ) (targetWeight : κ → ℕ) (rank : J → ℕ+)
    (d : PairFactorComparisonData J A B),
    (∀ j, degree sourceWeight (left j) = (rank j : ℤ)) →
    (∀ j, degree targetWeight (right j) = (rank j : ℤ)) →
    RegularPairComparisonsAt d 0 →
    RealizesPairingAtZero left d.left →
    RealizesPairingAtZero right d.right →
    relations left = relations right ∧
    ∃! T : generated left ≃ₗ[ℤ] generated right,
      GeneratedPositiveIsometry left right sourceWeight targetWeight T

/-- The analytic pole-to-pairing step followed by integral descent. -/
def PolePairingDescentStatement (ι : Type u) (κ : Type v) (J : Type w)
    (A : Type x) (B : Type y) : Prop :=
  PoleGramComparisonStatement ι κ J A B ∧
  PoleGeneratedDescentStatement ι κ J A B

end Langlands.Global.PoleComparison
