import Mathlib.Algebra.Central.Defs
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.FieldTheory.Separable
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Unitary involutions and the splitting of central simple algebras

This module defines when a map `τ : B → B` is an involution of the second kind
(a unitary involution) on an algebra `B` over a field `L`, relative to a map
`σ : L → L`, and states three properties of a base field `K`:

* `UnitaryInvolutionSplitting K`: for every separable quadratic extension `L/K`
  with nontrivial automorphism `σ`, every central simple `L`-algebra carrying a
  unitary involution relative to `σ` is a full matrix algebra over `L`;
* `UnitaryDivisionCommutative K`: the same situation for central division
  `L`-algebras forces dimension one;

and two statements: `UnitaryDivisionSplittingStatement` (over every field, the
second property implies the first) and `LocalUnitaryDivisionCommutativeStatement`
(every nonarchimedean local field has the second property). The statements are
not proved here.
-/

noncomputable section

universe u

namespace Langlands

/-- `τ` is a unitary involution (an involution of the second kind) of the
`L`-algebra `B` relative to `σ : L → L`: it is additive, reverses products, is its
own inverse, and acts on the scalars `algebraMap L B l` through `σ`. -/
def IsUnitaryInvolution {L B : Type*} [CommRing L] [Ring B] [Algebra L B]
    (σ : L → L) (τ : B → B) : Prop :=
  (∀ x y : B, τ (x + y) = τ x + τ y) ∧ (∀ x y : B, τ (x * y) = τ y * τ x) ∧
    (∀ x : B, τ (τ x) = x) ∧ ∀ l : L, τ (algebraMap L B l) = algebraMap L B (σ l)

/-- Over the field `K`, every central simple algebra over a separable quadratic
extension `L` of `K` that carries a unitary involution relative to the nontrivial
`K`-automorphism `σ` of `L` is isomorphic, as an `L`-algebra, to a full matrix
algebra `M_m(L)`. -/
def UnitaryInvolutionSplitting (K : Type u) [Field K] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L]
    [Algebra.IsSeparable K L] (σ : L ≃ₐ[K] L), σ ≠ 1 →
    ∀ (B : Type u) [Ring B] [Algebra L B] [FiniteDimensional L B] [IsSimpleRing B]
      [Algebra.IsCentral L B] (τ : B → B), IsUnitaryInvolution (⇑σ) τ →
      ∃ m : ℕ, Nonempty (B ≃ₐ[L] Matrix (Fin m) (Fin m) L)

/-- Over the field `K`, every finite-dimensional central division algebra over a
separable quadratic extension `L` of `K` that carries a unitary involution relative
to the nontrivial `K`-automorphism `σ` of `L` has dimension one over `L`. -/
def UnitaryDivisionCommutative (K : Type u) [Field K] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L]
    [Algebra.IsSeparable K L] (σ : L ≃ₐ[K] L), σ ≠ 1 →
    ∀ (D : Type u) [DivisionRing D] [Algebra L D] [FiniteDimensional L D]
      [Algebra.IsCentral L D] (τ : D → D), IsUnitaryInvolution (⇑σ) τ →
      Module.finrank L D = 1

/-- Over every field, if central division algebras with a unitary involution over
separable quadratic extensions are commutative, then central simple algebras with a
unitary involution over separable quadratic extensions are split. -/
def UnitaryDivisionSplittingStatement : Prop :=
  ∀ (K : Type u) [Field K], UnitaryDivisionCommutative K → UnitaryInvolutionSplitting K

/-- Over a nonarchimedean local field `K`, a finite-dimensional central division
algebra over a separable quadratic extension of `K` carrying a unitary involution
has dimension one over its center. -/
def LocalUnitaryDivisionCommutativeStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K], UnitaryDivisionCommutative K

end Langlands
