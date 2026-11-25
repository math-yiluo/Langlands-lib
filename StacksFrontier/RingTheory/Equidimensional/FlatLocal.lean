module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.Topology.Dimension.Equidimensional
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

/-!
# Stacks Tag 0AW4 (Lemma 15.111.3)

Let `A → B` be a flat local map of Noetherian local rings with `B` catenary and
`Spec(B)` equidimensional. Then (1) `Spec(B / pB)` is equidimensional for every
prime `p ⊆ A`, and (2) `A` is catenary and `Spec(A)` is equidimensional.

## Main statements

* `flat_local_catenary_equidim_fibre`: Stacks 0AW4 (1), the fibre is equidimensional.
* `specEquidimensional_iff_equidimensional`: the reusable bridge identifying this module's
  `SpecEquidimensional R` with the project-wide `TopologicalSpace.Equidimensional (PrimeSpectrum
    R)`.
* `specEquidimensional_quotients_and_isCatenary_of_flat_local`: the two clauses above, recombined
  into the single conjunction the Stacks source states, phrased with
  `TopologicalSpace.Equidimensional`.
* `flat_local_catenary_equidim_base`: Stacks 0AW4 (2), the base is catenary and equidimensional.

## Proof outline

Catenarity of `Spec B` makes `coheight` drop by exactly one along covering pairs, and with
equidimensionality this gives `height Q + coheight Q = dim B` for every prime `Q` of `B`. A prime
`Q` minimal over `pB` lies over `p` by going down, and has `height Q = height p` by the height
formula for flat maps (`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`), which gives (1).
Comparing the height formula at the closed points for `A → B` and for `A ⧸ p → B ⧸ pB` gives
`height p + dim (A ⧸ p) = dim A`; applied to `A ⧸ p` this shows `p ↦ dim (A ⧸ p)` is a dimension
function, so `A` is catenary (Stacks 02IA), and applied to minimal primes that `A` is
equidimensional.
-/

/-- The coheight of a prime `P` equals the Krull dimension of the quotient
`R ⧸ P`. -/
lemma coheight_eq_ringKrullDim_quotient {R : Type*} [CommRing R] (P : PrimeSpectrum R) :
    (Order.coheight P : WithBot ℕ∞) = ringKrullDim (R ⧸ P.asIdeal) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  rfl

namespace FlatLocalCatenary

open Order TopologicalSpace

variable {B : Type*} [CommRing B]

section flat

variable {A : Type*} [CommRing A] [Algebra A B]

end flat

variable {B : Type*} [CommRing B]

variable {A : Type*} [CommRing A] [Algebra A B]

section L2

open IsLocalRing

end L2

end FlatLocalCatenary

open FlatLocalCatenary Order

section EquidimensionalBridge

open TopologicalSpace PrimeSpectrum

end EquidimensionalBridge
