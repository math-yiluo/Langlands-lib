module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Tactic.IntervalCases
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# A normal local domain with separably closed fraction field is strictly henselian

Throughout, $(R, \mathfrak m, \kappa)$ is a commutative local ring with maximal ideal
$\mathfrak m$ and residue field $\kappa = R/\mathfrak m$.

Let $(R, \mathfrak m, \kappa)$ be a normal local domain: a local integral domain integrally
closed in its fraction field $K = \operatorname{Frac}(R)$. If $K$ is separably algebraically
closed then $R$ is strictly henselian, i.e. the residue field $\kappa$ is separably
algebraically closed and $R$ is a henselian local ring (Stacks tag 0BSQ).

## The encoding

`HenselianLocalRing R` says that for every monic $f \in R[X]$ and every $a_0 \in R$ with
$f(a_0) \in \mathfrak m$ and $f'(a_0)$ a unit there is $a \in R$ with $f(a) = 0$ and
$a - a_0 \in \mathfrak m$. `IsSepClosed k` says every separable nonconstant polynomial in
$k[X]$ has a root. A normal local domain is `IsLocalRing R`, `IsDomain R` and
`IsIntegrallyClosed R`, the last being integral closedness in the fraction field. "Strictly
henselian" is the conjunction `HenselianLocalRing R ∧ IsSepClosed (IsLocalRing.ResidueField R)`,
and $K$ is any field with `IsFractionRing R K`.

## Structure of the argument

Everything rests on one observation, `IsIntegrallyClosed.algebraMap_eq_of_integral`: because
`R` is integrally closed in `K`, any `x : K` integral over `R` is the image of an element of
`R`. Both halves are instances of the same engine — a root of a monic `R`-polynomial that is
separable over `K` actually lives in `R` — packaged as `sep_root_of_monic_mem_range` (L0) and
used to discharge `henselian_half` (L2) and `residue_sepClosed_half` (L1).
-/

@[expose] public section

open Polynomial IsLocalRing

-- ===== merged from StacksDraft.Ch10.Sec153.Tag04GM =====

/-- A complete local ring is Henselian: `IsAdicComplete.henselianRing` provides
the lifting property, and we transport the simple-root hypothesis along
`Ideal.Quotient.mk`. -/
@[stacks 04GM]
theorem henselianLocalRing_of_isAdicComplete_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    HenselianLocalRing R :=
  .mk fun f hf a₀ ha₀ ha₀' =>
    (IsAdicComplete.henselianRing R _).is_henselian f hf a₀ ha₀
      (ha₀'.map (Ideal.Quotient.mk _))

-- ===== merged from StacksDraft.Ch10.Sec153.Tag06RR =====

open Polynomial

-- ===== merged from StacksDraft.Ch10.Sec153.Tag06RS =====

/-!
# A local ring of Krull dimension zero is henselian

Throughout, `R` is a commutative ring; when `R` is local, `m` denotes its maximal ideal and
`k = R/m` its residue field, and for `f` in `R[T]` we write `f'` for the formal derivative
with respect to `T`.

A local ring `(R, m, k)` is *henselian* if for every monic `f` in `R[T]` and every `a₀` in
`R` with `f(a₀)` in `m` and `f'(a₀)` a unit — that is, the image of `a₀` is a simple root of
the image of `f` — there is `a` in `R` with `f(a) = 0` and `a - a₀` in `m`. This is Mathlib's
`HenselianLocalRing`, whose defining field `HenselianLocalRing.is_henselian` states exactly
that. A local ring is never the zero ring, so its maximal ideal is a genuine prime and Krull
dimension `0` coincides with Krull dimension at most `0`, spelled `Ring.KrullDimLE 0 R`:
every prime ideal is maximal.

The theorem is that a local ring of dimension `0` is henselian. Instead of the
finite-algebra characterization used in the Stacks proof, the argument here is the
self-contained Newton iteration, which is valid for an arbitrary local ring of Krull
dimension `0`: no Noetherian, Artinian or `m`-adic completeness hypothesis is needed, and
indeed `m`-adic completeness can fail for such a ring.

The pieces are:

* (A) In a local ring of Krull dimension `0`, `maximalIdeal R = nilradical R`, so every
  element of `m` is nilpotent (`KrullDimLE0.maximalIdeal_eq_nilradical`).
* (B) **One Newton step.** For `f : R[X]`, `a : R` and `u : R` with
  `f.derivative.eval a * u = 1`, put `a' = a - f.eval a * u`. Then
  `f.eval a' = (f.eval a) ^ 2 * c` for some `c : R`, and `a' - a = -(f.eval a * u)`
  (`Polynomial.newton_one_step`).
* (C) **Newton convergence at a nilpotent value.** If `f.eval a₀` is nilpotent and
  `f.derivative.eval a₀` is a unit, then `f` has a genuine root `a` with
  `a - a₀ ∈ Ideal.span {f.eval a₀}`, hence in any ideal containing `f.eval a₀`. The error
  after `n` Newton steps lies in `(f.eval a₀) ^ (2 ^ n)`, which vanishes once `2 ^ n`
  exceeds the nilpotency degree, and `f.derivative.eval aₙ` stays a unit because `aₙ ≡ a₀`
  modulo the nil ideal generated by `f.eval a₀`
  (`Polynomial.exists_isRoot_of_isNilpotent_eval`).
* (D) Assembling: under the henselian hypotheses `f.eval a₀ ∈ m = nilradical` is nilpotent
  by (A), so (C) gives a root `a` with `a - a₀ ∈ span {f.eval a₀} ⊆ m`.
-/

@[expose] public section

open Polynomial IsLocalRing
