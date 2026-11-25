module

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
public import Mathlib.Data.Finset.Functor
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Order.Interval.Finset.Box
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.AffineMonoid.UniqueSums

set_option autoImplicit false
set_option maxSynthPendingDepth 3

-- ===== merged from StacksDraft.Ch10.Sec58.Tag00K3 =====

/-!
# The Hilbert function of a graded quotient of a polynomial ring

Throughout, `k` is a field and `d ≥ 1` is a positive integer. Let
`S = k[X_1, …, X_d]` be the polynomial ring in `d` variables, regarded as a
graded `k`-algebra with the standard grading in which each variable `X_i` has
degree `1`. For an integer `n ≥ 0`, the degree-`n` graded piece `S_n` is the
`k`-vector space of homogeneous polynomials of degree `n` (together with `0`);
for `n < 0` we set `S_n = 0`.

We formalize the following (Stacks Lemma 10.58.10, Tag 00K3):

  Let `k` be a field, let `d ≥ 1`, and let `S = k[X_1, …, X_d]` with the standard
  grading. Let `I ⊆ S` be a *nonzero* graded ideal and set `M = S / I`. Then the
  Hilbert function `H_M(n) = dim_k(M_n)` is a numerical polynomial whose degree is
  strictly less than `d - 1`.

In particular there exist a polynomial `P ∈ ℚ[T]` with `deg P < d - 1` and an
integer `N` such that `dim_k(M_n) = P(n)` for all `n ≥ N`. (Here `deg P < d - 1`
allows `P` to be the zero polynomial, whose degree is taken to be `-∞`; this is
modeled in Lean by `Polynomial.degree`, which sends the zero polynomial to `⊥`.)
When `d = 1`, the bound `deg P < 0` forces `P = 0`, equivalently
`dim_k(M_n) = 0` for all sufficiently large `n`.
-/

@[expose] public section
-- needed file-wide: `FinModule.cls_eq_of_linearEquiv`, `FinModule.cls_add_of_ses`,
-- `KPrime0.hom_ext`, `xpow_four_term_class` and `hilbertFun_xpow_step_identity` all rewrite
-- through the `FinModule`/`KPrime0` quotient wrappers and the graded-piece subgroup coercions,
-- which only unfold with defeq transparency relaxed.  See also the note before
-- `section MainPieces`, which depends on this option holding for the whole file.
set_option backward.isDefEq.respectTransparency false
universe u

namespace Stacks.HilbertFunction.PolynomialQuotient

/-! ## Background and setup

We model `S = k[X_1, …, X_d]` as `MvPolynomial (Fin d) k`. The standard grading is
the total-degree grading, whose degree-`n` piece is the `k`-submodule
`MvPolynomial.homogeneousSubmodule (Fin d) k n` of homogeneous polynomials of
degree `n`. The total-degree grading makes `S` a graded algebra via
`MvPolynomial.gradedAlgebra` (registered as an instance below so that
`Ideal.IsHomogeneous` can refer to it). -/

/-- The total-degree grading turns `k[X_1, …, X_d]` into a graded algebra.
This is `MvPolynomial.gradedAlgebra`, registered here as an instance so that the
homogeneity predicate `Ideal.IsHomogeneous` is available for ideals of
`MvPolynomial (Fin d) k`. -/
noncomputable instance instGradedAlgebra (k : Type*) [Field k] (d : ℕ) :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin d) k) :=
  MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {d : ℕ}

/-- The degree-`n` graded piece of
`S = k[X_1, …, X_d]`: the `k`-vector space of homogeneous polynomials of degree
`n`. -/
noncomputable def gradedPieceS (k : Type*) [Field k] (d : ℕ) (n : ℕ) :
    Submodule k (MvPolynomial (Fin d) k) :=
  MvPolynomial.homogeneousSubmodule (Fin d) k n

/-- For an ideal `I ⊆ S`, its
degree-`n` graded piece, viewed as a `k`-vector space: the intersection of `I`
(restricted to a `k`-submodule) with the degree-`n` piece `S_n`. When `I` is a
graded ideal this is the `n`-th graded piece of `I` in the usual sense. -/
noncomputable def gradedPieceI (I : Ideal (MvPolynomial (Fin d) k)) (n : ℕ) :
    Submodule k (MvPolynomial (Fin d) k) :=
  (I.restrictScalars k) ⊓ gradedPieceS k d n

/-- The Hilbert function of `M = S / I`,
defined by `H_M(n) = dim_k(M_n) = dim_k(S_n) - dim_k(I_n)`. Since `I_n ⊆ S_n` and
both are finite dimensional, the truncated subtraction on `ℕ` agrees with the
honest difference `dim_k(M_n)`. -/
noncomputable def hilbertFunction (I : Ideal (MvPolynomial (Fin d) k)) (n : ℕ) : ℕ :=
  Module.finrank k (gradedPieceS k d n) - Module.finrank k (gradedPieceI I n)

/-! ## Correctness statements for the definitions

These auxiliary statements pin down the definitions above and connect them to the
standard descriptions of the Hilbert function. -/

/-! ## Decomposition lemmas for the main theorem

The main theorem is reduced to the lemmas below. The proof idea (Stacks) is:
pick a nonzero homogeneous `f ∈ I` of degree `e`; multiplication by `f` injects
`S_{n-e}` into `I_n`, so `dim I_n ≥ dim S_{n-e}`, giving an upper bound on `H_M`
by a binomial difference of degree `< d-1`; combine with the background fact that
`H_M` is a numerical polynomial to bound the *degree* of its representing
polynomial. -/

/-- Auxiliary: the rational binomial polynomial `X·(X-1)···(X-i+1)/i!`, whose
evaluation at `q : ℚ` equals `Ring.choose q i`. -/
noncomputable def binomialPoly (i : ℕ) : Polynomial ℚ :=
  Polynomial.C (1 / (i.factorial : ℚ)) * descPochhammer ℚ i

open Polynomial in
/-- Evaluation of the rational binomial polynomial equals `Ring.choose`. -/
theorem binomialPoly_eval (i : ℕ) (q : ℚ) : (binomialPoly i).eval q = Ring.choose q i := by
  unfold binomialPoly
  rw [eval_mul, eval_C]
  have hdp : (descPochhammer ℚ i).eval q = (i.factorial : ℚ) * Ring.choose q i := by
    rw [← descPochhammer_map (algebraMap ℤ ℚ), ← eval₂_eq_eval_map, ← aeval_def, aeval_eq_smeval,
      Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
  rw [hdp]; field_simp

end Stacks.HilbertFunction.PolynomialQuotient
