module

import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

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
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

/-!
# Regular sequences are quasi-regular

The multi-index power `listPow`, the elementary form `IsQuasiregularSeq` of quasi-regularity, the
cons and snoc induction steps, and the main results `isRegular_isQuasiregularSeq` (Stacks 00LN (2))
and `isRegular_isQuasiregularSeq_self` (Stacks 00LN (1)).
-/

@[expose] public section

open scoped Finset

namespace Stacks.QuasiregularSequence

variable {R : Type*} [CommRing R]

/-! ## Main statements -/

open RingTheory.Sequence

/-! ## The cons step

Notation throughout: `J = Ideal.ofList (f :: gs)`, `J' = Ideal.ofList gs`,
`g^{I'} = listPow gs I'`.  A multi-index `I : Fin (gs.length + 1) → ℕ` for the
sequence `f :: gs` decomposes as `(a, I')` where `a = I 0` is the exponent of `f`
and `I' = I ∘ Fin.succ` is the restriction to `gs`.  Then
`listPow (f :: gs) I = f ^ a * listPow gs I'`, which is `listPow_cons` below.
-/

/-- Ideal decomposition: `(f :: gs) = (f) + (gs)` at the level of generated ideals.
It follows from `{r | r ∈ f :: gs} = insert f {r | r ∈ gs}` and
`Ideal.span_insert`. -/
theorem ofList_cons_sup (f : R) (gs : List R) :
    Ideal.ofList (f :: gs) = Ideal.span {f} ⊔ Ideal.ofList gs := by
  unfold Ideal.ofList
  rw [show {r | r ∈ f :: gs} = insert f {r | r ∈ gs} by ext; simp, Ideal.span_insert]

/- Unfolds `IsQuasiregularSeq (init ++ [g]) M` to
the grouped, honest-`= 0` form fed to `snoc_inner_induction`.

Given the degree-`n` relation `∑_{I ∈ antidiagonalTuple (c+1) n} listPow (init++[g]) I • m I
∈ J^{n+1}M` (where `c = init.length`), produces a family
`a : ℕ → (Fin c → ℕ) → M` with `a e I' ≡ (the original coefficient at g-exponent e,
prefix index I') mod JM` such that the honest relation
`∑_{e=0}^n g^e • (∑_{|I'|=n-e} listPow init I' • a e I') = 0` holds, AND such that
`a e I' ∈ JM ↔ m (the corresponding full index) ∈ JM`.

This packages: (i) the last-coordinate peel `listPow (init++[g]) I = listPow init (I∘castSucc)
* g^(I last)` (`Fin.prod_univ_castSucc`); (ii) the last-coordinate reindexing of
`antidiagonalTuple (c+1) n` as `⨆_e {I' : |I'| = n-e}` (peel last coord); (iii) Step 1 of the
informal proof: subtract a representative `∑ f^I b_I` (`b_I ∈ JM`) of the `J^{n+1}M` element to
make the relation honest `= 0`, which only changes each `m I` by an element of `JM`. -/

end Stacks.QuasiregularSequence
