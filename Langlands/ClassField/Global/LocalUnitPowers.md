# Powers of local units have finite index

This module, in namespace `Langlands.ClassField.Global`, shows that `d`-th powers
of valuation units at a finite place of a number field have finite index in the
valuation units, for every `d ≠ 0`. It also shows that squares at a real place
have finite index in the units of the completion. It imports
[LocalUnitCohomology](LocalUnitCohomology.md), whose `localUnits v` is the
subgroup of `(v.adicCompletion K)ˣ` of valuation one,
[CompletionResidueAdic](../../Global/CompletionResidueAdic.md), which supplies
finiteness of the residue field of `v.adicCompletionIntegers K`, and
[IntegralFiniteAdeles](../../Global/IntegralFiniteAdeles.md), which supplies its
compactness.

## Hensel's lemma without monicity

- `exists_isRoot_of_isAdicComplete I f a₀ h₁ h₂`: let `R` be a commutative ring
  that is `I`-adically complete. Let `f` be a polynomial over `R`, not
  necessarily monic, and let `a₀` satisfy `f(a₀) ∈ I`, with `f'(a₀)` a unit
  modulo `I`. Then `f` has a root `a` with `a - a₀ ∈ I`. The proof is Mathlib's
  proof of `IsAdicComplete.henselianRing` (Newton iteration and adic
  completeness), copied verbatim. That proof never uses the monicity hypothesis
  of `HenselianRing`.
- `one_add_mul_pow_eq e z`: in any commutative ring, with `d = e + 1`,
  `(1 + d z)^d = 1 + d^2 (z + z^2 G(z))`, where
  `G(z) = Σ_{k<e} C(d, k+2) d^k z^k`. The proof uses the binomial theorem and
  splits off the terms of degree `0` and `1`.

## The completed integer ring

Write `O_v = v.adicCompletionIntegers K` for a finite place `v` of a number
field `K : Type u`.

- `compactSpace_adicCompletionIntegers v`: `O_v` is compact. This is the
  Library's `isCompact_adicCompletionIntegers`, stated as a `CompactSpace`
  instance.
- `isAdicComplete_adicCompletionIntegers v`: `O_v` is complete for its
  maximal-ideal-adic topology. The proof copies Mathlib's proof for
  nonarchimedean local fields. The cosets `f n + 𝔪^n` form a decreasing sequence
  of closed subsets: ideals of the compact Noetherian ring `O_v` are closed. By
  compactness this sequence has a common point, which is a limit of `f`.
  The Hausdorff condition is not proved here: instance search supplies it from
  Mathlib's instances for Noetherian local rings and discrete valuation rings.
- `exists_pow_eq_one_add_sq_mul v d hd t ht`: for `d ≠ 0` and `t` in the maximal
  ideal, `1 + d^2 t` is a `d`-th power in `O_v`. Write `d = e + 1`. Hensel's lemma
  applied to `f = X + X^2 G - t` at `a₀ = 0` gives `z` with
  `z + z^2 G(z) = t`, since `f(0) = -t ∈ 𝔪` and `f'(0) = 1`. Then
  `(1 + d z)^d = 1 + d^2 t` by `one_add_mul_pow_eq`.

## Finite index of local unit powers

- `localUnitsToIntegerUnits v : localUnits v →* (O_v)ˣ` regards a unit of
  valuation one, together with its inverse, as a unit of `O_v`; the simp lemma
  `coe_localUnitsToIntegerUnits` says that its underlying element of the
  completion is unchanged.
- `localUnitPowers v d : Subgroup (localUnits v)` is the range of the `d`-th
  power homomorphism on `localUnits v`; `mem_localUnitPowers_iff` unfolds
  membership as `∃ y, y ^ d = u`.
- `localUnitPowers_finiteIndex v d hd`: for `d ≠ 0`, `localUnitPowers v d` has
  finite index in `localUnits v`. Let `I = (d^2) 𝔪`, a nonzero ideal of the
  discrete valuation ring `O_v`. Then `I` is a power of `𝔪`, so `O_v ⧸ I` is
  finite because the residue field is finite. The kernel of the reduction
  homomorphism `localUnits v → (O_v ⧸ I)ˣ` consists of units `u ≡ 1 mod d^2 𝔪`.
  These are `d`-th powers `y^d` with `y ∈ O_v` by `exists_pow_eq_one_add_sq_mul`.
  The root `y` has valuation one: its valuation is at most one, and its `d`-th
  power has valuation one. The kernel has finite index because its target is
  finite, and it is contained in `localUnitPowers v d`.

## Powers at infinite places

For an infinite place `v` of a field `K`:

- `infiniteUnitPowers v d : Subgroup (v.Completion)ˣ` is the range of the `d`-th
  power homomorphism, with `mem_infiniteUnitPowers_iff`.
- `infiniteUnitPowers_one v : infiniteUnitPowers v 1 = ⊤`.
- `infiniteUnitPowers_two_finiteIndex v hv`: if `v` is real, squares have finite
  index. Transport by `InfinitePlace.Completion.ringEquivRealOfIsReal`. A unit
  `x` whose image in `ℝ` is positive is the square of the preimage of its square
  root, so `x` or `-x` is a square. Hence the classes of `1` and `-1` cover the
  quotient.

## Sources and provenance

J. S. Milne, *Class Field Theory*, version 4.03 (2020), Chapter I, 1.7, printed
p.22 (PDF p.31), registered original `milne-2020-class-field-theory`. It states
that Newton's lemma applied to `X^m - a` shows every `a ∈ O_K` with
`|1 - a| < |m|^2` is of the form `u^m` with `u ∈ 1 + 𝔪`, in characteristic zero.
`exists_pow_eq_one_add_sq_mul` is this statement for `O_v`; the condition
`a - 1 ∈ m^2 𝔪` is the same inequality. The Lean proof substitutes
`X = 1 + m Y` and solves for `Y` with a simple root. It does not use the
stronger Newton lemma. Milne, the same chapter, 1.6, printed p.22 (PDF p.31),
says that the squares of `ℝ^×` are the positive reals, which is the content of
`infiniteUnitPowers_two_finiteIndex`. The finite-index conclusion
`localUnitPowers_finiteIndex` is the standard consequence used in Emil Artin and
John Tate, *Class Field Theory*, AMS Chelsea edition (2009), Chapter VI §1,
first lemma, printed p.20 (PDF p.29), registered original
`artin-tate-2009-class-field-theory`. There it bounds local norm indices in the
proof that the idele-class norm index is finite. The non-monic Hensel lemma and
the adic completeness proof are copied from Mathlib (`IsAdicComplete.henselianRing`
in `Mathlib/RingTheory/Henselian.lean` and the `IsAdicComplete 𝓂[K] 𝒪[K]`
instance in `Mathlib/NumberTheory/LocalField/Basic.lean`). The binomial
identity and the reduction argument are internal.
