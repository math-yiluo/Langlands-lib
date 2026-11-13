# Haar coinvariants have dimension one

The theorem `Langlands.Jacquet.haarCoinvariantsDimension` proves exactly the
published proposition `Langlands.Jacquet.HaarCoinvariantsDimensionStatement`,
at its original group universe. For every Hausdorff, locally compact, totally
disconnected topological group `G`, the coinvariants of the left regular
representation on `SchwartzBruhat G` have complex finrank one.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, III.2.9, Example, printed p.78 / PDF p.84.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 275 read that original page, including the preceding identification
of the full algebraic dual of coinvariants with invariant functionals.

The implementation follows this algebraic-dual argument and constructs a
linear equivalence with ℂ inside the proof. Its only representation is the
published `HarmonicAnalysis.GroupAction.leftTests`; its quotient is the
published `Jacquet.Coinvariants` at the whole subgroup.

The published theorem
[`RenardHaar.leftHaar`](../../HarmonicAnalysis/Distribution/RenardHaarLeftProof.md)
supplies a left-invariant distribution `T` such that every left-invariant
algebraic distribution is a unique complex scalar multiple of `T`. In
particular, `T` is nonzero: if it vanished, the coefficients zero and one
would both express `T` as a multiple of itself, contradicting uniqueness.
The proof uses this uniqueness argument; it does not need to evaluate a
positive test function.

Left invariance of `T` says that it is unchanged by translating a test
function. The quotient universal property `Jacquet.lift` therefore gives a
linear functional `I` on the coinvariants with `I([f]) = T(f)`.

To prove that its kernel is zero, let `I(q) = 0` and take any algebraic
functional `φ` on the coinvariants. The composite `S = φ ∘ Jacquet.mk`
is left invariant, because the quotient map identifies every test with each
of its left translates. Haar uniqueness gives `S = c • T` for some complex
scalar `c`. Choose a representative `f` of `q` using `Jacquet.mk_surjective`.
Then `φ(q) = c T(f) = c I(q) = 0`. The Mathlib theorem
`Module.forall_dual_apply_eq_zero_iff` separates vectors by their full
algebraic dual and yields `q = 0`. Applying this kernel result to differences
proves that `I` is injective.

The map `I` is nonzero, since otherwise its composite with the quotient map
would make `T` zero. Every nonzero linear map to a one-dimensional vector
space is surjective; the proof uses
`surjective_of_nonzero_of_finrank_eq_one` and `Module.finrank_self ℂ`.
Finally, `LinearEquiv.ofBijective` turns `I` into a linear equivalence with
ℂ, whose `finrank_eq` proves the target.

This proves the quotient itself has dimension one without first imposing
finite dimensionality. All duals used in the proof are algebraic, as in the
source. The statement pair and its imports are unchanged, and the theorem
adds no hypotheses.
