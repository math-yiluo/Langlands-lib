# Renard C.I: monotonicity of the nilpotent-generated dimension maximum

Worker 709 authored the draft of the closed Prop-valued declaration
`Langlands.Renard.NilpotentDimensionMonotonicityStatement.{u,v}` for the
unnumbered assertion that `φ_l` is increasing in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, Appendix C.I, printed p.275 / one-based PDF281. It occurs
immediately before the displayed floor recurrence. This pair states the
assertion and its carrier-independent formulation; it contains no proof.
Worker 16 checked the source correspondence and prepared the focused pair
for submission, retaining Worker 709's formulation.

The governing registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF281–282 were reread, and PDF281 was visually checked, including the
sentence using monotonicity to compare the two arguments of `φ_l`. The
registered supplementary source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was reread on PDF18–19. Its C.I entries concern inequalities and exponents
in the older numerical proof; the 2026 original governs this assertion.

## Actual maximum and quantifiers

The published import `Langlands.Algebra.RenardNilpotentDimensionMaximum`
defines `nilpotentGeneratedMaxDimension l V` as the natural supremum of the
actual dimensions of
`Algebra.adjoin ℂ (Set.range a)`, where
`a : Fin l → Module.End ℂ V` ranges over commuting nilpotent tuples.
Its intrinsic laws prove that this set is nonempty and bounded and that
the maximum is attained by an actual tuple. Those definitions and laws
are imported unchanged. The canonical specialization
`nilpotentGeneratedPhi l k` is this maximum on `Fin k → ℂ`.

The first conjunct quantifies over every natural generator count `l` and
every pair of complex vector spaces `V : Type u` and `W : Type v`, each
with explicit additive-group, complex-module and finite-dimensional
instances. The carrier universes are independent. Its sole additional
premise is

`Module.finrank ℂ V ≤ Module.finrank ℂ W`.

It concludes

`nilpotentGeneratedMaxDimension l V ≤ nilpotentGeneratedMaxDimension l W`.

The second conjunct says, for every `l`, that
`Monotone (nilpotentGeneratedPhi l)`: for every pair of natural numbers
`k ≤ m`, `φ_l(k) ≤ φ_l(m)`. Thus increasing in the source means
nondecreasing, not strictly increasing. The first conjunct makes explicit
the source's independence of the choice of a dimension-`k` carrier; it is
a derived formulation of the same comparison, not a separately numbered
claim in the book. The carrier-transport statement and proof remain
separate published results.

The generator count is fixed in each comparison. The assertion includes
every natural tuple length, zero-dimensional spaces, and zero, repeated or
redundant generators. The identity and scalars lie in the unital adjoin
without adding a counted generator. No nontriviality, positivity,
chosen-basis, supplied embedding, supplied monotonicity, maximizing-witness
or sharp-dimension-bound premise is added.

For a zero-dimensional source space its maximum is zero, as proved in the
imported construction. For no generators on a nonzero space the unital
scalar algebra has dimension one; on the zero space it has dimension zero.
These boundary cases explain why the statement compares maxima. It does
not assert inclusion of the sets of possible dimensions under enlargement:
the zero-space dimension set consists of zero, whereas an adjoin on a
nonzero space contains a nonzero identity and has positive dimension.

## Proof and remaining scope

A possible proof extends a commuting nilpotent tuple by zero on an added
summand. Restriction to the original summand maps the enlarged generated
algebra onto the original generated algebra, so its dimension cannot
decrease. Carrier transport then identifies the canonical specialization.
The identity on the added summand still belongs to the enlarged unital
algebra; no equality of the two generated-algebra dimensions is presumed.
This paragraph describes a prospective proof route, not implemented Lean.

The ideal filtration endpoint, complement generation, restriction
injectivity, algebra splitting, first-level comparison, floor recurrence,
and final contradiction remain separate obligations. In particular,
monotonicity alone supplies neither the source's bound on `φ_l(k)` using a
complement of an attaining tuple nor its floor recurrence. Numerical base
cases, carrier transport, C.III results and the rest of the whole-book
program retain their existing owners.
