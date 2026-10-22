# Principal congruence entries and positive-level cofinality

Authors: Worker 128 (Lean and exposition), with Worker 70 (the intended
interface and two-sided criterion).

This pair states two reusable properties of the actual principal congruence
subgroups already defined in `Langlands.Representation.Conductor.PrincipalCongruence`.
All three declarations below are transparent `Prop`-valued definitions in
`Langlands.Conductor`, polymorphic in the arbitrary field universe `u`.
They state targets; this pair proves neither component.

## Two-sided membership criterion

`PrincipalCongruenceEntryStatement.{u}` quantifies over every field
`k : Type u`, subring `O : Subring k`, natural number `n`, ideal `I : Ideal O`,
and actual `g : Matrix.GeneralLinearGroup (Fin (n + 1)) k`. It asserts that
`g ∈ principalCongruenceSubgroup O n I` is equivalent to both entry conditions:

- For every `i,j : Fin (n + 1)`, there exists `x : O` with `x ∈ I` whose
  image in `k` is `g i j - δ i j`.
- For every `i,j : Fin (n + 1)`, there exists `x : O` with `x ∈ I` whose
  image in `k` is `g⁻¹ i j - δ i j`.

Here `δ i j` is the corresponding entry of the identity matrix over `k`.
The existential witnesses are independent for each entry and for the two
matrices. The left side is the existing image of the integral reduction kernel;
it is not a new entry-defined subgroup. The algebraic statement imposes no
valuation, topology, properness of `I`, or local-ring hypothesis on `O`.

Both conditions are necessary at `I = ⊤`: this principal subgroup is the
image of `GL_(n+1)(O)`, so both the matrix and its inverse must be integral.
For example, in rank one with `O = ℤ ⊂ ℚ`, the matrix `(2)` has integral
entries but its inverse `(1/2)` does not. A one-sided integral-entry test
would incorrectly include it. The existing integral membership theorem only
needs one entry condition because its argument is already an element of
`GL_(n+1)(O)`; the new target instead takes an arbitrary element of the field
matrix group.

## Positive levels in the supplied topology

`PrincipalLevelCofinalStatement.{u}` quantifies over `k : Type u` and supplied
instances, in order, of `Field k`, `ValuativeRel k`, `TopologicalSpace k`, and
`IsNonarchimedeanLocalField k`. For every natural number `n` and every subset
`U` of the actual `GL_(n+1)(k)` belonging to the identity-neighborhood filter,
it asserts the existence of a natural number `a` such that `0 < a` and
`(principalLevelOpenSubgroup k n a : Set _) ⊆ U`.

The open subgroup is the existing subgroup obtained from the `a`th power of
the maximal ideal of the supplied valuation's integer ring. Its openness and
the neighborhood filter use the supplied topology and its inherited matrix-unit
topology. No field realization is chosen. The neighborhood `U` need not itself
be open. The positive-level requirement is explicit even though the existing
construction also defines level zero, where the subgroup is the full integral
general linear group. Compactness is already proved by
`isCompact_principalLevelOpenSubgroup` and is not repeated in this target.

The aggregate `PrincipalCongruenceBasisStatement.{u}` is exactly the conjunction
of these two universally quantified components, in the displayed order.
All matrix ranks here are indexed as `n + 1`; `n = 0` means rank one.
Rank zero is outside this API. The target requires no additional local
compactness hypothesis and contains no block factorization, representation,
or contraction assertion.

## Sources and derived scope

The motivating original is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, *Induced representations and
the Jacquet module*, revision April 29, 2019, section 4, page 5,
Lemma III.4.1 and its proof. Registered source: `casselman-2019-jacquet-module`,
SHA256 `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The original page was read directly. No source-specific errata file was
present in the published notes or alongside the retained source when checked.

Casselman describes an identity-neighborhood basis with Iwahori factorization
and uses positive congruence levels `G(𝔭^a)`, `a ≥ 1`, in the split case.
The positive-level cofinality target here is the concrete general-linear-group
specialization using the existing principal subgroup construction and supplied
nonarchimedean local-field instances. The two-sided entry criterion is an
algebraic derived formulation of that construction: the image of the integral
reduction kernel consists of integral invertible matrices reducing to the
identity, with the inverse subject to the same congruence. Casselman does not
state these Lean formulations or the arbitrary-subring criterion literally.

This pair isolates the membership and cofinality interfaces needed for later
proofs. It makes no assertion that the new propositions have been proved and
does not import Casselman's factorization, normality, or simultaneous-parabolic
compatibility conclusions as assumptions.
