# Positive carry classes under the cyclic norm comparison

Author: Worker 28.

This module proves the published proposition
`Langlands.ClassFieldTheory.Local.CyclicClassNormNormalization.{u,v}`
as `cyclicClassNormNormalization`, with exactly that type and no additional
hypotheses. For every finite Galois extension `L/K` in independent universes,
every nonzero `n`, every cyclic coordinate isomorphism `χ`, and a generator `σ`
with `χ σ = Multiplicative.ofAdd 1`, the existing `cyclicH2NormEquiv` sends
the positive carry class of a base-field unit `a` to the class of `a` in the
actual determinant-norm quotient. This includes `n = 1`.

The proof imports the published cyclic cocycle-sum theorem
`Langlands.Cohomology.CyclicH2.cocycleSumComparison`. It retains the actual
Mathlib resolution comparison, the positive carry cocycle, and the field norm
quotient from the unchanged target's imports.

## Carry calculation for nontrivial cyclic groups

For `n > 1`, the private lemma `sum_cyclicCarry_one` proves that precisely the
summand at `n - 1` contributes one to
`∑ i ∈ Finset.range n, cyclicCarry (i : ZMod n) 1`.
The coordinate isomorphism identifies the Galois group cardinality with `n`
and sends powers of the chosen generator to the corresponding residues.
Distributing scalar multiplication over the sum gives the private lemma
`cyclicUnitCocycle_sum`: the cycle sum of the carry cocycle equals the included
base-field unit `baseUnit K L a`.

The main theorem applies `cocycleSumComparison` over `IntegerScalars.{v}`
to this explicit kernel element, whose fixedness follows from
`baseUnit_fixed`. It unfolds `cyclicH2InvariantsEquiv`, cancels Mathlib's
comparison isomorphism with its inverse, and uses
`ShortComplex.moduleCatCyclesIso_inv_π_assoc` to identify the homology
representative. The kernel-to-invariants and quotient maps send that
representative to `baseUnitsToInvariants` by definition.
Finally, `invariantsModNormEquiv_symm_projection` identifies its descent
with the class of the original base-field unit in the norm quotient.

## The group of order one

When `n = 1`, every residue has value zero, so the carry cocycle and its
cohomology class vanish. The representation norm of the included base unit
is the base unit itself: every action fixes it and the group cardinality is
one. Thus this invariant unit belongs to the norm image, and its quotient
class vanishes as well. This branch does not need the generic comparison
theorem.

## Provenance and scope

This is an internal specialization of the published generic comparison
and field-descent constructions. The original conventions are those of
Jean-Pierre Serre, *Local Fields*, English translation, Springer GTM 67
(1979), VIII.4, Proposition 6, its corollary and the following
generator-character remark, printed pages 132–133 / PDF pages 138–139.
The registered source is `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
These passages use `D = σ - 1`, the positive group norm, and the character
with value `1/n` at `σ`; their relation to the positive carry convention
is documented in the target's paired Markdown.

Worker 28 implemented the carry arithmetic and field specialization.
The imported generic proof credits Workers 53 and 262 for its resolution
comparison and chain map, Worker 28 for its interface and positive
comparison design, and Worker 25 for documenting its target.
Worker 80 authored the field normalization target.
This theorem supplies the algebraic normalization only; it does not
construct a local invariant map or prove an arithmetic class-formation
theorem.
