# The integral completion map and its ramification index

The module constructs `FiniteExtension.completionIntegersMap` by restricting the
canonical map `completionMap p q` to the actual valuation rings
`p.adicCompletionIntegers K` and `q.adicCompletionIntegers L`. Here `K : Type u`
and `L : Type v` are number fields, with independent universes, their given
`Algebra K L`, and height-one primes `p` and `q` with `q` lying above `p`.
All field maps and scalar structures extend the canonical scoped algebra from
`Langlands.Global.AdelicFunctoriality.Extension`.

This is internal derived infrastructure for the completed local degree bound.
It is obtained from the published completion embedding and the pinned Mathlib
valuation and ramification theory, rather than transcribed from a literature
statement. It supplies no assumption of a degree bound or completed tensor
isomorphism.

## Construction and valuation formula

`valuation_completionMap` proves, for every completed element `x`,

`Valued.v (completionMap p q x) = Valued.v x ^ q.asIdeal.ramificationIdx (𝓞 K)`.

The proof extends Mathlib's `HeightOneSpectrum.valuation_liesOver` from the dense
image of `K`. Both normalized integer-valued valuations are continuous because
they are surjective; composition with the continuous completion map and taking
a fixed power preserve continuity. The dense-range equalizer proves equality
on the completions. Mathlib's comparison lemma converts the older primed
ramification index in `valuation_liesOver` to the current `Ideal.ramificationIdx`.

The global ramification index is positive. Thus taking that power preserves and
reflects the condition that the valuation is at most one. This gives
`completionMap_mem_integers_iff`, and hence the restricted ring homomorphism
`completionIntegersMap`. Its underlying field map is recorded by the definitional
lemma `completionIntegersMap_coe`.

The module installs, in the `FiniteExtension` scope, the induced algebra on
completed integer rings and its two compatible scalar towers into the target
completion. A further scoped instance proves the map is local: a unit in the
target has valuation one, so the power formula and positivity of the exponent
force its preimage to have valuation one. Injectivity follows from injectivity
of the field homomorphism and supplies the scoped torsion-free module instance.

## Normalization and ramification comparison

`completionIntegers_intValuation` identifies the maximal-ideal adic valuation on
the completed integer ring with its existing `Valued.v`. Zero is immediate. For
a nonzero element, the DVR factorization writes it as a unit times a power of an
irreducible element. The irreducible generates the maximal ideal and is therefore
a uniformizer for the existing valuation. Surjectivity of that valuation fixes
its value at `WithZero.exp (-1)`, exactly the value of a maximal-ideal generator
for the adic valuation. Both valuations assign one to units; multiplicativity
then proves the identity for every element.

`completionIntegers_ramificationIdx` proves the exact equality

`(IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)).ramificationIdx
  (p.adicCompletionIntegers K) = q.asIdeal.ramificationIdx (𝓞 K)`.

The local homomorphism supplies the lying-over relation between the maximal
ideals. Apply Mathlib's integral valuation restriction formula to a base
uniformizer and convert its index to the current ramification index. The
normalization lemma and `valuation_completionMap` express both sides as powers
of `WithZero.exp (-1)`. Injectivity of these natural powers equates the two
ramification indices.

This module proves the ramification bridge only. Residue-field scalar
compatibility, inertia-degree comparison, and the final local degree inequality
are separate obligations. In particular, no finite-module property of the
completed integer-ring extension is assumed.
