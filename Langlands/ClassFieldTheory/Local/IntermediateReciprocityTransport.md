# Reciprocity transport to prescribed intermediate fields

This internal construction extends the published `IntermediateWeil` comparison
from actual Weil groups to the absolute Galois groups of prescribed finite
intermediate fields, including fields which are not normal over the base.
It supplies no new class field theory premise and does not assert existence
of an unconditional common-closure reciprocity system.

The chosen absolute Galois map in `IntermediateWeil` is the conjugate of the
published extension map by the closure correction. Its range is the literal
fixing subgroup of the prescribed field, by the existing conjugacy formula.
Cancellation proves injectivity. Compactness of the source and the Hausdorff
property of the ambient Galois group give a closed embedding. Restricting to
its range therefore produces the topological group equivalence
`intermediateGaloisEquiv`.

Applying the published functor on quotients by closed commutators gives
`intermediateWeilAbelianEquiv` and `intermediateGaloisAbelianEquiv`.
The Weil projection square commutes on the groups by the existing prescribed
closure comparison; quotient induction proves the corresponding square on
abelianizations. These constructions and elementary proofs are derived from
the published Library comparisons and abelianization API, rather than new
external mathematical assertions.

The component constructor `CommonClosure.intermediateReciprocityCandidate`
precomposes a supplied standalone candidate with the inverse Weil quotient
comparison. `familyOfStandalone` performs this operation at every actual
finite intermediate field with the canonical topological data. Its induced
Galois map is the supplied standalone Galois map followed by
`intermediateGaloisAbelianEquiv`, by the quotient square above.

If every supplied standalone candidate satisfies
`GeometricWeilReciprocityRelation`, its Galois map has dense range by the
finite norm-residue relation. Composing with the Galois equivalence preserves
density. The published `profiniteReciprocityCompletion` gives a comparison
from the actual open-finite-quotient completion of field units to the
standalone Galois abelianization. Postcomposing with the prescribed-field
Galois equivalence supplies the exact `CompletionRelation` diagram.
No norm, transfer or conjugation coherence is asserted by these conditional
transport lemmas; those are separate obligations in the full system target.
