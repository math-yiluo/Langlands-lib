# The actual smooth complex inside a standard Levi

Internal construction by Worker 194, using Worker 23's actual subgroup
functors and Levi indexing.

`LeviComplex.family L F J K` reads `K : Finset J` in the ambient root set
using `leviIndex`, then takes the subgroup `F(K)` inside `L`. The proved
inclusion laws transport increasing parabolics and decreasing radicals to
these restricted families.

For a closed standard Levi `M(J)`, `LeviComplex.sharpFunctor ... K` applies
the actual standard-subset complex construction to the families
`P(L) ∩ M(J)`, `M(L) ∩ M(J)`, `U(L) ∩ M(J)`, indexed by subsets `L` of `J`.
The supplied Levi-in-Levi semidirect decompositions and unimodularity proofs
are explicit prerequisites. Closedness of the restricted radicals is
inherited by continuous preimage; closedness of `M(J)` supplies local
compactness. Monotonicity follows from the proved inclusion laws. The
functor uses the same canonical quotient transitions, exterior signs,
incoming-image submodules and quotient maps as `StandardComplex`.

Its value `sharpObject A K` is the actual retained cokernel in degree
`|J| - |K|`. In particular, `K = Finset.univ` selects degree zero, as needed
for cuspidal objects of the full Levi. The carrier universe is enlarged to
contain the index universe, so repeated cokernel, Jacquet and conjugation
functors compose. This imposes no finite-length restriction.

The provenance is the standard Levi version of the corrected complex in
Aubert's 1996 erratum, printed pp.4687 and 4690. This file constructs that
complex for the supplied actual subgroup families. It does not prove
exactness, cuspidality of a Jacquet module, or the associated-Levi comparison
on p.4690. General reductive realization of the subgroup and topology data,
and all representation-theoretic comparison laws, remain separate
obligations.
