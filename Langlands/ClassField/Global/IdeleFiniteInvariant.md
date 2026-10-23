# Finite-place invariants of idele cohomology

Author: Worker 21.

This module uses a supplied family `I` of local invariant maps, with no
choice of a distinguished family. The fields `F` and `E` are number fields
in an arbitrary common universe, with `E/F` Galois. All cohomology groups
and arithmetic maps are the published actual ones.

`finiteIdeleInvariant I v w` is the additive map obtained by composing
`ideleLocalMap v w 2` with the supplied relative invariant of `E_w/F_v`.
The hypotheses provide the canonical finite-dimensional Galois extension
of completions. This definition itself requires no image law.

`finiteIdeleInvariant_principal` identifies its value on
`principalIdeleCohomologyMap F E 2 x` with
`Reciprocity.finiteLocalInvariant v w I x`. The proof applies the supplied
local invariant to the published equality between principal embedding
followed by the local cohomology map and the field-unit localization map.

The remaining constructions assume `RelativeImages` for every prime.
`finite_ideleLocalSupport` uses `relativeH2_finite` and
`relativeH2_card` to discharge the two hypotheses of
`finite_setOf_ideleLocalMap_ne_zero`. Finiteness is supplied separately
from the cardinality equality; no inference is drawn from a bound on
`Nat.card` alone. The completed base field's carrier is definitionally
the completion used in the cardinality bound.

For any explicit choice `wf v` of a finite place of `E` above each finite
place of `F`, `finite_support_finiteIdeleInvariant` proves that only
finitely many resulting invariants are nonzero. Its support is contained
in `ideleLocalSupport`, since an additive invariant maps zero to zero.

`finiteIdeleInvariantSum I hI wf` is the additive map given by the
finitely supported sum over all finite places of `F`. The zero law is
pointwise. Additivity follows from finite support of both summands and
`finsum_add_distrib`.

`finiteIdeleInvariantSum_principal` gives the finite sum appearing in
`Reciprocity.SumOfInvariantsVanishes` on a principal class, by the
pointwise principal compatibility above.

These are internal derived constructions from the imported local image
law, finite-support theorem, and functoriality of the actual coefficient
maps. They supply no archimedean terms, independence of the choice of
places, reciprocity law, or descent to idele-class cohomology. In
particular, they do not prove `GlobalInvariantStatement`.
