# Functorial actual pinned lifts

Author: Worker 1472.

This internal construction uses the published chosen pinned lifts and pinned
rigidity theorem. For supplied split pinnings over any field in universe `u`,
it constructs the identity and composition of actual pinned isomorphisms.
Composition uses the actual group and torus isomorphisms and the composite
root-index equivalence. The inclusion square, full roots and coroots, simple
supports and chosen Lie vectors are preserved. The Lie-vector equation follows
from functoriality of the actual differential.

`Iso.ext_torus_index` applies the published unconditional pinned rigidity
theorem through `PinnedIsomorphism.iso_ext`. Thus a pinned isomorphism is
determined by its actual torus isomorphism and root-index equivalence.
`eq_isoOfRootDatumEquiv` identifies any lift with the existing chosen lift
when its forward full character map and index map are the prescribed ones.
The full character map determines the torus isomorphism by split-torus
extensionality; the perfect pairing forces the corresponding cocharacter map.

`isoOfRootDatumEquiv_id` proves that the chosen lift of the identity root-datum
equivalence is the complete identity pinned isomorphism.
`isoOfRootDatumEquiv_comp` proves equality of complete pinned isomorphisms for
composition. If `e` goes from the first root datum to the second and `d` from
the second to the third, the chosen lift of `d.comp e` is the lift of `e`
followed by the lift of `d`. The proof compares full forward character maps
and root-index equivalences, then invokes uniqueness. Character transport is
inverse pullback, so its order is the forward order of the torus isomorphisms.

These are internal consequences of the imported Library results. Their paired
Markdown records the original-source interpretation. All pinnings remain
supplied inputs. This module does not prove pinning existence, a splitting of
the automorphism functor on coefficient algebras, an effective Galois datum,
or quasi-split inner-form existence.
