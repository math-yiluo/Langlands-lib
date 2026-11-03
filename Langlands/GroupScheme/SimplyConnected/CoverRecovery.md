# A recovered cover of a simply connected target is an isomorphism

Let `k` and `K` be fields in arbitrary universe `u`, with `Algebra k K`.
Suppose `G` is simply connected over `k`, and an actual central isogeny
`a : D → G` has semisimple source. Let `π : C → G_K` be a supplied arrow
over `K`. The additional data are an actual source isomorphism
`j : D_K ≅ C` and the exact recovery equation `a_K = j.hom ≫ π`.
All scalar extensions use the actual group-scheme pullback along
`Spec.map (CommRingCat.ofHom (algebraMap k K))`.

`IsSimplyConnected.isoOfCoverRecovery` constructs an actual isomorphism
`C ≅ G_K` whose hom is precisely `π`. Simple connectedness of `G`
makes `a` an isomorphism, since `D` is semisimple and `a` is a central
isogeny. Functoriality makes `a_K` an isomorphism. The recovery equation
then makes `j.hom ≫ π` an isomorphism, and cancellation of the source
isomorphism makes `π` an isomorphism. The construction packages that
arrow with `asIso`. The accompanying hom theorem records its exact hom.

`IsSimplyConnected.fieldExtension_of_coverRecovery` additionally assumes
simple connectedness of `C` and transfers it across the inverse of this
constructed isomorphism to prove simple connectedness of `G_K`.

This is an internal categorical adapter of the public simple-connectedness
predicate, functorial preservation of isomorphisms, and cancellation of
isomorphisms. It uses the unchanged full central-isogeny predicate,
including scheme-theoretic kernels on all test schemes. No external
source assertion is introduced. The descended source, arrow, source
isomorphism, and recovery equation are explicit inputs. This module
constructs no descent data or cover and does not prove the unrestricted
field-extension theorem.
