# Clopen subgroups of normal subgroups in connected families

Let `S : Scheme.{u}` be any base, `G`, `K`, and `P` group schemes over `S`,
`i : K → G` a homomorphism monomorphic on the underlying schemes over `S`,
and `j : P → K` an open and closed immersion. Assume the full range subgroup
functor of `i` is normal and `G → S` is geometrically connected.

`conjugation` constructs the actual morphism `G ×_S P → P` restricting
ambient conjugation. Its composite with `j` and `i` is the original
conjugation morphism. Consequently `isNormal_range_comp` proves normality
of the full range subgroup functor of `j ≫ i`, on every scheme test.

The proof first applies the supplied normality of `i` on the test scheme
`G ×_S P` to factor conjugation through `K`. Monomorphy of `i` shows that
along the section `p ↦ (1,p)` the resulting morphism to `K` is exactly `j`.
The inverse image of the range of `j` is clopen. Each fibre of the second
projection `G ×_S P → P` is connected by geometric connectedness of `G → S`,
and meets this clopen inverse image at the section. A preconnected set
meeting a clopen set is contained in it, so the entire conjugation image
lies in `j`. Open-immersion lifting now gives the actual restricted
morphism. Precomposing it with any pair of test points proves the stated
all-test normality.

This is a source-free internal construction from the existing normal
subgroup-functor definition, Mathlib's geometric-connectedness and clopen
APIs, and the published open-immersion lifting operation. No local-base,
finite, flat or smooth hypothesis is needed. Applied to a supplied finite
clopen part of a kernel subgroup in a geometrically connected group, it
supplies the ambient normality ingredient. It does not construct that part
or prove the host fibrewise-isogeny theorem.
