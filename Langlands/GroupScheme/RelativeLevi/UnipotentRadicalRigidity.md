# Dynamic rigidity for relative unipotent radicals

This internal proof helper is developed for the uniqueness assertion in Conrad,
*Reductive group schemes* (2014), Corollary 5.2.5, page 153. It uses the published
dynamic constructions over an arbitrary base scheme.

The smoothness lemma places an automorphic action of the multiplicative group
on a smooth affine group in its actual semidirect product. The ambient dynamic
unipotent subgroup represents the original action's identity-limit functor.
The published arbitrary-base dynamic smoothness theorem and uniqueness of
representatives then give smoothness of any representative.

The normalized conjugation lemma checks equivariance using the actual
conjugation morphism. The intersection lemma uses this equivariance and
closedness to identify the scheme-theoretic intersection with the
identity-limit subgroup of the action on the normalized subgroup, on every
test scheme. These are derived helper results, rather than separate assertions
quoted from Conrad.

The geometric-fibre isomorphism criterion assumes that the source is flat and
locally of finite presentation, and that the target is locally of finite type
over the base. It first reflects isomorphisms from the chosen algebraic closure
to the residue field by faithfully flat base change. The published fibrewise
open-immersion criterion applies over the residue fields. Surjectivity follows
by lifting a point to its residue-field fibre, and a surjective open immersion
is an isomorphism. The final passage through the forgetful functors produces an
isomorphism of group schemes.

Containment of all-test subgroup ranges supplies a factorization of one
inclusion through the other. The universal property of the scheme-theoretic
intersection then gives an inverse to its projection. Consequently, for two
relative unipotent radicals, both intersection projections are isomorphisms on
every geometric fibre, using the published field-radical uniqueness theorem.
If the intersection is smooth over the base, the preceding criterion makes
both projections isomorphisms globally, and the two all-test ranges agree.

For `radical_range_eq_of_dynamic_unipotent`, the ambient group `P` is affine
over an arbitrary scheme `S`. The inputs are two relative radicals
`n : N → P`, `r : U → P`, and a cocharacter `χ : Gm → P` for which `r`
represents `Dynamic.unipotent χ`. Normality of `n` gives the induced
conjugation action on `N`. Closedness makes `N` affine over `S`; it is smooth
by the relative radical predicate. The intersection lemma and the action
smoothness lemma make `N ∩ U` smooth. The preceding comparison therefore
proves equality of `range n` and `range r` on every test scheme, including
nonreduced schemes.

`dynamicRadicalIso` packages this equality as the compatible isomorphism
`N ≅ U` of representatives. The accompanying equation states that its
homomorphism followed by `r` is `n`. This is an internal construction derived
from the stated inputs. It neither constructs a radical on a general parabolic
nor establishes an étale-local dynamic presentation or descent; those remain
separate steps toward the unchanged global target.
