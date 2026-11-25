# Actual root opposition from a supplied rank-one central cover

This internal derived construction compares actual nonzero adjoint-weight
roots through a supplied central isogeny. It then applies that comparison to
a supplied cover by `SL₂ × C`. No cover-existence theorem is proved or used.
The field, characteristic and universe are unrestricted.

`IsCentralIsogeny.rootPullbackEquiv` takes an actual central isogeny
`f : G ⟶ H`, two split commutative tori with action homomorphisms `i` and `j`,
and a torus isogeny `t` satisfying `i ≫ f = groupHom t ≫ j`. The ambient groups
are affine and locally of finite type. It constructs an equivalence from the
actual roots of `j` to those of `i`. Its forward map is the actual character
pullback `χ ↦ t ≫ χ`. Flatness and surjectivity of the torus isogeny make its
underlying scheme map an epimorphism, hence character pullback is injective.
The published central-isogeny nonzero-weight theorem gives equality of root
supports for the same source-torus action. The published root comparison
then gives a bijection, from which `Set.BijOn.equiv` constructs the equivalence.

`IsCentralIsogeny.eq_or_eq_neg_of_source` gives the corresponding general
descent of equality or opposition. It pulls both target roots back through
the torus isogeny, applies the supplied source-root property and uses
injectivity of character pullback to reflect the resulting equality.

`eq_or_eq_neg_of_sl2_centralCover` takes a supplied central isogeny
`SL₂ × C ⟶ G`, a split commutative torus `C`, a supplied split torus action on
`G`, and an isogeny from `D × C` to that torus compatible with the standard
special-linear diagonal action. For any two actual roots of the target
it proves equality or opposition. It needs neither maximality nor pairwise
dependence once the cover is supplied.

The finite ambient isogeny and the target's affine, locally finite type
structure give both scheme hypotheses of the source product by composition.
These two steps are the general lemmas
`IsCentralIsogeny.isAffineHom_source` and
`IsCentralIsogeny.locallyOfFiniteType_source`.
Consequently no root datum or independent reductivity theorem for the product
is needed. The root comparison pulls both target roots back to actual
product roots. The explicit product calculation in `RankOneCentralCoverRoots`
makes those pullbacks equal or opposite. Injectivity of character pullback
reflects the equality; its additivity handles the negative case.

The provenance is this direct internal combination of finite-morphism
geometry, actual central-isogeny weight transport, split-torus character
restriction and explicit `SL₂` matrix roots. The full scheme-theoretic kernel
and finite-flat-surjective isogeny hypotheses are retained, including for
inseparable isogenies. This result supplies a conditional consumer of a
supplied rank-one cover and does not itself prove cover existence; the Library
proves `RankOneCentralCoverStatement` by `rankOneCentralCover`
(`RankOneCentralCoverProof`).
