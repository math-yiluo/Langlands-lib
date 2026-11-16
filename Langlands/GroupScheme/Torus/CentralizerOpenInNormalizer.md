# Centralizers are open in torus normalizers

This internal construction supports the smooth-affine torus Weyl quotient.
Its inputs and proof are derived from the published all-test torus centralizer
and normalizer, the split-torus conjugation rigidity results in
`Rational.TorusNormalizerRigidity`, and descent of open immersions along
surjective étale maps in `SchemeFlatPropertyDescent`. It introduces no additional
geometric premise.

For any scheme `S`, a monomorphic homomorphism `t : T.toGrp ⟶ G` from a relative
torus, and representatives `n : N ⟶ G` and `z : Z ⟶ G` of its actual normalizer
and centralizer functors,
`relativeTorusCentralizerNormalizerInclusion` constructs the canonical
homomorphism `c : Z ⟶ N`. The returned data prove `c ≫ n = z`, prove that the
underlying scheme map of `c` is an open immersion, and identify its range on
every test scheme with `(torusCentralizer t).comap n`. The base is arbitrary;
there is no affine, smoothness, connectedness, or maximality assumption on the
ambient group. The relative torus condition is the published existence of a
small étale cover on which the torus is split.

The implementation first treats a split torus with a chosen finite coordinate
set. In any normalizing family `g` over a test scheme `U`,
`TorusConjugation.centralizerLocus` is the open locus where conjugation acts by
the identity exponent matrix at the residue-field point. Openness follows
from the published local constancy of `ActsAtPoint`.

`actsBy_iff_forall_actsAtPoint` detects a specified exponent matrix after an
arbitrary restriction `a : V ⟶ U`. The forward implication restricts to residue
fields. For the converse, it tests affine charts. Each selected coefficient is
an idempotent. If it were a nonunit, a maximal ideal containing it would
contradict the prescribed residue-field action. A unit idempotent is one,
giving the all-test action on that chart and then on the restriction. With
the identity matrix, the published `actsBy_one_iff` identifies this action
with centralization. Thus a restriction factors through `centralizerLocus`
exactly when its image centralizes the torus on all further tests.

For a representative `c : Z ⟶ N` of the centralizer preimage,
`splitTorusCentralizer_isOpenImmersion` identifies `Z` with that open locus in
`N`. One map is the open-subscheme lift of `c`; the other is obtained by the
representing property applied to the open locus itself. Monicity of the
representative and of the open immersion proves that the maps are inverse.

`isOpenImmersion_groupHom_of_etaleCover` checks an open immersion after base
change to each member of a small étale cover of the base. It pulls the cover
back to the target group scheme and descends along the surjective étale map
from the disjoint union of its members. On each open summand of that disjoint
union, the required pullback agrees, by the canonical pullback isomorphism,
with the given base-changed group homomorphism.
`relativeTorusCentralizer_isOpenImmersion` applies this to an étale splitting
cover of the torus. The actual normalizer, centralizer, and centralizer preimage
all commute with base change, so the split result applies on each member.

Finally, the selected construction factors `z` through `n` using
`torusCentralizer_le_torusNormalizer` and the representing property of `n`.
Monicity and `c ≫ n = z` identify this factor with the centralizer preimage
on every test scheme. The relative openness theorem then supplies its open
immersion property. This construction alone does not construct the quotient
or assert the Weyl quotient theorem.
