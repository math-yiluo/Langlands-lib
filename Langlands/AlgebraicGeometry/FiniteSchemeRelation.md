# A relation assembled from finitely many scheme charts

This is internal infrastructure for the finite symmetric-tuple presentation in
the proof of the Noetherian first-level statement. Its mathematics is derived
from the universal properties of scheme coproducts and pullbacks, finite
extensivity of schemes, and the existing definition of an étale equivalence
relation. The motivating finite family of symmetric-tuple charts is Stacks
Project, Decent Algebraic Spaces, Lemma 68.8.6 (Tag 07ST), proof, in the
registered source `stacks-noetherian-approximation-2026-11-01`. The generic
coproduct construction here is derived infrastructure, rather than a separate
claim stated in that source. It does not assert or assume an approximation theorem.

`isClosedImmersion_sigma_ι` identifies a coproduct component as a closed
immersion. The component is already an open immersion. Joint surjectivity and
disjointness of the coproduct inclusions identify its range complement with
the union of the other open component ranges; thus its own range is closed.
`isClosedImmersion_of_finite_coproduct` proves that an injective map
from a finite coproduct is a closed immersion if its restrictions are closed
immersions. Surjectivity on stalks is local on the source. The image of a closed
set is the finite union of its closed component images, so the total map is
closed; together with continuity and injectivity this gives a closed embedding.

`FiniteSchemeRelation I` supplies object charts `U i`, cross-chart schemes
`R i j`, their endpoints, closed joint endpoint immersions, étale endpoints,
and reflexivity, symmetry and transitivity on points valued in every scheme.
Here `I` is a type; the assembly uses its finiteness and is valid also when `I`
is empty. All schemes retain the arbitrary universe `u`.

`objectScheme` and `relationScheme` are the coproducts of the object charts and
the cross-chart schemes, respectively. `first` and `second` include the
appropriate endpoint into the object coproduct. `ι_first` and `ι_second` give
their restrictions. Their étaleness follows by locality on the source.
`component_joint_isClosedImmersion` follows by composing a chartwise joint
immersion with the product of the closed coproduct inclusions.
`joint_isClosedImmersion` applies the finite coproduct criterion. Equality of
the two total joint images forces both chart indices to agree, by projecting
to the object coproduct. On the same component, injectivity follows from its
closed immersion into the product of total object schemes. This argument does
not identify scheme-product points merely from their two projections.

`exists_composite` composes two chartwise arrows whose middle endpoints agree
in the object coproduct. When the middle chart indices agree, monicity of the
coproduct inclusion reduces the condition to chartwise transitivity. When they
differ, disjointness of the coproduct inclusions forces the test scheme to be
empty; its initial property supplies the unique arrow and endpoint equalities.

`toEtaleEquivalenceRelation` assembles an actual étale equivalence relation.
Reflexivity and symmetry are coproducts of their chartwise witnesses.
For transitivity, finite extensivity identifies the pullback of the two total
endpoint maps with the coproduct, over pairs of cross-chart indices, of the
component pullbacks. `exists_composite` supplies a map from each such component
to the relation coproduct. Their coproduct and the pullback universal property
give composition for any test scheme, including disconnected schemes. The
endpoint equations follow componentwise. Monicity follows from the proved
closed immersion, and the endpoint étaleness was proved above.

The concluding instances retain the closed joint immersion and show that the
assembled object and relation schemes are affine whenever all their components
are affine. They use finiteness of the coproducts.
