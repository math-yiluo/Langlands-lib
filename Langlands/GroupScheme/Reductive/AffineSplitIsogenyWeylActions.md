# Square and fixed conjugation of the actual powered Weyl family

This internal derived module instantiates `PoweredWeylActions` with the actual
powered maps prescribed by a root-datum isogeny. It retains the original
characteristic condition on the coefficient ring and does not require those
powered maps to be root parametrizations.

The root-map character identity is first recorded as
`hasRootConjugationFormula_rootMap`. Over a commutative coefficient ring, with an
affine target group and genuine normalized target simple-root data for the
transported words, word transport supplies the same identity for every
member of the powered source-indexed Weyl family.

`wordConj_square_poweredWeylFamily` assumes the standard integral coordinate
pairings for the two root data and the genuine target `RankOneLaws` for the
opposite pair at the root being used for conjugation. The existing powered
rank-one theorem supplies the source coroot square under the prescribed
torus map. Combining it with the proved source-character formula gives
conjugation twice by the actual powered Weyl product as multiplication by
the raw integer sign `negOnePow` of the source Cartan entry, cast into the
coefficient ring.

`wordConj_fixed_poweredWeylFamily` assumes that the coefficient ring is local,
the target torus inclusion is closed, and the conjugating source root is simple. Both this root
and its negative must be nonopposite to the root being conjugated and
have no mixed root with it in the source datum. The genuine target
parametrizations supplied by the normalized data commute by the actual
no-cone theorem, including its exceptional characteristic cases. The
root-power and transported-word identities identify all three maps as
precompositions of those target parametrizations. The generic fixed-action
theorem then gives the exact powered Weyl-map identity.

`PoweredWeylActionRelations` records these two laws at every simple source
root and every root being conjugated. `poweredWeylActionRelations` proves
this bundle under the same local target hypotheses, the standard coordinate
pairings, and genuine target rank-one laws at the corresponding simple
opposite pairs. Those genuine rank-one laws remain an explicit geometric
input of this assembly; no square or fixed-action identity for powered maps
is an input.

The proofs use the existing root-map equivariance, word transport, powered
rank-one laws, and the separately proved square and fixed-action group
algebra. They do not assert that an empty source cone gives an empty
target cone. The remaining Weyl-conjugation induction, root relations,
ambient map construction, and final isogeny theorem remain separate work.
