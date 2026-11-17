# Extending actual split-torus fibre maps to an open neighbourhood

Let `S` be any scheme and let `I` and `J` be finite coordinate types.
For an actual homomorphism `f : splitTorus S I ⟶ splitTorus S J`,
`splitTorus.coordinateBaseChangeGroupHom p f` is the pullback along `p : A ⟶ S`
expressed in the canonical split coordinates over `A`. Its definition first
uses the inverse source `baseChangeIso`, then the actual pulled-back map,
then the target `baseChangeIso`.

The main constructor `splitTorus.coordinatePermutationNeighbourhood` takes
an equivalence `σ : J ≃ I`, a point `s : S`, and an equality saying that this
normalized pullback along `S.fromSpecResidueField s` is the actual coordinate
permutation with target coordinate `j` equal to source coordinate `σ j`.
It returns an open `W` containing `s` together with the equality

`coordinateBaseChangeGroupHom W.ι f = (coordinatePermutationIso W σ).hom`.

Thus the same supplied permutation works on the whole open neighbourhood.
The hypothesis and conclusion are equalities of group-scheme homomorphisms,
not just equalities on points valued in the residue field. In particular,
they imply the coordinate formula on every relative test scheme. No
connectedness, reducedness, affineness or positive-rank hypothesis is
imposed on `S`, and empty finite coordinate types are allowed. The point
parameter makes no assertion that an empty scheme has a point. The stated
`Fintype` and `DecidableEq` instances support the finite sums and choices.

The file also provides the following ingredients:

- `HomFamily.exists_open_actsBy_of_actsAtPoint` extends a prescribed integer
  matrix for an arbitrary multiplicative natural family from one residue
  fibre to all tests over an open neighbourhood of its parameter point.
- `HomFamily.postcomposeFamily` turns an actual group-scheme homomorphism
  into a multiplicative natural family, ignoring the parameter section.
- `baseChangePointsEquiv_baseChangeIso_inv` and
  `coordinateBaseChangeHom_points` compute the canonical normalization on
  arbitrary tests using the pullback adjunction.
- `actsBy_postcomposeFamily_of_coordinateBaseChangeHom_eq` and its converse
  `coordinateBaseChangeHom_eq_of_actsBy_postcomposeFamily` identify an actual
  normalized monomial pullback with the all-test `ActsBy` formula over that
  base map. The forward argument regards any original-base test factoring
  through `p` as a test over `A`; the reverse argument uses all tests over
  `A` and group-scheme morphism extensionality.
- `exists_open_coordinateBaseChangeHom_eq_of_residue_eq` gives the same
  neighbourhood assertion for any prescribed rectangular integer matrix.
- `coordinatePermutationMatrix σ` has row `j` equal to the single-entry
  vector at `σ j`. Its character projection is proved equal to the actual
  coordinate permutation, giving
  `exists_open_coordinatePermutation_of_residue_eq` and the constructor.

This is a derived internal ingredient. The general family locality proof
uses the published `HomFamily.isLocallyConstant_actsAtPoint`, obtains an
open on which the prescribed matrix locus is constant, and applies
`actsBy_of_forall_actsAtPoint_on`. Those imported results use the idempotent
coefficients of the actual torus family, so the conclusion applies over
nonreduced bases. The actual-map bridge uses the published pullback point
equivalence, its compatibility with postcomposition, and the canonical
split-torus coordinate formulas. The permutation specialization follows by
the all-test monomial formula for `characterProjection` and finite-product
simplification of single-entry rows. The final constructor chooses an open
from the proved existence statement; it asserts no uniqueness.

For the supplied relative-Borel Weil-presentation problem, this result
provides the locality step once an actual residue-fibre permutation is
known. It does not construct quotient charts, prove their residue-fibre
comparison, assemble an etale permutation atlas, or prove effective
descent. Those remain separate obligations of the host task.
