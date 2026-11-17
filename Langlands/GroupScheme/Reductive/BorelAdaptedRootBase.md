# Coordinate root bases adapted to a supplied relative Borel

Let `R` be any commutative ring, `G` a reductive group scheme over
`Spec R`, and `i` a closed fibrewise maximal coordinate torus in `G`.
Let `P` be a fibrewise root datum for that actual inclusion. For a
supplied relative Borel `j` containing the range of `i` and any point
`s` of `Spec R`,
`AffineRegularBorel.exists_base_adapted_to_suppliedBorel` produces:

- a single integral exponent vector `n` pairing nontrivially with every
  root of `P`;
- a base `b` of `P` whose positive roots are exactly the roots with
  positive dot product against `n`;
- equality of the whole dynamic centralizer of the global coordinate
  cocharacter `cocharacter i n` with the range of `i`;
- an open immersion `p : U ⟶ Spec R` whose image contains `s`, on which
  the range of the pulled-back supplied Borel is the dynamic parabolic
  of the pullback of that same fixed-exponent cocharacter.

`AffineRegularBorel.AdaptedBorelRootBaseData i j P s` packages these
witnesses as data: the exponent and root base, regularity and sign
proofs, the global centralizer equality, the neighbourhood scheme and
projection, its open immersion and containment proofs, and its equality
with the supplied Borel. `AffineRegularBorel.adaptedBorelRootBase`
chooses such a package from the existence theorem with exactly the same
reductivity, closed maximal torus, fibrewise root datum, Borel and
containment hypotheses. The choice asserts no uniqueness or canonical
chamber on disconnected bases.

These are equalities of subgroup functors on all scheme tests. The
coordinate inclusion is retained throughout. There is no connectedness,
reducedness, integral-domain or positive-rank assumption on `R` or the
coordinate torus. The local assertion takes a base point as input, so it
makes no existence assertion for a point of an empty spectrum.

`splitTorus.exists_exponentCocharacter_eq_on_field` first normalizes an
arbitrary cocharacter of a coordinate torus on one specified field
fibre. After the canonical split-torus identification, its integral
coordinate vector determines a global fixed-exponent cocharacter with
the same pullback on that field fibre. This uses the field coordinate
equivalence and the arbitrary-base exponent base-change formula; it
does not assert that all global cocharacters have constant exponent
vectors over disconnected bases.

`AffineRegularBorel.regularExponent_of_centralizer_field` uses one supplied
field-valued fibre. The closed torus inclusion represents the whole
dynamic centralizer there, after the canonical coordinate
identification. The published centralizer regularity theorem forces
nonzero pairing with every actual root. The fibrewise root datum and
the character/cocharacter dot-product formula identify these pairings
with the asserted integer sums.

`CoordinateRootDatum.exists_base_of_regularExponent` uses the published
regular-coweight base construction. Its simple roots have positive
pairing, and positive-root induction identifies all positive roots with
the roots of positive integer pairing.

`RelativeLevi.exists_open_borelPresentation_of_residue` retains an
arbitrary prescribed torus cocharacter presenting the supplied Borel on
the residue fibre. Containment in the monic Borel gives its factorization
through that Borel. The published local-presentation theorem spreads
the residue-fibre equality to an open neighbourhood and retains the
given field point. Evaluating that lift at the field's unique point
proves that the neighbourhood contains `s`.

The main construction applies `exists_residueBorelCocharacter` to the
supplied Borel, normalizes its cocharacter on the residue fibre, and
transfers both the parabolic and centralizer equalities to the fixed
exponent. Giving the residue field its actual `R`-algebra structure
permits the fibrewise root-datum tests above. They give regularity and
the adapted root base. The published
`AffineRegularBorel.centralizer_eq_range_of_mono` gives the global
centralizer equality, and the preceding local-presentation helper gives
the neighbourhood.

This is a derived construction from the published residue-cocharacter,
root-base, fibrewise-root-datum, centralizer and dynamic
local-presentation results. It supplies the local choice of a Borel
chamber needed for the adjoint-torus atlas. It does not construct
comparisons between root data on different charts, prove local
simple-root permutation transitions, or perform effective descent.
