# Compatibility of normalized CM witnesses on a common test

`levelDataBaseChange_eq_witness` compares two direct pullbacks along
equal base maps. It uses equality transport of the action object as the
rational isomorphism and multiplier one. Under the specified equality of
the transported representatives, this is a witness of the polarized
isogeny and level relation.

`pulledWitness_square_compatible` treats two maps to the same base and a
connected locally noetherian test with maps to their sources whose
composites agree. Start with two pointed representatives on the base,
with the positive object and numerical conditions on the first. Supply
witness isomorphisms between their restrictions to each source and the
indicated compatibility of the re-presented orbits.
The theorem shows that the pulled-back witness isomorphisms commute with
the canonical square comparisons on the common test. It assumes
geometric-point Hom faithfulness and geometric rigidity at the level in
use.

The proof pulls the two witnesses back to the common test. The
composition comparisons and equality-transport comparisons give
witnesses with multiplier one, so composition and inversion put both
pulled-back witnesses between the same directly pulled-back
representatives. The positive object and numerical conditions of the
first representative persist under pullback. Connected-base uniqueness
gives equality of the resulting rational isomorphisms. Cancelling the
direct-to-iterated comparisons gives the square equation.
