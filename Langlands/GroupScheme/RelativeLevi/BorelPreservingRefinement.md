# Affine fppf Borel-preserving refinements

For reductive group schemes G and H over a quasi-compact scheme S, actual
relative Borel inclusions i : B to G and j : B' to H, and a natural local
group isomorphism e on a single fppf cover U of S,
`LocalGroupIso.borelPreservingFppfRefinement` constructs a single affine
fppf cover V of S, a comparison map V to U and an actual point f : V to G.
The refined local family twisted by conjugation with f identifies the full
ranges of i and j on every relative scheme test.

The input morphism U to S is flat, surjective and locally of finite
presentation. Its total space need not be affine or quasi-compact. The
comparison V to U is only required to be a morphism over S: it is not
asserted to cover U. The output cover V to S is flat, surjective and locally
of finite presentation and has affine total space. The record
`BorelPreservingFppfRefinement` retains all these properties together with
the actual map, cochain and subgroup-preservation proof.

The proof reuses `LocalGroupIso.borelPreservingRefinement`, which constructs
an etale surjective refinement with the required conjugation and subgroup
preservation by actual relative Borel conjugacy. Its parameter scheme is an
fppf cover of S by composition. Applying `affineFppfRefinement` to that
parameter gives the affine fppf cover V. Composing its comparison map with
the original refinement and pulling back the original cochain preserves
the subgroup-range equivalence by associativity. Thus no new conjugacy or
geometric-fibre assertion is needed here.

If a supplied action c of A on G restricts to conjugation along a group
homomorphism q : G to A, the twist by the image f followed by q preserves
the same full subgroup ranges. This follows from the existing identity
`twist_conjugation_eq`. The image twist also retains any supplied
all-refinement inner discrepancy, by the existing refinement and twist
lemmas. Retention of inner discrepancy itself requires neither action
faithfulness nor compatibility with conjugation; the compatibility is
needed for the subgroup-preservation conclusion.

The provenance is internal: this module composes published actual
Borel-preserving refinement, affine fppf refinement and local-isomorphism
transport results. It constructs no Borel subgroup, special quasi-split
form, unipotent filtration or induced-torus presentation. Those geometric
inputs and the unconditional semi-local inner-form statement remain
separate obligations.
