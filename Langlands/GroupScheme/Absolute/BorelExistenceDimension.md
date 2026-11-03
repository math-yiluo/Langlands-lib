# A largest-dimension actual Borel embedding

This internal adapter takes the minimum coordinate-kernel height retained by
`BorelExistence.BorelData` and derives a largest topological Krull dimension.
The ambient group scheme is affine, smooth and connected over any field
`k : Type u`. Neither algebraic closedness nor a characteristic restriction is
imposed.

The construction keeps the actual subgroup scheme and its embedding. Its
dimension bound compares that subgroup with every closed, smooth, connected,
solvable subgroup of the ambient group, without requiring containment. This
unit supplies the dimension comparison requested for the subsequent properness
argument; it does not prove quotient properness or Borel conjugacy.

The proof uses the published
`Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType`:
in a finitely generated domain over a field, prime height plus quotient dimension
equals ambient dimension. Applying it to two prime ideals reverses their height
inequality into an inequality of quotient dimensions. Finite prime heights and
the imported natural-valued dimension lemma reduce the comparison to natural
number addition.

Smoothness and connectedness make the ambient scheme integral by the published
`CharacterLatticeProof.isIntegral_of_smooth`. Affineness and local finite type
make its global ring a finitely generated algebra over the given field; the
algebra structure is induced by the actual structure morphism and the canonical
global-sections isomorphism of `Spec k`. A closed subgroup's pullback on global
sections is surjective, so the first isomorphism theorem identifies its global
ring with the quotient by `coordinateKernel`. Finally the affine scheme's
`isoSpec` homeomorphism identifies topological dimension with ring dimension.

`BorelData.maximalDimension` proves the global bound for any existing data with
the retained minimum-height property. `MaximalDimensionBorelData` records both
that original data and the bound, and `maximalDimensionBorelData` constructs an
actual such choice from `borelData`.

The provenance is derived internal content: it combines the previously
constructed Borel data with the published commutative-algebra dimension formula,
using actual scheme pullbacks throughout. It adds no structural algebraic-group
assumption.
