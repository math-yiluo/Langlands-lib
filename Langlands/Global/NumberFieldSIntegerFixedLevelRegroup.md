# Enlarged upper number-field levels with the original integral model

This derived construction continues Conrad, *Weil and Grothendieck approaches
to adelic points* (2011), Example 4.2, printed pp.9–10. Work with actual number
fields K and L and their specified embedding, an initial finite lower support
S, and any finite support T containing S. Both original integral coefficient
rings remain fixed: A is the S-integer ring of K, and B is the integer ring
of L away from the full preimage of S. All infinite places occur.

`upperLevel` is the full preimage of T, with the proved containment of the
original upper support. `indexEquiv` reuses the existing actual-place
bijection at T: every lower-coordinate/upper-place pair becomes exactly
one original upper level coordinate. `factorPointHomeomorph` proves that
reindexing preserves the original completed ring, its fixed B-action and
its point topology. In each infinite, finite-field or integer case,
algebra extensionality identifies the coefficient actions, and the map
then is the identity. `productPointHomeomorph` takes their product and
reindexes it; its application theorem gives its exact value.

For any quasi-compact, quasi-separated B-scheme Y,
`upperPointHomeomorph` identifies its actual enlarged-level points with
the original upper coordinate product. The source has the independently
defined `numberFieldFixedModelStageTopology` and every coordinate has
`schemePointTopology`. The proof composes the fixed-base arithmetic stage
homeomorphism with the actual product-point bijection. The latter follows
from quasi-separatedness for injectivity and quasi-compactness and the
actual local coefficient rings for surjectivity; its topology comparison
is the existing inducing coordinate theorem. The coordinate theorem
identifies every component with the literal original upper level
projection on spectra.

Suppose additionally that Y is locally of finite type and has a specified
relative immersion into a finite-dimensional projective space over B.
`adelicLevelPointHomeomorph` compares actual points of the original integral
Weil model W over the lower T-level with actual points of the original Y
over the upper full-preimage T-level. Both carry their existing fixed-model
stage topologies. It composes the fixed-base local Weil homeomorphism,
the regrouping above and the inverse upper coordinate homeomorphism.
No finiteness or separation condition on W is assumed by this assembly.

`adelicLevelPointHomeomorph_coordinates` identifies the whole upper
coordinate family with the regrouped local Weil components.
`adelicLevelPointHomeomorph_coordinate_left` states the same equality after
each literal upper projection. Together with the imported local component
theorem this retains the actual local Weil counit after the literal lower
projection. Its proof uses the upper inverse identity and the exact
regrouping and projection laws.

The fields share an arbitrary universe. This unit constructs enlarged
finite-level homeomorphisms over the two original integral bases.
Compatibility with support inclusions, cofinal passage to full adelic
points and the generic-fiber comparison remain host obligations.
