# Real-point topology and root contractions

This module supplies internal, derived infrastructure for
`Langlands.GroupScheme.RealPointComponentsStatement`. All point spaces use the
Library's evaluation topology, and all group laws are the actual group-object
laws on relative scheme morphisms. No new mathematical premise is introduced.
This module alone does not prove the components statement for arbitrary simply
connected groups.

The declarations are in `Langlands.GroupScheme.RealPointTopology`.

- `rationalRingPointMulEquiv G` identifies the identity-test rational points of a
  real group scheme with its `RingPoint` carrier. Its underlying equivalence is
  the published `rationalPointEquiv`; precomposition preserves multiplication.
- `ringPointIsTopologicalGroup G`, for affine `G`, transports the published
  topological group structure on actual affine coefficient points through
  `affinePointsRingPointHomeomorph`. The comparison preserves multiplication.
- `affineLine_connectedSpace` proves connectedness of the real points of the
  actual affine line. Its spectrum presentation and the published polynomial
  evaluation homeomorphism identify this point space with a one-coordinate real
  vector space.
- `root_mem_connectedComponent_one G i a` places each rational point of the
  actual root subgroup functor in the identity component. It requires no
  root-system membership condition on the character `a`.
- `identityComponentPreimage G` is the subgroup of rational points whose
  corresponding real points lie in the identity component.
- `rootGenerated_le_identityComponentPreimage G i` places the subgroup generated
  by the relative-root points in that subgroup.
- `quasiSplitSimplyConnected_connectedSpace G hG hqs S i hi` proves connectedness
  of the real points of an affine, quasi-split, algebraically simply connected
  group, with a supplied maximal split torus `i`.

For the root contraction, membership in `RelativeRoot.subgroup i a` supplies an
orbit extension `e : T × A¹ → G` with value one at zero. Here `T` is the identity
test of the real base. The product unitor identifies `T × A¹` with `A¹`, so this
is a continuous map on the real affine-line point space: continuity is the
published continuity of postcomposition by an affine scheme morphism. At zero
the map takes the group identity. At the affine-line point obtained by evaluating
the character on the identity of the torus, the orbit-extension equation and
the action's identity law give the original root point. Its preconnected image
therefore lies in the identity component.

The identity component is a subgroup of a topological group.
`relativeRootGeneratedSubgroup_le_iff` extends the root-point containment to the
generated subgroup. Finally the published
`quasiSplitSimplyConnectedRootGenerationStatement_proof` identifies this
generated subgroup with all rational points under the simply connected and
quasi-split hypotheses. The point equivalence is surjective, so the identity
component is the entire real point space.

The provenance is internal and derived from the imported Library point
comparisons, root-subgroup definitions and root-generation theorem, together
with Mathlib's connected-space and topological-group results. The proof uses
connected components and makes no assertion about path components or the
topology on the underlying scheme.
