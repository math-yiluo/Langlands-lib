# Character conductors on the actual rank-one carrier

This internal unit uses an actual representation equivalence from a complex
representation of `GL₁(F)` to the scalar character representation. The field
and carrier have independent universes. The level results require only a field
with its valuation relation; the comparison with the smoothness-constructed
conductor also uses the nonarchimedean local-field topology.

If the character is trivial on the determinant of every matrix in a level
subgroup, the intertwining relation and injectivity of the equivalence show
that every vector of the original carrier is fixed. The fixed submodule is
therefore the whole carrier. `rankOneCharacterLevelEquiv` restricts the
character coordinates to this actual submodule and gives an explicit complex
linear equivalence to `ℂ`, establishing dimension one without a dimension
premise.

If one matrix at a level has a nontrivial character value, a fixed vector has
coordinate `z` satisfying `(χ(det g) - 1) z = 0`. Hence its coordinate and the
vector vanish. Triviality at level `a` and a nontrivial value at every lower
level establish `IsNewvectorConductor π a`. Its uniqueness identifies `a`
with `rankOneConductor`, whose finite existence was proved from smoothness.

The final conditional result transports the full scalar-model epsilon
relation from `LocalTateEpsilonTransport` through the representation
equivalence, retaining the same coefficient and exponent. Together with the
level arguments this yields all three rank-one conductor conclusions on the
original carrier. It assumes the actual scalar analytic, generator and
functional-equation data with exponent `a`; it does not prove their existence
or the full essential/conductor theorem. The epsilon result uses exactly the
Hausdorff, local-field and Borel structures listed in Lean.

The provenance is internal. The level construction is linear algebra applied
to the unchanged concrete congruence and invariant-submodule definitions.
The epsilon step reuses the actual pair-relation transport along representation
equivalences and the conditional scalar-to-JPSS transport. No new
source-attributed analytic or conductor theorem is asserted.
