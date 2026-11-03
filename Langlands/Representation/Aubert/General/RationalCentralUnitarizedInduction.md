# Central unitarization on the actual rational-point families

This internal adapter specializes the ambient central-unitarization construction
to the actual standard parabolic, Levi and unipotent rational-point subgroups.
It uses the canonical `pointTopology`, literal `SimpleRoot i ν` labels and
independent field and representation universes, with representation carriers in
`max (u + 1) v`.

`center_le_standardLevi` derives containment of the full abstract ambient center
in every actual standard Levi from the original point-centralizer comparison.
Every central point centralizes the torus image; the existing
`pointCentralizer_le_levi` then gives the containment. No comparison between the
scheme center and the full abstract center is assumed in this step.

`rationalInductionCentralUnitarizingCharacter` restricts the supplied inducing
scalar character to the ambient center and applies the actual
`rationalCentralUnitarizer`. This uses the actual rational-character valuation
image, whose projection has a proved open kernel. The central torus map, finite
index of its actual valuation image and compactness of the common norm kernel
on the full abstract center remain explicit structural inputs.

`rationalCentralUnitarizedInducingObject` twists the original finite-length
inducing representation by the restriction of this ambient character. Its
irreducibility follows from scalar-twist irreducibility, and its finite length
follows from irreducibility. This does not require any finite-length-preservation
theorem for induction. Admissibility is preserved as an equivalence, without
asserting that an arbitrary original inducing object is admissible.

`rationalCentralUnitarizedInductionUnitaryCentralCharacter` constructs a unitary
scalar action of the full abstract ambient center on the actual normalized
induction of that twisted inducing object. The standard-cocharacter premise
gives compact-limit radicals by the existing dynamic unipotent compact-containment
proof. Positive open-kernel characters therefore kill these actual radicals.
The actual induced-function twist equivalence transports the rational ambient
unitary-central-character datum to this induction.

The induction irreducibility and inducing cuspidality equivalences preserve irreducibility of the actual normalized
induction and the exact original inside-Levi cuspidality condition. The latter
uses the actual restricted standard subgroups and derives all needed radical
triviality from the same standard-cocharacter premise. Consequently the original
reducibility and cuspidality hypotheses survive this central unitarization.

`exists_rationalCentralUnitarizedInducingObject` assumes that the original
irreducible inducing object is admissible. The published admissible Schur
proof then supplies its unique locally constant scalar central character;
local constancy makes the kernel open. Applying the constructions above gives
an actual finite-length inducing object that is irreducible and admissible,
with unitary central-character data on its normalized induction, together with
the irreducibility-of-induction and cuspidality equivalences. No scalar character
is an extra input to this existence theorem. Admissibility of the original
object remains an explicit premise.

These constructions compose the existing subgroup, valuation-image,
central-character and scalar-twist definitions and proofs. They introduce no
new literature assertion. Existence of a scalar character without admissibility,
admissibility of arbitrary irreducible inducing representations, the two
displayed valuation structural inputs, an invariant positive form on the whole
induction, exponent estimates, square-integrability and the self-association
theorem remain separate obligations.
