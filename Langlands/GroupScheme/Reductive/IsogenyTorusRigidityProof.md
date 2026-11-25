# Proof: isogenies agreeing on a maximal torus are locally torus conjugate

`Langlands.GroupScheme.reductiveIsogenyTorusRigidity` proves
[`ReductiveIsogenyTorusRigidityStatement`](IsogenyTorusRigidityStatement.md)
in every universe `u`, with no additional hypotheses.

For every scheme `S` and reductive group schemes with the stated maximal
tori, two isogenies carrying the source torus into the target torus agree
on the source torus if and only if they are conjugate by target-torus
points on an fppf cover. The conjugation identity holds on every scheme
over each cover member. Two conjugating points over the same `S`-scheme
differ by a point commuting with every target-group point after every
further base change. The target allows empty, disconnected and
non-Noetherian bases and non-split tori.

The Lean proof composes two published results:

1. [`affineSplitSurjectionRootDatum`](AffineSplitSurjectionRootDatumProof.md)
   proves `AffineSplitSurjectionRootDatumStatement.{u}` over every
   commutative ring.
2. [`reductiveIsogenyTorusRigidity_of_affineSplitSurjectionRootDatum`](AffineOpenIsogenyConjugacy.md)
   takes exactly that proposition and concludes
   `ReductiveIsogenyTorusRigidityStatement.{u}`.

The second result obtains compatible root data on affine open charts,
applies the supplied-root conjugator construction, and composes the
resulting fppf covers. Its coordinate-to-general-base reduction handles
arbitrary maximal tori and includes the reverse implication and uniqueness
modulo the centre. Applying it to the first theorem discharges its sole
intrinsic compatibility premise. No root datum, splitting, freeness or
affineness assumption remains in the final theorem type.

This is a derived proof by direct composition. The target's paired
Markdown records its relation to Conrad, *Reductive group schemes*
(2014), Corollary 6.1.15, second assertion. The imported proof modules
describe the implemented arguments. This module adds only the final
theorem and does not alter the target or its imports.
