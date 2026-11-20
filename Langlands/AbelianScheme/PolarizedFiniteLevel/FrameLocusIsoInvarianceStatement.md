# The projective frame locus depends only on the isomorphism class of a datum

`Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusIsoInvarianceStatement` is a
proposition definition (universe `u`). It is a statement target only; this module proves
nothing.

## The statement

For `P : Prerequisites.{u}`, a scheme `S`, natural numbers `g d n m`, data
`a b : Datum P S g d n` and a family `ρ : Fin (m + 2) → Fin (2*g) → ZMod n` of level
coefficient tuples: if there is a polarized isomorphism `PolarizedIso a b` (module `Data`),
then `a.frameLocus ρ = b.frameLocus ρ` (module `FrameLocus`).

No hypothesis on `S` (such as local noetherianity) is made.

## Mathematical content and provenance

Internal (derived) statement; it translates no source assertion. A polarized isomorphism
`α` identifies the abelian schemes over `S`, carries every torsion section with
coefficients `r` to the torsion section with the same coefficients (it preserves the ordered
level sections), and identifies the cubic bundles (`PolarizedIso.cubicBundlePullbackIso`,
module `PolarizedBundleTransport`). Hence it identifies the cubic direct images
`a.rigidificationModule ≅ b.rigidificationModule` and the targets of the torsion
evaluations, compatibly with the torsion evaluations themselves. The frame evaluations of
`a` and `b` therefore differ by isomorphisms on both sides, so they are isomorphisms on the
same opens.

## Use

Task 7811's reduction of `FrameChartRepresentabilityStatement`
(`frameChartRepresentability_of_frameHilbertLocus`) uses it to show that every datum whose
class lies in the frame chart has frame locus `⊤`: the target statement characterizes the
image through an arbitrary representative of the class, so this invariance is needed.
