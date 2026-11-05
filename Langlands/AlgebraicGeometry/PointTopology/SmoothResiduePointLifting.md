# Smooth point lifting from a field residue

For an arbitrary scheme `X` smooth over `R`, the construction
`smoothResiduePointLift` lifts any actual point with values in `S / I` to an
actual `S`-valued point, when the `R`-algebra `S` is adically complete for a
maximal ideal `I`. The carrier is the existing `PointTopology.RingPoint` and
reduction is its existing change of coefficient ring by the literal quotient
algebra map. The exact reduction equation is proved. Neither affineness of `X`
nor a supplied point on its generic fibre is assumed. All types share an
arbitrary universe.

The quotient is a field, so its spectrum has one point. The proof chooses an
affine chart of `X` containing the image of that point. The entire residue point
factors through that chart by the actual open immersion. The chart is smooth
over `R`, and the affine adic lifting construction gives a point of the chart
over `S`. Postcomposition with the chart inclusion gives the required point of
`X`, retaining the prescribed reduction. The final corollary specializes to
`S = R` and concludes nonemptiness from a residue-valued point.

This is a derived complete-ring implementation of the smooth lifting step in
Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Lemma B.2.4
and the proof of Theorem B.2.5, printed pp.543–544 / PDF pp.548–549. It uses
`AdicSmoothPointLifting` and the affine open cover of the actual scheme. The
registered October 2026 errata has no correction to this passage. Choices of
chart and lift are noncomputable; no canonical choice, naturality of the lift,
general Henselian lifting theorem, torsor point theorem, arithmetic model
existence, local parabolic covering or integral maximality is asserted here.
