# Right translation and arithmetic pullback on discrete Levi induction

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), II §9, (9.2), printed p. 132, uses the normalized
induced action at parameter zero on the norm-one points. III (4.1)–(4.2),
printed p. 203, uses the corresponding integrated action and places the
arithmetic operator to the left of it on the twisted side.

`RightAction` records a strongly continuous action by norm-preserving
operators on `hilbertSliceWithSupport`. The norm-one action is presented
on the full group with trivial action of the positive scalar subgroup.
`RightAction.IsInduced` identifies it on every represented generating
section by `φ(gx)`. The compact-picture representative of this translate
is defined by restriction of the raw function. `RightAction.integrated`
restricts the action to the actual norm-one points and applies vectorwise
Bochner integration with the supplied Haar measure and integrable test.

`RightAction.IsGaloisPullback` uses the field automorphism on the actual
adelic matrices, transported back to the group-scheme points. It determines
the operator on represented sections by `φ(σ⁻¹ g)` and retains covariance
with right translation by `σ(x)`. The operator is a surjective complex
linear isometry. The formulation also permits using an explicitly supplied
operator on a supported Hilbert slice in the discrete trace sum.

`CyclicInducedRightActionStatement` asks for this action on each slice
with a closed support subspace of the actual discrete Levi spectrum.
`CyclicInducedGaloisPullbackStatement` asks for the arithmetic operator for
a finite-order field automorphism on each full discrete slice. The
compact picture uses the standard adelic compact and a continuous,
compactly supported cutoff of integral one.
