# Proof of the affine tensor-power Euler comparison

`lineBundleTensorPowerProjectionIso` packages `L^n` as an actual line
bundle using `tensorPow_isLocallyFreeRankOne`. It applies the actual
line-bundle projection isomorphism with coefficient sheaf `O_X`.
Inside the pushforward, the explicit tensor right unitor removes
`O_X`, and `actualPullbackTensorPowIso` identifies `f*(L^n)` with
`(f*L)^n`. This constructs the sheaf isomorphism
`L^n tensor f_*O_X ≅ f_*((f*L)^n)`.

The pulled-back bundle is locally free of rank one, and so is each
of its tensor powers. `IsLocallyFreeRankOne.isQuasicoherent` supplies
the hypothesis for `affinePushforwardEulerCharacteristic`. That
theorem identifies finite cohomology and Euler values of `(f*L)^n`
with those of its actual pushforward.

Finally `hasFiniteCohomology_of_iso` transports finiteness in both
directions across the constructed isomorphism, and
`eulerCharacteristic_eq_of_iso` identifies the Euler values for
any supplied finiteness witnesses. Composition gives the complete
`AffinePullbackTensorPowerEulerStatement`, including exponent zero
and without additional geometric hypotheses.

This proof is an internal composition of the actual categorical and
cohomological constructions named above. It does not use a numerical
degree or an Euler-polynomial assumption.
