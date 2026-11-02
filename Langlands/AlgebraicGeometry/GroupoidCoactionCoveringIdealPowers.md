# Covering ideal powers and vanishing

This internal construction uses commutative rings `B`, `C`, `D`, and `P` in
an arbitrary universe `u`, source algebra maps, target maps `t : B →+* C` and
`td : D →+* P`, and a source-cartesian equivalence
`e : P ≃ₐ[D] D ⊗[B] C`. The target compatibility is
`(cartesianBaseMap e).comp t = td.comp (algebraMap B D)`. The coaction
comparisons use the actual étale equivalence relations on these ring maps.

`pushforwardTensorEquiv_naturality` proves naturality of cartesian tensor
cancellation for covering-linear maps, by induction on tensors after applying
the inverse equivalence. `IsHom.pushforward` then transfers equivariance.
`pushforward_submodule` applies this to a stable submodule inclusion and
compares the two restricted coactions after their common inclusion. Flatness
of the base source map, obtained from étaleness, makes that tensor inclusion
injective. This comparison assumes stability on both sides.

`IsInvariantIdeal.map_cartesian` uses the target compatibility and source
identity to show that an invariant base ideal extends to an invariant ideal
of `D`. The definition `coveringIdealPowerSubmodule I n` is the `D`-submodule
`(I ^ n).map (algebraMap B D) • ⊤`. Its scalar restriction is exactly
`I ^ n • ⊤`, by Mathlib's `Submodule.restrictScalars_map_smul_eq`. This
identity requires compatible scalar actions, without flatness of `B → D`.

The vanishing results assume an actual effective presentation
`ε : P ≃ₐ[D] D ⊗[invariantRing td] D` with
`ε (td d) = 1 ⊗ d`, and faithful flatness of `D` over this invariant ring.
`submodule_pushforward_oneCohomologyVanishes` applies effective descent to a
stable covering submodule and then pushes forward its vanishing.
`idealPower_pushforward_oneCohomologyVanishes` applies this to the defined
covering ideal-power submodule. Invariance of the extended ideal gives
covering stability, while base stability is an explicit parameter. The
scalar restriction identity then gives vanishing for the specified base
ideal-power restriction.

Finally, `hom_pushforward_oneCohomologyVanishes` and
`idealPower_hom_pushforward_oneCohomologyVanishes` apply these results to the
constructed `coveringHom` coaction. Its pushforward is the actual base Hom
coaction `hom hE (pushforward e ht ψ hE hP) θ`. The source `Y` is finitely
presented over `B`; the `D`-action on `Hom_B(Y,H)` is multiplication in the
source of a linear map. This action and its scalar tower are local instances
of priority 50, preserving the ordinary `B`-action on Hom.

The comparisons allow coefficient modules in an independent universe `v`.
The vanishing results use coefficient modules in `Type (max u v)`, as
required by the effective descent construction. No Noetherianity is used.
Apart from the Hom source's finite presentation, the results require no
module finiteness. These are derived algebraic helpers for support
dévissage; they do not prove the host acyclicity statement or construct its
geometric covering presentation.
