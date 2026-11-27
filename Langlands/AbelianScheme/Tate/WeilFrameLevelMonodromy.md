# Source coordinates, continuity and finite orbits of Weil-frame monodromy

This module works with the full Weil-compatible adelic frames
`WeilAdelicFrame` of an arbitrary abelian scheme `A` over a quasi-separated
scheme `S`, with arbitrary dual data, polarization map, rational action
`i : D →ₐ[ℚ] End0 A`, rational module `V` with form `ψ`, and geometric point
`s`. Write `H` for the scalar-extension similitude group
`ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ`, acting on frames
from the right by precomposition (`weilAdelicFrameRightAction`), and `Γ` for the
geometric fundamental group `FundamentalGroup s hs`, acting on frames from the left
through `weilAdelicFrameMonodromyAction` with the published
`rationalWeilGeometricTransport`. Coordinates use rational PEL conditions
`hPEL : RationalPELConditions σ ψ` and `Nontrivial V`, through the published
equivalence `weilAdelicFrameSourceEquiv : H ≃ Frame` at a chosen frame `eta`.

## Coordinates

* `weilAdelicFrameSourceEquiv_eq_right`, `_one`, `_mul`: the coordinate of `g` is
  the right translate of `eta` by `g`; the identity coordinate is `eta`; a product
  of coordinates is successive right translation (from `right_one` and
  `right_mul`).
* `weilAdelicFrameSourceOrbit_eq_iff`: for any subgroup `K` of `H`, the raw right
  `K`-orbits (`RightOrbit.mk K`) of the frames with coordinates `g` and `k` agree
  exactly when `g⁻¹ * k ∈ K`. Forward: a translating element `w ∈ K` gives
  `k = g * w` by injectivity of the coordinate equivalence. Backward: `g⁻¹ * k`
  translates.

## Coordinate monodromy

`weilAdelicFrameCoordinateMonodromy eta : Γ →* H` sends `γ` to the coordinate of
`γ • eta`. The homomorphism laws follow by injectivity of the coordinates, the
multiplication law and commutation of the two actions (`right_comm`).
`weilAdelicFrameCoordinateMonodromy_spec` is its defining equation and
`weilAdelicFrameSourceEquiv_monodromy` shows that monodromy is left multiplication
in coordinates: `γ • coord eta g = coord eta (ρ γ * g)`.
`weilAdelicFrameSourceOrbit_stabilizer_iff` says that `γ` fixes the raw `K`-orbit of
the frame with coordinate `g` exactly when `g⁻¹ * ρ γ * g ∈ K`; with `g = 1`,
`weilAdelicFrameOrbit_base_fixed_iff` says the raw orbit of `eta` is fixed by all of
`Γ` exactly when `ρ` lands in `K`.

## Topology

The rational Tate module carries `rationalTopology`; the source
`(Global.FiniteAdeles ℚ) ⊗[ℚ] V` carries its module topology, and the named carrier
`ScalarExtensionSimilitudePoints` its operator topology.

* `weilAdelicFrameScalarLinear` regards a frame as linear over the finite adeles,
  using `scalarExtensionAlgebraModule_one_tmul_smul` and
  `finiteAdeleAlgebraAction_tmul`; `continuous_weilAdelicFrame` gives forward
  continuity by `IsModuleTopology.continuous_of_linearMap`, with
  `rationalFull_topologicalAddGroup` and `finiteAdeleModule_continuousSMul`.
* `weilAdelicFrameEvaluation eta g x` evaluates the frame with coordinate `g` at
  `x`. The function-valued map `weilAdelicFrameEvaluation eta`, sending `g` to the
  whole function `x ↦ weilAdelicFrameEvaluation eta g x` from the source to the
  rational Tate module, is injective (`weilAdelicFrameEvaluation_injective`):
  equality of these functions at every `x` determines the underlying linear
  equivalence (`LinearEquiv.ext`), hence the frame (a subtype of linear
  equivalences) and its coordinate. Evaluation at a single `x` is not injective in
  general (at `x = 0` every frame gives `0`). With the product topology on the
  function space, the function-valued map is continuous
  (`continuous_weilAdelicFrameEvaluation`, by `continuous_pi`): its coordinate at
  `x` is `ScalarExtensionSimilitudePoints.continuous_apply x` followed by
  `continuous_weilAdelicFrame eta`.
* `continuous_weilAdelicFrameCoordinateMonodromy_of_fixed`: if the raw orbit of
  `eta` at a compact open level `K` is fixed, `ρ` lands in the compact subgroup `K`.
  The same function-valued map `weilAdelicFrameEvaluation eta`, restricted to `K`,
  is a continuous injection from a compact space into the product of copies of the
  Hausdorff rational Tate module (`rationalFull_t2Space`), hence an embedding. Its
  composite with `ρ` is continuous by `continuous_pi`: the coordinate at `x` sends
  `γ` to the value of `γ • eta` at `x`, which is the monodromy of `eta.1 x` and is
  continuous by `continuous_rationalFullMonodromy`. Hence `ρ` is continuous.
* `weilAdelicFrameOrbit_stabilizer_isOpen_of_fixed`: under the same hypothesis the
  stabilizer in `Γ` of every raw orbit at every compact open level `K'` is open,
  being the preimage of the open subgroup `K'` under the continuous map
  `γ ↦ g⁻¹ * ρ γ * g`.
* `CompactOpenLevel.cosetImage_finite`: in a topological group, the image of a
  compact open subgroup `K` in the discrete quotient by an open subgroup `K'` under
  `k ↦ k g` is finite.
* `weilAdelicFrameOrbit_finite_of_fixed`: under the same hypothesis every
  monodromy orbit of raw orbits at every compact open level `K'` is finite: by the
  coordinate formula the orbit of the class of coordinate `g` is the image of the
  finite set of cosets `ρ(γ) g K'` with `ρ(γ) ∈ K`.

Provenance: internal. The module generalizes, from the Harris integral-action
family to arbitrary frames and with coordinates taken in `H` itself, the
constructions of the modules `HarrisIntegralCMLevelMonodromy`,
`HarrisIntegralCMLevelFiniteOrbits`, `HarrisIntegralCMLevelContinuousMonodromy` and
`HarrisIntegralCMLevelContinuousOrbits`; it combines the published frame
coordinates, frame actions and Tate-module topology results named above.
