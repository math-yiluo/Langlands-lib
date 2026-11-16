# The Iwahori model of a Galois-stable chamber of a simply connected group

`Langlands.GroupScheme.localSimplyConnectedUnramifiedIwahoriModel` proves
exactly `LocalSimplyConnectedUnramifiedIwahoriModelStatement.{u}` at arbitrary
universe `u`, with no additional premises.

For the original nonarchimedean local field `F`, affine simply connected
group `G` over `F`, supplied building datum `C` over
`L = inertiaFixedField F`, semilinear datum `D` and Galois-stable chamber
`Y₀`, the conclusion supplies an actual `IntegralModel 𝒪[F] F G`. This
model is smooth, its full special fibre over `𝓀[F]` has connected underlying
space, and for every rational point `g` of the original `G_L`,

```text
g ∈ M.baseChangeUnramified.integralPoints ↔ (g • ·) '' Y₀ = Y₀.
```

The proof applies the published assembly
`localSimplyConnectedUnramifiedIwahoriModel_of_inputs`. Its parahoric-model
input is the unconditional theorem
`Langlands.BruhatTits.IntegralModels.unramifiedParahoricModel`; its smooth
descent input is
`Langlands.GroupScheme.IntegralModel.unramifiedSmoothModelDescent`.

For the assembly's remaining input, the proof introduces its arbitrary
original field, group, supplied building, chamber and stabilizing point.
`isSimplyConnectedFieldExtension` gives simple connectedness of the actual
base-changed group `baseChanged F (inertiaFixedField F) G`.
`Langlands.Geometry.Building.MaximalUnramified.simplyConnectedChamberStabilizer`
then applies to this group and the same `C`, `Y₀` and `g`, proving that the
setwise stabilizer fixes the chamber pointwise. The theorem is applied over
the original local field `F`; no local-field structure on `L` is required.

The assembly obtains a nonempty bounded translated-apartment presentation
of the chamber and a zero datum for the simply connected group over `L`.
The neutral model from the parahoric theorem has integral-point image
`E.zeroPoints ⊓ C.pointwiseFixer Y₀`. Simple connectedness makes
`E.zeroPoints` the whole rational-point group. Pointwise fixation by the
setwise stabilizer therefore identifies this image with the full setwise
stabilizer of the original chamber. Galois stability under the supplied
semilinear action gives stability of this image, so smooth descent supplies
a model over the original integers with an actual compatible unramified
model isomorphism. The assembly transports the neutral model's connected
fibres and integral-point identity along that isomorphism and descends
connectedness to the full special fibre over `𝓀[F]`.

This is an internal composition of published Library results. The source
comparison with Kaletha–Prasad Theorem 8.3.13, 9.2.5–9.2.6, 4.1.12(1),
Remark 4.1.13 and 9.3.26 is in the
[unchanged statement Markdown](LocalUnramifiedIwahoriModelStatement.md).
The proof retains every original field, group, building and semilinear datum
and every stable chamber quantified by that statement. It uses no proof of
the downstream chamber, integral-twist or cocycle-vanishing statements and
leaves the target pair and its imports unchanged.
