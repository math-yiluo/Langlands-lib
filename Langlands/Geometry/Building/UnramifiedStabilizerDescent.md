# Stabilizer descent along a supplied maximal-unramified building embedding

Worker 1681. This internal unit compares the existing fixers and norm-one
stabilizers on two supplied building quotients. The base is an arbitrary
nonarchimedean local field `F : Type u`, in either characteristic. The field
upstairs is the actual `UnramifiedClosure F`, definitionally
`LocalGalois.Separable.inertiaFixedField F`, equipped with
`MaximalUnramified.valuation F`. The upstairs bundle is
`MaximalUnramified.BuildingData F` for the actual scalar extension
`GaloisPointComparison.baseChanged F (UnramifiedClosure F) G`. It uses the
integer-valued interface without a local-field instance on that infinite field.

The provenance is internal: the proofs compose the published normalized
valuation comparison, the published character-kernel descent proof, and the
existing fixer definitions. No additional assertion from the literature is
used.

`characterValuationKernel_eq_of_isEquiv` works over any field and with
independent universes for the two ordered value groups. Mathlib's
`Valuation.IsEquiv.eq_one_iff_eq_one` identifies the two conditions that a
character value has valuation one. Applying this to every rational character
proves equality of the actual character-kernel subgroups.

`MaximalUnramified.characterValuationKernel_comap` applies this equality to
`valuation_isEquiv F`, replacing the integer-normalized kernel with the
published spectral fixed-field kernel on the same field and group. The
published theorem `characterValuationKernelDescent_proof` then identifies its
preimage under the original `rationalExtend` homomorphism with
`Plancherel.rationalCommonNormKernel G`. The only group hypothesis here is
affineness over the base field.

For the building comparisons, let `B : ValuationBuildingData G` and let `C` be
the upstairs bundle just described. The function
`e : B.ReducedBuilding → C.ReducedBuilding` is supplied, with injectivity and
the identity

```text
e (g • z) = rationalExtend F (UnramifiedClosure F) G g • e z.
```

Both actions are the existing actions on the supplied KP quotients.
`fixer_comap` expands point-fixer membership into a fixed-point equation.
Equivariance and injectivity identify that equation with `g • z = z`.
`pointwiseFixer_comap` makes the same argument for every point of any subset
`Y`, using precisely its image `e '' Y`.

Finally `oneStabilizer_comap` distributes subgroup preimage over the
intersection defining `C.oneStabilizer (e z)`. Character-kernel descent and
`fixer_comap` identify the two factors with the original rational norm kernel
and `B.fixer z`. Their intersection is exactly `B.compactStabilizer z`.
All conclusions are equalities of subgroups of the original `rationalPoints G`,
with its original action.

`oneStabilizerExtend` constructs a multiplicative map from the actual subgroup
`B.compactStabilizer z` to `C.oneStabilizer (e z)`. Its underlying point is exactly
`rationalExtend F (UnramifiedClosure F) G g`, as recorded by the definitional
formula `coe_oneStabilizerExtend`. The preimage identity just proved supplies
membership in the target subgroup, and the multiplication and identity laws
are those of the original scalar-extension homomorphism. This map is
injective: the rational/coefficient equivalences identify equality of its
underlying points with equality after coefficient extension, and the published
`GaloisPoint.extend_injective` reflects that equality using affineness of `G`.
This proof requires neither finiteness nor a local-field structure upstairs.

This unit requires the two building bundles and the injective equivariant map.
Their construction, metric and geometric properties, and comparison with a
supplied integral model remain separate obligations. The subgroup named
`compactStabilizer` is the existing definition; no compactness theorem is
asserted here. In particular this helper does not prove
`IntegralModel.BuildingComparisonStatement`.
