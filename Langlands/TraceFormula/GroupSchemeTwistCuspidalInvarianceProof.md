# Twisting preserves the full almost-everywhere cuspidal subspace

`Langlands.TraceFormula.groupSchemeTwistCuspidalInvariance` proves
`GroupSchemeTwistCuspidalInvarianceStatement` at universe `u`. The statement
supplies the preservation hypotheses for the subgroup defining `[G]` and
for the quotient measure. Under those hypotheses the twisting operator
maps the full almost-everywhere cuspidal subspace of `L²([G])` into itself.

## Proof

Write `β = Θ⁻¹` for the inverse adelic automorphism and `ψ` for the pullback
of the chosen representative of `φ` by the inverse quotient automorphism.
The inverse identities for `α` identify `β` with the adelic-point map of
`α⁻¹`. By `twistOperator_coeFn`, `ψ` agrees almost everywhere with the
representative of the twisted `L²` class. Both representatives are strongly
measurable, using measurability of the inverse quotient map for `ψ`.

For each proper rational parabolic `P`, choose a closed parabolic
presentation `p` and its represented unipotent radical `r` from
`rationalParabolicRadical_spec`. Postcomposition of `p` with `α⁻¹` gives
the presentation of a parabolic `P' = α⁻¹(P)` by
`IsParabolicSubgroup.comp_iso`. The range identity `SubgroupFunctor.range_comp_iso`
and the inverse comap identity give properness. Using the same `r` in
`rationalParabolicRadical_eq` identifies the radical of `P` with the preimage
under `α⁻¹` of the radical of `P'` as subgroup functors.

The closed adelic radical and compact radical quotient instances allow
application of `AdelicSubgroupPoints.rationalQuotientIso` for `α⁻¹`. This
published isomorphism uses the correspondence on the evaluated radical
subgroups and their actual rational images. Its measure-preserving property
comes from uniqueness of the invariant probability on the compact quotient.
On representatives, `properParabolicPositivePeriodIntegrand_mk` and
`quotientAutomorphism_symm_mk` reduce the comparison to
`ψ([n g]) = φ([β(n) β(g)])`. Applying
`integrable_comp_rationalQuotientIso_iff` and `integral_comp_rationalQuotientIso`
gives the equivalence of absolute convergence and equality of the integrals
for `ψ` along `P` at `g` and `φ` along `P'` at `β(g)`, for the intrinsic
mass-one measures.

`map_normOneSubgroup_le` for `α` and `α⁻¹` makes `β` a continuous group
automorphism of `G(𝔸_F)^1`. The pushforward of its Haar measure is Haar and
absolutely continuous with respect to the original Haar measure by
`Measure.absolutelyContinuous_isHaarMeasure`. Pullback therefore carries
both almost-everywhere conditions for `φ` along `P'` to the corresponding
conditions for `ψ` along `P`. After varying `P`, the comparison
`mem_aeParabolicCuspidalFunctionSubmodule_congr` transfers cuspidality from
`ψ` to the representative of the twisted class.

## Source

Getz and Hahn define inverse pullback in display (18.33) and assert that
it preserves cuspidality, for the finite-order automorphism introduced in
§18.5. They use the restriction to cuspidal representations in the
twisted trace formula, including Corollary 18.5.1. The proof above is a
derived change-of-variables argument for the Library's almost-everywhere
cuspidality condition and applies to the arbitrary-order automorphism
with the quotient hypotheses in the published statement.
[Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
§18.5, printed pp. 486–488](https://doi.org/10.1007/978-3-031-41153-3).
