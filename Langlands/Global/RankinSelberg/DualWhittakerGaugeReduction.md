# Translated dual Whittaker majorization from the generic gauge input

This internal reduction for Task 7262 is conditional on
`WhittakerSimpleRootMajorizationStatement`. It does not prove that analytic
statement or the rectangular Mellin convergence statement. The imported gauge
interface and majorization proposition are published Library declarations.
Their publication states the analytic premise; a proof of that premise is still
required.

`dualCuspSpaceEquiv` is the complex linear equivalence from the realization's
vector space to `iotaSpace (cuspSpace T)`, obtained by composing the published
`cuspEquiv` and `iotaSpaceEquiv`. Its coercion to a function is exactly
`dualFunction (cuspFunction v)`, as proved by `coe_dualCuspSpaceEquiv`.

For every number field `F : Type u`, every actual cuspidal realization `T` of
rank `r + 1`, and the retained compactness assumption on `AdeleQuotient F`,
`dualCuspWhittaker_majorization_of_simpleRoot` produces real exponents `β` and
`τ ≥ 0`. They are independent of the standard additive character and vector.
For each such character and vector it produces an adelic simple-root gauge `Ξ`
with

`‖dualFunction (cuspWhittaker ψ v) g‖ₑ ≤ ofReal(detNorm(g)^β) * Ξ(g)`.

The proof reuses the published
`EqualGaugeDualSpecialization.exists_norm_iotaCuspSpace_le`, which transfers
the dual cusp function central power bound from `CuspCentralBound` to every
vector of `iotaSpace (cuspSpace T)`.
The published `whittakerDecayClass_iotaSpace` supplies the decay-class hypothesis
for this space. The generic majorization premise is applied to the inverse
standard character and the image of the cusp vector. The published identity
`dualCuspWhittaker_eq_whittaker` identifies the resulting Whittaker function
with the desired dual function.

`detNorm_unfoldingWeyl` proves that the actual unfolding Weyl representative
has determinant norm one. Directly unfolding its block definition shows it is
its own inverse. Multiplicativity makes its determinant norm square equal to
one; positivity selects the value one.

Finally, `translatedDualCuspWhittaker_majorization_of_simpleRoot` gives the same
estimate after right translation by `unfoldingWeyl F h` for any `h : t < r`.
The algebraic helper `unfoldingWeyl_mem_standardCompact` places that
representative in the actual standard compact subgroup. Right compact
invariance of the gauge and the determinant norm identity leave the majorant
unchanged. This is exactly the pointwise input expected by
`rectWhittakerGaugeBound_of_simpleRootGauge`.

These claims are derived from the named Library results, the separately
reviewed compact Weyl helper, and the explicit generic majorization premise.
They assert no independent analytic convergence theorem.
