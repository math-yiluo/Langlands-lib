# Whittaker multiplicity one over every nonarchimedean local field: proof

Author: Worker 5089.

`Langlands.Whittaker.localFieldMultiplicityOne.{uF,uV}` proves exactly the published
`Langlands.Whittaker.LocalFieldMultiplicityOneStatement.{uF,uV}` from
`Langlands.Representation.Whittaker.LocalFieldMultiplicityOneStatement`, unapplied and
with the statement module imported unchanged:

```lean
theorem Langlands.Whittaker.localFieldMultiplicityOne :
    LocalFieldMultiplicityOneStatement.{uF,uV}
```

So for every field `F : Type uF` with `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]` (any characteristic), every `n`, every complex carrier
`V : Type uV`, every bundled nontrivial continuous unitary additive character `ψ`, and
every admissible irreducible representation `ρ` of `GeneralLinear (n + 1) F` on `V`: for
`ℓ₁ ℓ₂ : glFunctionals ψ n ρ` with `ℓ₁.val ≠ 0` there is a unique `c : ℂ` with
`ℓ₂ = c • ℓ₁`. Rank one (`n = 0`) and the zero second functional are included; no
existence of a nonzero Whittaker functional is asserted.

## Inputs

- `Langlands.LocalField.gelfandKazhdanContragredient`, in
  `Langlands.Representation.Smooth.Contragredient.LocalFieldGelfandKazhdan` (this
  submission): an equivalence `E : V ≃ₗ[ℂ] SmoothDual ρ` intertwining `ρ ∘ (inverse
  transpose)` with the smooth contragredient, over every nonarchimedean local field.
- `Langlands.Whittaker.LocalField.shalikaDistributionInvariance`, in
  `Langlands.Representation.Whittaker.LocalFieldShalikaInvariance` (this submission):
  every distribution on `GeneralLinear (n + 1) F` that is bi-equivariant for the standard
  character of a bundled character is invariant under the Weyl-conjugated transpose, over
  every nonarchimedean local field.
- The published `Langlands.Whittaker.smoothDualFunctionalTransport` and
  `smoothDualFunctionalTransport_ne_zero` (`BundledDualTransport`),
  `generalizedCoefficient_isBiEquivariant` (`CoefficientDistribution`) and
  `generalizedCoefficientKernel` (`GeneralizedCoefficientKernelProof`). These are stated
  for a general field or group and are used exactly as in the p-adic proof.
- The published `RankinSelberg.generalLinearHaar F n` and
  `RankinSelberg.generalLinearHaarSymmetries F n`, stated for every nonarchimedean local
  field.

## Implemented proof

The proof is the published p-adic proof `Langlands.Whittaker.multiplicityOne`
(module `MultiplicityOneProof`) with the two p-adic inputs replaced by the all-field
theorems above. Instead of the canonical structures of a `PadicField`, the topological
instances on `G = GeneralLinear (n + 1) F` (Hausdorff, locally compact, second
countable, nonarchimedean, totally disconnected) and on `F` (Hausdorff, totally
disconnected) are installed from `Langlands.Group.GL.LocalFieldTopology` with
`attribute [local instance]`.

1. Give `G` its Borel measurable space and let `μ = RankinSelberg.generalLinearHaar F n`.
   `generalLinearHaarSymmetries` gives inversion invariance of `μ`; composing its
   transpose-preservation law with its conjugation-preservation law at the long Weyl
   element `weylLong (n + 1) F` shows that `weylTransposeHomeomorph n F`
   (`g ↦ J gᵗ J`) preserves `μ`. In the p-adic proof the same composition is the private
   helper `weylTranspose_preserves_haar`; here it is inline.
2. `LocalField.gelfandKazhdanContragredient F n V ρ hAdm hIrr` gives `E` and its
   equivariance. Put `η = smoothDualFunctionalTransport ψ ρ E hE ℓ₁`, a functional in
   `glInverseFunctionals ψ n (smoothContragredient ρ)`, nonzero by
   `smoothDualFunctionalTransport_ne_zero` because `ℓ₁.val ≠ 0`.
3. For each `ℓ : glFunctionals ψ n ρ`, the generalized coefficient distribution
   `generalizedCoefficient μ ρ hAdm.1 ℓ.val η.val` is bi-equivariant for `ψ.scale (-1)`
   (`generalizedCoefficient_isBiEquivariant`). `LocalField.shalikaDistributionInvariance F
   n (ψ.scale (-1))` makes it Weyl-transpose invariant.
4. `generalizedCoefficientKernel` applied to `G`, `μ`, `ρ`, the involutive and
   multiplication-reversing `weylTransposeHomeomorph n F`
   (`weylTransposeHomeomorph_involutive`, `weylTransposeHomeomorph_mul`), the measure
   preservation of step 1, the submodule `glFunctionals ψ n ρ`, the nonzero `η.val` and
   the invariance equations of step 3 gives the unique scalar `c` with `ℓ₂ = c • ℓ₁`.

## Provenance

The statement is Bernstein–Zelevinsky (1976), Theorem 5.16 (printed p.50), registered as
`bernstein-zelevinsky-1976-representations-gln`; its Markdown records the
correspondence. This proof module is an internal composition of the published p-adic
argument with the all-field inputs of this submission. It introduces no new
transcription from the literature. The source of each input is recorded in its own
Markdown: Shalika (1974), Theorem 1.6, for `LocalFieldShalikaInvariance`, and
Bernstein–Zelevinsky (1976), Theorem 7.3, for `LocalFieldGelfandKazhdan`. The
topological instances come from `LocalFieldTopology`.
