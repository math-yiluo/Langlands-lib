# Exact subgroup Haar shear for the signed Fourier kernel

This internal derived module proves the actual substitution
`(u,g) ↦ (u,u g)` on a subgroup times its ambient group, then applies it
to the signed original matrix Fourier kernel. It asserts no gamma equation.

The general section assumes a measurable group `G`, a subgroup `H` with a
measurable inclusion, S-finite measures `μH` and `μG`, and left invariance
of `μG`. `subgroupLeftHaarShear` is a measurable equivalence whose inverse
is `(u,g) ↦ (u,u⁻¹ g)`. The subgroup coordinate is fixed.
`measurePreserving_subgroupLeftHaarShear` uses Mathlib's
`MeasurePreserving.skew_product`, with exact left invariance on every
ambient fiber. The resulting `integrable_subgroupLeftHaarShear_iff`
preserves absolute convergence in both directions.
`integral_subgroupLeftHaarShear` preserves the total Bochner integral
without requiring convergence. Neither measure is scaled.

The canonical p-adic section retains arbitrary `PadicField.{uF} p`, with
`p` prime, every natural `n` including zero, every unitary additive
character `ψ`, and the same supplied additive Haar measure `ν`.
Write `r = n+1`, `χ = standardCharacter ψ n`, `W = rankOneSignedWeyl n`,
and `d(g) = determinantWeight abv g r`. For actual ambient matrix
Schwartz–Bruhat tests `Φ, Ψ`, the sheared kernel is

```text
d(g) χ(u)⁻¹ Φ((u g).val) Fourier(Ψ)((W g).val).
```

Here Fourier is the existing plus rectangular Fourier integral for `ψ,ν`.
`signedUnipotentGeneralLinearFourierOriginalKernel_shear` proves that
this is the signed original kernel evaluated at the actual shear.
The determinant-power character is one on `u`, and associativity cancels
`u⁻¹ u` in `(W u⁻¹)(u g)`. In particular, this is a proved substitution
in the true group and matrix arguments.

`integrable_generalLinear_signedUnipotentMatrixFourierShearedKernel`
transfers the original signed kernel's genuine product convergence,
assuming self-duality of `ν` and that `Φ` has topological support in the
invertible matrix locus. It needs no box support condition on `Ψ`.
`integral_generalLinear_signedUnipotentMatrixFourierShearedKernel`
gives exact equality of the two total product integrals even without
these convergence hypotheses. The measures are the unchanged
`unipotentHaar F.Carrier n` and `generalLinearHaar F.Carrier n`.

The provenance is source-free derived content: measurable fiberwise
left translation proves Haar transport, WeightedSynthesis supplies
unipotent triviality of the determinant power, and SignedGLFourier
supplies the original kernel and its absolute convergence.
