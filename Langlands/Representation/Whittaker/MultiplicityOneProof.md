# Whittaker multiplicity one: proof

Author: Worker 16.

`Langlands.Whittaker.multiplicityOne.{uF,uV}` proves exactly the published
`Langlands.Whittaker.MultiplicityOneStatement.{uF,uV}`. The target and its
imported Lean/Markdown pairs are unchanged. The theorem retains every prime,
every specified `PadicField.{uF} p`, every positive rank `n + 1`, the independent
carrier universe `uV`, every bundled nontrivial continuous unitary additive
character, and the admissibility and irreducibility hypotheses.

For any two elements `ℓ₁` and `ℓ₂` of the actual standard Whittaker-functional
submodule, the hypothesis `ℓ₁.val ≠ 0` yields

```text
∃! c : ℂ, ℓ₂ = c • ℓ₁.
```

No existence of a nonzero Whittaker functional is asserted. The zero second
functional and rank one (`n = 0`) are included.

## Published inputs

The proof composes the following published declarations by their Lean names.

- `Langlands.gelfandKazhdanContragredient`, in
  `Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof`,
  gives an actual complex linear equivalence
  `E : V ≃ₗ[ℂ] SmoothDual ρ` intertwining inverse transpose on the original
  representation with its actual smooth contragredient.
- `Langlands.Whittaker.smoothDualFunctionalTransport`, in
  `Langlands.Representation.Whittaker.BundledDualTransport`, uses this
  equivalence and long-Weyl translation to construct an inverse-character
  functional on that smooth dual. Its nonvanishing theorem preserves the
  nonzero first functional.
- `Langlands.Whittaker.generalizedCoefficient_isBiEquivariant`, in
  `Langlands.Representation.Whittaker.CoefficientDistribution`, identifies the
  covariance of the actual generalized-coefficient distributions.
- `Langlands.Whittaker.shalikaDistributionInvariance`, in
  `Langlands.Representation.Whittaker.DistributionInvarianceProof`, proves
  Weyl-transpose invariance of every such bi-equivariant algebraic
  distribution.
- `Langlands.Whittaker.generalizedCoefficientKernel`, in
  `Langlands.Representation.Whittaker.GeneralizedCoefficientKernelProof`,
  converts invariance of all generalized coefficients with one fixed nonzero
  smooth-dual functional into unique scalar proportionality in the chosen
  submodule of the full algebraic dual.

These are theorem applications. In particular, the distribution invariance
and contragredient equivalence are discharged by their public proofs.

## Haar measure and topology

For the given field, the proof installs its canonical normed field, canonical
valuation and canonical nonarchimedean local-field structure. On
`G = GeneralLinear (n + 1) F.Carrier` it chooses the Borel measurable space.
Local compactness of the finite matrix space uses its finite-product instance.
The published `valuativeGeneralLinearNonarchimedean` supplies a
`NonarchimedeanGroup G`; Mathlib then supplies total disconnectedness.
These are derived structures on the target's existing group and topology.

The measure is the existing
`Langlands.RankinSelberg.generalLinearHaar F.Carrier n`.
Its Haar and right-invariance instances are the published ones. Inversion
invariance comes from
`Langlands.RankinSelberg.generalLinearHaarSymmetries`.

The only private helper, `weylTranspose_preserves_haar`, composes that same
theorem's transpose-preservation law with its conjugation-preservation law at
the long-Weyl element. The composite is definitionally the existing
`weylTransposeHomeomorph n F.Carrier`, namely `g ↦ J * gᵗ * J`.
Thus it supplies precisely the measure-preservation premise of the kernel
criterion. Involutivity and multiplication reversal use the existing
Weyl-transpose lemmas.

## Representation and distribution assembly

Given admissible irreducible `ρ` and `ℓ₁.val ≠ 0`, obtain `E` and its
equivariance from `gelfandKazhdanContragredient`. Set

```text
η = smoothDualFunctionalTransport ψ ρ E hE ℓ₁.
```

This is an element of
`glInverseFunctionals ψ n (smoothContragredient ρ)`; explicitly,
`η(v) = ℓ₁(ρ(J)(E.symm v))`. Its underlying algebraic functional is nonzero
by `smoothDualFunctionalTransport_ne_zero`.

For each `ℓ : glFunctionals ψ n ρ`, form
`generalizedCoefficient μ ρ hAdm.1 ℓ.val η.val`.
The coefficient-distribution bridge proves bi-equivariance for
`ψ.scale (-1)`. This sign is essential: with the published translation
conventions the left covariance uses `ℓ` at an inverse unipotent, and the
right covariance uses the inverse-character functional `η`. Both factors
are consequently the standard character for `ψ.scale (-1)`.

Apply `shalikaDistributionInvariance` at this scaled bundled character to
each coefficient distribution. This supplies the full family of
Weyl-transpose invariance equations required by the kernel criterion, with
the same fixed nonzero `η`. Apply `generalizedCoefficientKernel` with
`W = glFunctionals ψ n ρ`, the chosen Haar measure and the existing
Weyl-transpose homeomorphism. Its conclusion is already the target's unique
scalar equality in that submodule; no additional identification of
functional spaces or dimension argument is needed.

All constructions use algebraic distributions on the existing test-function
space and the actual smooth dual. The representation carrier has no added
topology or finite-dimensionality hypothesis. Rank one follows from the same
applications, and the field and carrier universes remain independent.

## Provenance

This module is an internal composition of published interfaces, authored by
Worker 16 from the earlier one-premise assembly draft. Its Haar adapter is the
direct composition described above. It introduces no new transcription from
the literature. The companion Markdown of the unchanged target records the
JPSS scalar multiplicity statement; the imported Shalika, Gelfand–Kazhdan,
kernel and transport modules record their respective original sources,
implemented deductions and authorship. The proofs of those imported
declarations are reused by import.
