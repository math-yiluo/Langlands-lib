# Row Fourier closure and inversion from scalar self-duality

`Langlands.HarmonicAnalysis.rowFourierCompatibility` proves the unchanged
[`RowFourierCompatibilityStatement`](RowFourier.md). For a field `F : Type u`
with a topological ring structure, Borel measurable structure, local compactness,
the Hausdorff property and total disconnectedness, every supplied character
`ψ : UnitaryAdditiveCharacter F`, additive Haar measure `μ`, and natural number
`d` satisfy

```text
IsSelfDual ψ μ → RowFourierClosed ψ μ d ∧ IsRowSelfDual ψ μ d.
```

The transform is the actual Bochner integral against
`rowMeasure μ d = Measure.pi (fun _ : Fin d => μ.measure)`. Its kernel is
`ψ.complex (∑ i, x i * y i)`, with the inherited plus sign and no conjugation.
The conclusion supplies an actual Schwartz–Bruhat Fourier partner, convergence
of the second integral at every row, and the identity that the second transform
equals `f (-y)`.

The closing theorem's complete parameter order is the implicit carrier `F`,
the `Field`, `TopologicalSpace`, `IsTopologicalRing`, `MeasurableSpace`,
`BorelSpace`, `LocallyCompactSpace`, `T2Space`, and `TotallyDisconnectedSpace`
instances on `F`, then `ψ`, `μ`, and `d`. This is the elaborated telescope of
the published target. It has no Borel-space premise on the row space and no
sigma-finiteness premise. The proof establishes the integrability it uses from
scalar integrability and tensor decomposition.

## Published prerequisites

The module imports
[`scalarFourierClosure`](ScalarFourierClosureProof.md), which derives both
`SigmaFinite μ.measure` and scalar Fourier closure from the supplied
`IsSelfDual ψ μ`. Thus each scalar test `g` has an actual scalar test partner
`ghat` satisfying `ghat y = fourierIntegral ψ μ g y` pointwise.

It also imports
[`rowTensorDecomposition`](RowTensorDecompositionProof.md), which expresses
each row test function as a finite complex linear combination of products:

```text
f x = ∑ j : Fin N, c j * ∏ i : Fin d, g j i (x i).
```

Both are proved under the original generic topological hypotheses. Neither
conclusion is added as an assumption of the closing theorem.

## Products and integrability

The private construction `rowTensor g` bundles `x ↦ ∏ i, g i (x i)` as an
actual row test function. Finite induction proves local constancy from
coordinate evaluation and multiplication. The support lies inside the product
of the compact scalar topological supports, which is compact.

`rowFourierIntegrand_tensor` applies the additive character law to the finite
pairing sum and distributes products. It identifies the row integrand of a
pure tensor with the product of the scalar integrands. Consequently,
`rowFourierIntegral_tensor` applies Mathlib's
`MeasureTheory.integral_fintype_prod_eq_prod` to factor its integral into
scalar Fourier integrals.

The private lemma `rowFourierIntegrand_integrable_of_decomposition` uses the
same identity and Mathlib's `Integrable.fintype_prod`. Each coordinate
integrand is integrable by the published `fourierIntegrand_integrable`.
A finite linear combination remains integrable, so the published tensor
decomposition gives integrability for every row test. This argument uses the
actual product measurable structure directly and does not identify it with the
row Borel structure.

`rowFourierIntegral_sum` then proves linearity on finite sums of row tests by
`integral_finsetSum` and `integral_const_mul`, using this established
integrability for every summand.

## Fourier partners and inversion

The private assembly lemma `rowFourierCompatibility_of_scalar` takes scalar
closure, scalar sigma-finiteness, tensor decomposition, and scalar self-duality.
For a decomposition of `f`, it chooses a scalar Fourier partner `ghat j i`
for every factor. The finite sum

```text
k = ∑ j : Fin N, c j • rowTensor (ghat j)
```

is an actual row test. Linearity, tensor factorization and the pointwise scalar
partner identities prove `IsRowFourierPair ψ μ f k`.

Applying the same factorization to `k`, scalar self-duality gives
`fourierIntegral ψ μ (ghat j i) (y i) = g j i (-(y i))` for each coordinate.
The original decomposition evaluated at `-y` therefore proves
`rowFourierIntegral ψ μ d k y = f (-y)`.
The pointwise Fourier-pair equality identifies the first row transform with
`k` everywhere. Substitution and the established row-test integrability prove
convergence of the second integral; substitution also gives the required
inversion identity.

The public theorem introduces scalar self-duality, obtains sigma-finiteness
and closure from `scalarFourierClosure F ψ μ`, installs that derived
sigma-finiteness locally, and supplies `rowTensorDecomposition F d` to the
assembly lemma.

All products and sums include their empty-index cases. In dimension zero,
the empty product is one, the product measure is unit point mass, and the
coefficients retain the arbitrary value of the test at the unique row. No
positive-dimension assumption enters the construction, factorization,
integrability, or inversion arguments.

## Provenance

Worker 110 authored this internal derivation from the published
[`Basic`](Basic.md) and [`RowFourier`](RowFourier.md) definitions, the two
published prerequisite proofs, and Mathlib's finite-product integration
theorems. The Fourier convention and self-duality hypothesis are inherited
from those interfaces; this module introduces no separate literature claim.
The proof constructs no self-dual scalar measure and requires no valuation,
lattice, uniformizer, p-adic structure, continuity of multiplicative inversion,
or additional countability hypothesis.
