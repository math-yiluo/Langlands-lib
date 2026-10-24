# Binary tensor coordinates for the Shahidi pair carrier

Worker 321 authored this internal algebraic construction unit. All declarations
are in `Langlands.Shahidi`. It completes the interface of the published
`pairSplit`, `pairFlip` and `pairFunctional`, without introducing another
carrier, flip or functional.

## Setting and provenance

Let `V₁` and `V₂` be arbitrary complex modules with additive commutative group
structures, in the same universe as required by `pairCarrier`. The domain is
exactly `PiTensorProduct ℂ (pairCarrier V₁ V₂)` from
`Langlands.Representation.Shahidi.Induction`, with `pairCarrier V₁ V₂ 0 = V₁`
and `pairCarrier V₁ V₂ 1 = V₂`. No topology, norm, finite-dimensionality,
irreducibility, smoothness, admissibility or unitarity hypothesis is used.
Zero modules are allowed. The block-action lemmas additionally take positive
ranks and a commutative ring `F` in an independent universe.

The construction is derived from the published tensor universal-property
constructions, not asserted as a theorem of Shahidi. Specifically,
`IntertwiningInduced.pairSplit` (in the namespace `Langlands.Shahidi`) is
`FiniteTensor.headTailLinearEquiv` followed by Mathlib's singleton tensor
equivalence on the tail. Its `pairSwap` transports `TensorProduct.comm`,
and its `pairFlip` specializes the factor identifications to identity maps.
`LocalCoefficientPadic.pairFunctional` is the published multilinear
universal-property construction of the product of two linear functionals.
The two Shahidi modules and their existing constructions were authored by
Worker 11; this unit imports them by module name.

For downstream context only, F. Shahidi, *Fourier transforms of intertwining
operators and Plancherel measures for GL(n)*, American Journal of Mathematics
106 (1984), 67–111, printed page 72, uses `π₁ ⊗ π₂` in the induced space and
the functional `λ₁ ⊗ λ₂` in (0.2); the top of printed page 73 identifies the
latter as the map induced on the tensor product by the two functionals.
Registered source: `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
Those source passages motivate the interface; they are not the proof of this
algebraic equivalence. This unit proves no assertion about Jacquet integral
stabilization, integration, Haar normalization or local-coefficient comparison.

## The binary tensor bridge

`pairTensorEquiv V₁ V₂` is the explicit specialization

```lean
PiTensorProduct ℂ (pairCarrier V₁ V₂) ≃ₗ[ℂ] V₁ ⊗[ℂ] V₂
```

of `pairSplit (pairCarrier V₁ V₂)`. It is an abbreviation of that actual
constructed equivalence. The usual `LinearEquiv.apply_symm_apply` and
`LinearEquiv.symm_apply_apply` give both inverse identities.

- `pairTensorEquiv_pairTensor` sends `pairTensor v₁ v₂` to `v₁ ⊗ₜ[ℂ] v₂`.
  This is the published `pairSplit_tprod` specialized to `pairVector`.
- `pairTensorEquiv_symm_tmul` sends `v₁ ⊗ₜ[ℂ] v₂` back to
  `pairTensor v₁ v₂`. The proof applies injectivity of the equivalence and
  then its forward formula and inverse identity.
- `pairTensorEquiv_pairRepresentation` states that the actual block action
  `pairRepresentation hm hn π₁ π₂ g` becomes
  `TensorProduct.map (π₁ (g 0)) (π₂ (g 1))` under the bridge. Here
  `pairRepresentation` is the published abbreviation for
  `(twoBlocks m n hm hn).blockTensor (pairFamily π₁ π₂)`.
  The proof writes the argument as an inverse image under the bridge and
  uses binary tensor induction; the generator case uses the published
  `blockTensor_pairTensor`, and the sum case uses linearity.

## The existing flip and its inverse

`pairFlip_eq_transport` identifies the published `pairFlip` with the composite
of `pairTensorEquiv V₁ V₂`, `TensorProduct.comm ℂ V₁ V₂`, and
`(pairTensorEquiv V₂ V₁).symm`. The proof unfolds the already constructed
flip and removes the tensor product of the two identity equivalences.

- `pairTensorEquiv_pairFlip` gives the corresponding commuting-square
  formula on arbitrary tensors.
- The imported `pairFlip_pairTensor` gives
  `pairFlip (pairTensor v₁ v₂) = pairTensor v₂ v₁`.
- `pairFlip_pairFlip` proves that exchanging the factors twice is the
  identity. The proof applies bridge injectivity, the commuting-square
  formula twice, and `TensorProduct.comm_comm`.
- `pairFlip_symm` identifies the inverse flip with the forward flip on the
  reversed pair, using injectivity and the preceding involution identity.
- `pairFlip_symm_pairTensor` is the inverse pure-tensor formula, obtained
  from that equality and the imported forward formula.
- The imported `pairFlip_pairRepresentation` says that the flip intertwines
  the original block action at `twoBlockLeviSwap hm hn F g` with the swapped
  action at `g`. `pairFlip_symm_pairRepresentation` gives its inverse
  orientation. Applying the forward flip reduces this inverse orientation
  to the imported compatibility and the inverse equations.

## Agreement of the scalar functionals

For arbitrary linear functionals `ℓ₁ : V₁ →ₗ[ℂ] ℂ` and
`ℓ₂ : V₂ →ₗ[ℂ] ℂ`, the ordinary tensor functional is

```lean
TensorProduct.dualDistrib ℂ V₁ V₂ (ℓ₁ ⊗ₜ[ℂ] ℓ₂)
```

Mathlib constructs it by mapping the factors into `ℂ ⊗[ℂ] ℂ` and using the
canonical scalar tensor equivalence. Its value on `v₁ ⊗ₜ[ℂ] v₂` is
`ℓ₁ v₁ * ℓ₂ v₂`. This uses the canonical linear map `dualDistrib`; no
identification of the full dual with a tensor of duals is needed or claimed.

`pairFunctional_eq_tensor_comp` proves the equality of linear maps

```lean
pairFunctional ℓ₁ ℓ₂ =
  (TensorProduct.dualDistrib ℂ V₁ V₂ (ℓ₁ ⊗ₜ[ℂ] ℓ₂)).comp
    (pairTensorEquiv V₁ V₂).toLinearMap
```

Thus the already published functional is exactly the requested composition;
there is no second definition of the pair functional. The proof uses indexed
tensor extensionality, `pairFunctional_tprod`, `pairSplit_tprod` and
`TensorProduct.dualDistrib_apply`.

`pairFunctional_pairTensorEquiv_symm` evaluates this functional in binary
coordinates; it follows by composing the map equality with the inverse
bridge. The imported `pairFunctional_pairTensor` gives its pure-tensor
product formula. The imported `pairFunctional_pairFlip` proves
`pairFunctional ℓ₂ ℓ₁ (pairFlip x) = pairFunctional ℓ₁ ℓ₂ x`.
Finally, `pairFunctional_pairFlip_symm` supplies the inverse orientation by
rewriting the inverse flip as the reversed forward flip. Together with the
map equality, these formulas also prove flip compatibility for the ordinary
tensor-functional description.
