# Canonical map from finite tensors of smooth duals

Author: Worker 173.

## Construction and scope

`Langlands.FiniteTensor.smoothDualTensorMap` is the canonical linear map

```text
(⨂[R] i, SmoothDual (ρ i)) →ₗ[R] SmoothDual (FiniteTensor.external ρ).
```

Here `R : Type uR` is any commutative ring, `ι : Type uI` is finite,
`G i : Type uG` is a dependent family of topological groups, and
`V i : Type uV` is a dependent family of additive commutative groups with
`R`-module structures. Each `ρ i` is an actual linear representation of
`G i` on `V i`. In particular, setting `R := ℂ` gives the requested complex
linear map. All four universes are independent. The product group has its
actual product topology. No topology is put on any carrier or dual module.
No resizing, countability, nontriviality, finite dimensionality, smoothness
of `ρ i`, admissibility, local compactness, or separation hypothesis is used.

The tensor products are Mathlib's actual `PiTensorProduct`. The target is the
smooth-vector submodule of the full algebraic dual of the actual external
tensor representation. The finite index type may be empty, and carriers
may be zero. The map needs only `[Finite ι]`; the two displayed finite-product
laws use `[Fintype ι]` to write the product notation. A `Fintype` can always be
chosen for a finite type.

## Implemented maps and laws

`dualTensorIntertwiner` first gives the algebraic intertwiner

```text
FiniteTensor.external (fun i => (ρ i).dual)
  → (FiniteTensor.external ρ).dual.
```

Its underlying linear map is precisely `PiTensorProduct.dualDistrib`.
This map sends a pure family of algebraic functionals to the functional
whose value on a pure family of vectors is the product of their values.
Equivariance is proved by tensor extensionality in both the functional
and vector arguments. The external tensor action acts coordinatewise,
and each dual action evaluates at the inverse group element, so the two
products agree term by term. This algebraic construction needs no topology.

`smoothDualTensorIntertwiner` composes this map with the external tensor
of the canonical smooth-part inclusions `smoothInclusion (ρ i).dual`.
The source representation, the external tensor of the smooth
contragredients, is smooth by `isSmooth_smoothContragredient` and
`isSmooth_external`. The latter uses continuous coordinate evaluations
for the actual product topology and finite intersections of open
stabilizers. Applying `smoothLift` therefore restricts the target to its
smooth vectors: an equivariant map carries a vector fixed by an open
subgroup to a vector fixed by that same open subgroup.
`smoothDualTensorMap` is the underlying linear map of this intertwiner.

The accompanying intrinsic laws are:

- `smoothDualTensorMap_val` identifies the underlying algebraic functional
  with `dualDistrib` after tensoring the subtype inclusions
  `smoothDualPairing (ρ i)`.
- `isSmoothVector_smoothDualTensorMap` states that the underlying functional
  of every image tensor is smooth for the dual external action. This
  follows from its proved membership in the smooth-vector submodule.
- `smoothDualTensorMap_tprod_apply` gives the exact evaluation formula
  `⟨map (⊗ᵢ ℓᵢ), ⊗ᵢ vᵢ⟩ = ∏ᵢ ⟨ℓᵢ, vᵢ⟩`. It follows from the underlying
  map formula, `PiTensorProduct.map_tprod`, and `dualDistrib_apply`.
- `smoothDualTensorMap_action` states equivariance under every element
  of the actual product group, for arbitrary tensors of smooth functionals.
- `matrixCoefficient_smoothDualTensorMap_tprod` gives the pointwise identity
  `c(map (⊗ᵢ ℓᵢ), ⊗ᵢ vᵢ)(g) = ∏ᵢ c(ℓᵢ, vᵢ)(gᵢ)`, using the Library's
  `matrixCoefficient` and the subtype pairings. The proof combines
  `external_tprod` with the pure evaluation formula. The coefficient
  convention is `ℓ(ρ(g)v)`, with no inverse in the coefficient itself.

For the empty family the finite products in both formulas equal `1`;
no separate nonempty-index assumption is concealed in the construction.

## Provenance and boundaries

This is internal infrastructure derived from the tensor universal property
and the existing smooth-part construction. It is not attributed verbatim
to an external literature theorem. Pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`,
`Mathlib/LinearAlgebra/PiTensorProduct/Dual.lean`, supplies `dualDistrib`
and `dualDistrib_apply`. The project dependencies are imported by their
current Lean names: `Tensor.Finite`, `Smooth.Contragredient.LawsProof`,
and `MatrixCoefficient.Definitions`.

The full `Classification.BlockTensorAnalyticStatement` pair describes
smooth-functional decomposition as a remaining analytic prerequisite.
The present construction supplies products of smooth functionals and
their coefficient law. It asserts no injectivity or surjectivity, no
factorization of the full algebraic dual, and no integrability, central
quotient, or block classification result. In particular it does not use
Mathlib's `dualDistribEquiv`, which requires finite free factor modules.

Surjectivity for admissible factors with a cofinal supply of compact open
subgroups is a separate statement and proof obligation. The existing
`Smooth.Contragredient.CompactDualityProof`,
`Smooth.Contragredient.AdmissibleDualityProof`, and
`Tensor.FiniteProperties` supply relevant fixed-vector and duality tools
for that later argument; none is needed as an extra hypothesis here.
No existing statement or imported pair is changed.

The paired module passed a development Lake build and declaration inspection
in the pinned Lean 4.34.0 environment with zero errors and warnings.
The selected declaration is a definition with universe parameters
`uR`, `uI`, `uG`, `uV`, and only the standard assumptions `propext`,
`Classical.choice`, and `Quot.sound`. This development check is distinct
from independent semantic review and publication.
