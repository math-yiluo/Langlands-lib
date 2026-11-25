# Canonical tensor maps into restricted products: import module

Module `Langlands.LinearAlgebra.RestrictedProduct.Tensor`. It declares nothing. It imports the two Mathlib
stand-in modules

- `Langlands.Mathlib.Topology.Algebra.RestrictedProduct.Basic`, with `RestrictedProduct.mapAlongLinearMap`,
  `RestrictedProduct.mapAlongLinearMap_apply` and `RestrictedProduct.inclusionLinearMap`, and
- `Langlands.Mathlib.DedekindDomain.FiniteAdeleRing.TensorRestrictedProduct`, with
  `RestrictedProduct.rangeLTensor`, `rangeLTensorLeft`, `lTensor`, `lTensorLeft`, `lTensor_tmul` and
  `lTensorLeft_tmul`, the canonical maps
  `M ⊗[R] Πʳ i, [N i, L i]_[ℱ] → Πʳ i, [M ⊗[R] N i, (image of M ⊗[R] L i)]_[ℱ]`.

## Why a module that declares nothing

Until 22 November 2026 this module held these nine declarations, ported (2026) from the
Imperial College London FLT project at commit `923d45174c500aa1d994ba973bac38ea39eacbf7`
(`FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean` lines 28-91 and
`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` lines 40-88). The Imperial project declares all
nine under the same names, so they were moved, with the Imperial text of its
commit `019805815d7da565ed1e9f427b6fbd0cbc9d00d3`, to the modules above (see their pages for
origin, licence and the differences). The module stays because the statement and proof modules of this
directory import it (`TensorStatement`) and because it is a root of the Library's build; importing it
gives exactly the declarations it used to have. The Lean file keeps the source's copyright and author
lines; the upstream licence is at `licenses/ImperialCollegeLondon-FLT/LICENSE`.

## Checks

The module builds with Lean 4.35.0 and Mathlib `56a0058`.
