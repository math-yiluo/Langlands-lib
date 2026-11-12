# Scalar extension of an algebra to a completion, decomposed over the places above

Author: Worker 19.

This internal algebraic construction decomposes the scalar extension of a
possibly noncommutative algebra to the completion of a number field at a
finite place into the product over the places of a larger number field above
it. It is the step from Harris's undecomposed split-prime identification to
the product over places in Harris (1999), (4.2), and Harris (1998), (A.1);
the Harris specialization is `HarrisSplitPrimeFactors`, submitted together
with this module.

## Inputs

The published `Langlands.Global.AdelicFunctoriality` modules (owned by the
global arithmetic branch and reused unchanged) provide, for number fields
`K` and `L` with `Algebra K L` and a finite place `p` of `K`:

- `FinitePlacesAbove L p`, the finite places `q` of `L` whose prime ideal lies
  over that of `p`, with `Finite` and `Fintype` instances (`Norm`);
- `FiniteExtension.completionMap p q : K_p →+* L_q`, the continuous extension
  of `K → L`, and the scoped `K_p`-algebra structure on `L_q` given by it
  (`Extension`); `FiniteExtension.local_finite`: `L_q` is finite over `K_p`;
- `finiteTensorMap p : K_p ⊗[K] L →ₐ[K_p] Π_{q ∣ p} L_q`, with
  `x ⊗ y ↦ (completionMap p q x * y)_q` (`finiteTensorMap_tmul`,
  `finiteTensorMap_one_tmul`), and the published theorem
  `completedTensorComparison`, whose first part states that `finiteTensorMap p`
  is bijective at every finite place (`CompletedTensorComparisonProof`).

Here `K_p = p.adicCompletion K` is Mathlib's adic completion.

## The decomposition

All declarations are in namespace `Langlands.Shimura.PlaceTensor`. Let
`F` and `K` be number fields with `Algebra F K`, and `𝔭` a finite place of
`F`; write `F_𝔭` and `K_w` for the completions.

- `fieldTensorEquiv 𝔭 : K ⊗[F] F_𝔭 ≃ₐ[K] Π_{w ∣ 𝔭} K_w` is the exchange of
  factors followed by the bijection `finiteTensorMap 𝔭`, as an isomorphism
  of `K`-algebras (it sends `k ⊗ 1` to the constant family of `k`).
  `fieldTensorEquiv_tmul`: `k ⊗ x ↦ (completionMap 𝔭 w x * k)_w`.

Let `A` be a ring with `Algebra F A`, `Algebra K A` and `IsScalarTower F K A`
(no commutativity is assumed).

- `towerEquiv 𝔭 A : A ⊗[F] F_𝔭 ≃ₐ[K] A ⊗[K] (K ⊗[F] F_𝔭)` is the inverse of
  Mathlib's `TensorProduct.AlgebraTensorModule.cancelBaseChange`, shown to be
  multiplicative on pure tensors; `towerEquiv_tmul`: `a ⊗ x ↦ a ⊗ (1 ⊗ x)`.
  (Mathlib's `Algebra.TensorProduct.cancelBaseChange` requires commutative
  factors, so the algebra equivalence is built from the linear one, as in the
  published `InvolutionBaseChangeTower.baseChangeTowerEquiv`.)
- `placeTensorEquiv 𝔭 A : F_𝔭 ⊗[F] A ≃+* Π_{w ∣ 𝔭} K_w ⊗[K] A` is the ring
  isomorphism obtained by composing: the exchange `F_𝔭 ⊗[F] A ≃ A ⊗[F] F_𝔭`,
  `towerEquiv`, `A ⊗[K] fieldTensorEquiv`, Mathlib's
  `Algebra.TensorProduct.piRight` (`A ⊗[K] Π_w K_w ≃ Π_w A ⊗[K] K_w`), and the
  exchange in each factor. `placeTensorEquiv_tmul`: it sends `x ⊗ a` to
  `(completionMap 𝔭 w x ⊗ a)_w`.
- `placeUnitsEquiv 𝔭 A : (F_𝔭 ⊗[F] A)ˣ ≃* Π_{w ∣ 𝔭} (K_w ⊗[K] A)ˣ` is the
  induced isomorphism of unit groups followed by Mathlib's
  `MulEquiv.piUnits`; `placeUnitsEquiv_apply` gives its components, by `rfl`.

## Totally split places

Let `F` be a number field and `v` a finite place of `ℚ`.

- `finrank_completion_eq_one v hcard 𝔭`: if `[F : ℚ]` is at most the number
  of places of `F` above `v` (`hcard`), then every completion `F_𝔭` above `v`
  has dimension one over `ℚ_v`.
- `completionMap_bijective_of_le_card v hcard 𝔭`: under the same hypothesis
  the completion map `ℚ_v → F_𝔭` is bijective (Mathlib's
  `Module.Free.bijective_algebraMap_of_finrank_eq_one`).

Proof: `finiteTensorMap v` is a bijective `ℚ_v`-linear map from
`ℚ_v ⊗[ℚ] F`, of dimension `[F : ℚ]` (`Module.finrank_baseChange`), to
`Π_{𝔮 ∣ v} F_𝔮`, of dimension `Σ_𝔮 [F_𝔮 : ℚ_v]` (`Module.finrank_pi_fintype`).
Every summand is at least one (`Module.finrank_pos`), so
`[F_𝔭 : ℚ_v] + (#places − 1) ≤ [F : ℚ] ≤ #places`, whence `[F_𝔭 : ℚ_v] = 1`.

## Scope

The isomorphisms are algebraic: no topology is compared. The decomposition is
stated for one place `𝔭` of `F` and the places of `K` above it; it does not
decompose `ℚ_p ⊗[ℚ] A` over all places above `p`. The degree-one criterion
uses only the count of places and does not compute ramification indices or
residue degrees.

## Provenance

Internal construction from the published completed tensor comparison and
Mathlib tensor-product equivalences. Its purpose is the product
`∏_j (𝒟_j)ˣ = ∏_j (𝒟 ⊗ 𝒦_{v^(j)})ˣ` of Harris (1999), equation (4.2) on
printed p. 309, and `∏_j B(F_j)ˣ` of Harris (1998), Appendix, equation (A.1)
on printed p. 206; see `HarrisSplitPrimeFactors.md` for the source passages.

Formal dependencies: `Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof`
(with `Norm` and `Extension`) and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in particular
`TensorProduct.AlgebraTensorModule.cancelBaseChange`,
`LinearMap.map_mul_of_map_mul_tmul`, `Algebra.TensorProduct.congr`,
`Algebra.TensorProduct.piRight`, `Algebra.TensorProduct.comm`,
`AlgEquiv.piCongrRight`, `MulEquiv.piUnits`, `Module.finrank_baseChange`,
`Module.finrank_pi_fintype`, `Module.finrank_pos` and
`Module.Free.bijective_algebraMap_of_finrank_eq_one`.
