# Iwahori units and the decomposition `G = 𝔄ˣ · W · B(F)`

Lean module: `Langlands.Representation.AffineGeneric.Decomposition`, namespace
`Langlands.AffineGeneric`.

Let `F` be a nonarchimedean local field with valuation ring `𝒪` and residue field `k`.

- `resOf_entry`: for `κ ∈ GL_{m+1}(𝒪)` (`Conductor.integralSubgroup`), the entries of its
  reduction (`IntegralReduction.reduction`) are the residues `resOf` of the entries of `κ`.
- `isIwahoriOrder_of_reduction`: an element of `GL_{m+1}(𝒪)` whose reduction modulo `𝔭` is upper
  triangular lies in the Iwahori order `𝔄` (its entries below the diagonal have residue `0`).
- `inv_upperTriangular`: the inverse of an upper triangular invertible matrix is upper
  triangular.
- `permutation_mem_integralSubgroup`, `reduction_permutation`: permutation matrices are integral
  and reduce to the permutation matrices over `k`.
- `exists_iwahori_decomposition`: every `x ∈ GL_{m+1}(F)` can be written `x = ι w β b⁻¹` where
  `ι` and `ι⁻¹` lie in `𝔄`, `w` is a permutation matrix (`permutation`), and `β`, `b` are upper
  triangular.

**Proof of the decomposition.** The Iwasawa decomposition
(`Iwasawa.exists_upperTriangular_mul`) writes `x⁻¹ = b k` with `b` upper triangular and
`k ∈ GL_{m+1}(𝒪)`; put `κ = k⁻¹`. The Bruhat factorization over the residue field
(`fieldUpperBruhatFactorizationTheorem`) writes the reduction of `κ` as `a w a'` with `a`, `a'`
upper triangular over `k` and `w` a permutation. Let `β` be the integral lift of `a'`
(`IntegralReduction.lift`), which is upper triangular, and `ι = κ β⁻¹ w⁻¹`. The reduction of
`ι` is `a` and that of `ι⁻¹` is `a⁻¹`, both upper triangular (`inv_upperTriangular`), so `ι`
and `ι⁻¹` lie in `𝔄` by `isIwahoriOrder_of_reduction`. Finally `κ = ι w β`, so
`x = κ b⁻¹ = ι w β b⁻¹`.
