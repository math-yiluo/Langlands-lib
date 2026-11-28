# Auxiliary lemmas for the assembly of Landherr's theorem

Module: `Langlands.Algebra.CentralSimple.LandherrMainLemmas`.

- `ofFn_getD_eq`: a list of length `L` is recovered as `List.ofFn` of its entries
  (with a default value).
- `isUnit_of_mul_eq_one'`: in a finite-dimensional algebra over a field, an element with a
  right inverse is a unit (the algebra is Artinian).
- `isUnit_subalgebra`: if `a` lies in a commutative subalgebra `K` of a finite-dimensional
  algebra `A` and is a unit of `A`, then it is a unit of `K`: left multiplication by `a` on
  the finite-dimensional space `K` is injective, hence surjective.
- `involutionUnit τ u`: an involution `τ : FirstKindInvolution F A` maps a unit `u` to the
  unit `τ u` with inverse `τ u⁻¹` (`involutionUnit_val`).
- `involution_fix_adjoin`: if `τ x = x`, then `τ` fixes the subalgebra `F[x]` pointwise
  (induction on `Algebra.adjoin`, using that `F[x]` is commutative).
- `intAt_map`: an `F`-linear map sending a basis to elements with `v`-integral coordinates
  preserves `v`-integrality (`IntAt`, module
  `Langlands.Algebra.CentralSimple.LandherrIntegrality`).
- `upperPart F`, `lowerPart F`: the linear maps `b ↦ E₀₁ b` and `b ↦ E₁₀ b` into `M₂(B)`, with
  `upper_eq`, `lower_eq`: `upper b = 1 + E₀₁ b` and `lower b = 1 + E₁₀ b`.
- `intAt_listProd`: for a basis `β₂` of `M₂(B)` with `BasisIntAt β₂ v`, and a basis `βB` of
  `B` whose images under `upperPart` and `lowerPart` are `v`-integral, an elementary product
  `listProd l` whose entries are `v`-integral in `βB` is `v`-integral in `β₂`, and so is its
  inverse. The proof uses induction on `l` and the identities `(upper b)⁻¹ = upper (-b)`
  and `(lower b)⁻¹ = lower (-b)`.

## Provenance

Elementary algebra used in the final assembly of the proof of Landherr's theorem (module
`Langlands.Algebra.CentralSimple.LandherrMain`).
