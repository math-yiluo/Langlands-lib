import Langlands.Representation.Archimedean.ComplexPermutationReduction
import Langlands.Representation.Archimedean.ComplexSwapJacquetProof
import Langlands.Representation.Archimedean.ComplexSwapJacquetNonvanishing
import Langlands.Representation.Archimedean.ComplexJacquetFrobeniusProof

/-!
# Permutation invariance of irreducible complex principal series

`complexStandardPermutation` proves `ComplexStandardPermutationStatement`: if the `U(n)`-finite
principal series `X(ds)` of `GL_n(ℂ)` is an irreducible `(𝔤𝔩_n(ℂ), U(n))`-module and `es` is a
permutation of `ds`, there is a bijective intertwining map `X(es) → X(ds)`.

The proof combines three inputs:

* `ComplexPermutation.complexStandardPermutation_of_swapJacquet`
  (`ComplexPermutationReduction`): the statement follows from Frobenius reciprocity and
  `SwapJacquetStatement`, the existence of a nonzero rank-one Jacquet functional for an adjacent
  swap;
* `complexJacquetFrobenius` (Library, `ComplexJacquetFrobeniusProof`): Frobenius reciprocity
  for Jacquet functionals;
* `ComplexSwapJacquet.swapJacquet_of_nonvanishing` (`ComplexSwapJacquetProof`) together with
  `ComplexSwapJacquet.exists_integral_integrand_ne_zero` (`ComplexSwapJacquetNonvanishing`):
  the rank-one integral `f ↦ ∫_ℂ (R(c E_jj) f - κ_j(c) f)(s x(z)) dz` is a Jacquet functional
  with the swapped exponents and is nonzero.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

/-- **Permutation invariance** of irreducible `(𝔤𝔩_n(ℂ), U(n))` principal series. -/
theorem complexStandardPermutation : ComplexStandardPermutationStatement :=
  ComplexPermutation.complexStandardPermutation_of_swapJacquet
    (ComplexSwapJacquet.swapJacquet_of_nonvanishing
      ComplexSwapJacquet.exists_integral_integrand_ne_zero)
    complexJacquetFrobenius.{0}

end Langlands.Archimedean
