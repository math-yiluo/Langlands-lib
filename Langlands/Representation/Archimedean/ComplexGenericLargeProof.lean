import Langlands.Representation.Archimedean.ComplexGenericLargeReduction
import Langlands.Representation.Archimedean.RealWhittakerMaximallyFaithfulProof

/-!
# Irreducible admissible generic `(𝔤𝔩_n(ℂ), U(n))`-modules are large

`complexGenericLarge` proves `ComplexGenericLargeStatement`: the reduction
`complexGenericLargeReduction` applied to Kostant's theorem for finite products of `𝔤𝔩_n(ℂ)`
(`Kostant.glProductWhittakerMaximallyFaithful`).
-/

set_option autoImplicit false

universe uV

namespace Langlands.Archimedean

/-- Every irreducible admissible generic `(𝔤𝔩_n(ℂ), U(n))`-module is large. -/
theorem complexGenericLarge : ComplexGenericLargeStatement.{uV} :=
  ComplexGenericLarge.complexGenericLargeReduction Kostant.glProductWhittakerMaximallyFaithful

end Langlands.Archimedean
