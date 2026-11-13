# An exterior-square comparison from cup generators

Author: Worker 327.

This internal algebraic construction is a helper for the degree-two
cohomology comparison of abelian varieties. It works over an arbitrary
commutative ring `R`, with a free module `M` and arbitrary modules `H`, `P`.
It constructs no geometric cup product and asserts no geometric generation
or Künneth compatibility.

For an alternating map `cup : M [⋀^Fin 2]→ₗ[R] H`, let `q` be its linear
extension from `⋀[R]^2 M`. If a linear map `detect : H →ₗ[R] ⨂[R]^2 M`
sends every cup monomial to its antisymmetrization, `cupLift_injective`
proves that `q` is injective. The equality `detect ∘ q = antisym` is checked
on exterior generators using the universal property. The published
`Langlands.LinearAlgebra.exteriorPowerToTensorPower_injective` then gives
injectivity without inverting 2.

`cupEquiv` assumes in addition that `q` is surjective, and constructs its
inverse as a linear equivalence `H ≃ₗ[R] ⋀[R]^2 M`. The theorem
`cupEquiv_cup` computes this inverse on every cup monomial.

`exists_comparison_of_cup_generators` takes such a generating alternating
cup map, a supplied equivalence
`κ : P ≃ₗ[R] H × (⨂[R]^2 M) × H`, and three linear maps `p₁`, `p₂`, `m`
from `H` to `P`. It assumes the required three formulas after applying
`κ`, only on elements `cup v`. The middle component of `κ ∘ m` is the
detector above. Equality of linear maps on the exterior generators and
surjectivity of `q` extend the formulas to every element of `H`, using the
constructed inverse for the middle component of `m`.

This is a derived algebraic argument using the imported injectivity lemma
and Mathlib's exterior-power universal property. It uses no external
geometric result, no Picard or dual-scheme result, no primitive-cohomology
injectivity theorem, and no finite-dimensionality assumption. Its geometric
applications must still prove cup generation and the three generator
formulas for the actual canonical cohomology pullbacks.
