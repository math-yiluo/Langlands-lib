# Exterior-square comparison from bounded creation and contraction

Author: Worker 327.

This derived internal construction combines the generation theorem in
`Langlands.LinearAlgebra.BoundedCreationContraction` with the comparison
construction in `Langlands.LinearAlgebra.ExteriorSquareCoproduct`.
It is conditional linear algebra and supplies no geometric operators.

Let `M n` be modules over a commutative ring `R`. A finite type `ι` indexes
linear creation maps `c i n : M n → M (n+1)` and contraction maps
`d i n : M (n+1) → M n`. Assume the relations
`d_i c_j + c_j d_i = δ_ij id` in every positive degree, and that `M n`
vanishes for `n > card ι`. Let `cup` be an alternating two-variable map
from `M 1` to `M 2`. Assume vectors `v i : M 1` satisfy
`c i 1 x = cup ![v i, x]` for every `i` and `x`.
No basis hypothesis on these vectors is required.

`cupLift_surjective` proves that the linear extension of `cup` from
`⋀[R]^2 (M 1)` is surjective. The imported generation theorem says that
the ranges of `c i 1` span `M 2`. Each such range lies in the range of
the exterior cup lift, by the displayed compatibility and the defining
formula for the lift on an exterior monomial. Consequently the latter
range is the whole module. This conclusion needs no freeness hypothesis.

For the remaining constructions assume `M 1` is free over `R`.
`cupEquiv` additionally takes a linear detector from `M 2` to the tensor
square of `M 1` that sends each cup monomial to the antisymmetrization of
the corresponding exterior monomial. It passes the proved surjectivity
to the imported exterior-square construction, obtaining an equivalence
`M 2 ≃ₗ[R] ⋀[R]^2 (M 1)`. `cupEquiv_cup` computes this equivalence on
cup monomials. The compatible detector gives injectivity, so no division
or characteristic assumption is required.

`exists_comparison` takes a supplied linear equivalence
`κ : P ≃ₗ[R] M 2 × (⨂[R]^2 (M 1)) × M 2` and three linear maps
`p₁`, `p₂`, `m` from `M 2` to `P`. On every cup monomial, their coordinates
are assumed respectively to be `(cup w, 0, 0)`, `(0, 0, cup w)` and
`(cup w, antisym (wedge w), cup w)`. The theorem applies the imported
comparison theorem using the proved surjectivity. It gives one exterior
equivalence `e` for which the same three formulas hold on every element,
with middle coordinate `antisym (e x)` in the third formula.

The provenance is the internal derivation above from the two imported
linear algebra constructions and the exterior-power universal property.
No external geometric theorem is invoked. A cohomological application
still needs actual cup and contraction maps, their relations in all
positive degrees, the required vanishing bound, a suitable number of
directions, a Künneth equivalence and the formulas for the canonical
pullbacks on cup monomials. This module proves none of those inputs.
