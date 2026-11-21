# Representations across a split integer quotient

A `SplitDegree G` is a continuous homomorphism `degree : G → ℤ` (written
multiplicatively), together with an element `lift` of degree one. Its kernel
`inertia` is a normal subgroup. Every `g` has the normal form
`g = factor g * lift ^ deg g` with `factor g` in inertia, and `mulEquiv` identifies `G`
with the semidirect product of inertia by `ℤ`, where `ℤ` acts by conjugation with
powers of the lift. For local Weil groups this is the decomposition of `W_K` into
inertia and powers of a geometric Frobenius.

`extend ρ U hU` builds a representation of `G` from a representation `ρ` of inertia
and an invertible operator `U` with `ρ(lift · n · lift⁻¹) = U ρ(n) U⁻¹` for every
inertia element `n`. It is the representation `g ↦ ρ(factor g) · U ^ deg g`
(`extend_apply`), and it restricts to `ρ` on inertia (`extend_on_inertia`). It is
obtained from `SemidirectProduct.lift`. The compatibility for all integer powers comes
from the subgroup of compatible pairs. `continuous_extend` assumes that `G` is a
topological group and `V` is finite-dimensional over `ℂ`. It shows that a continuous
`ρ` gives a continuous extension: the factor map is continuous, and `U ^ deg g`
depends only on the discrete degree.

`exists_compatibleOperator` turns an equivalence `ρ ≅ ρ ∘ conj(lift)` into such an
operator `U`. `intertwines_of_inertia_and_lift` shows that a linear map intertwining
on inertia and at the lift intertwines on all of `G`, because the elements where it
intertwines form a subgroup.

`exists_twisted_intertwiner` starts from two finite-dimensional representations `ρ`
and `σ` of `G` with a nonzero intertwiner between their inertia restrictions. It
produces `z ∈ ℂˣ` and a nonzero intertwiner from the unramified twist of `ρ` by
`z ^ deg` to `σ`. The space of inertia-invariant linear maps is finite-dimensional,
nonzero and stable under the action of the lift. Over `ℂ` this action has an
eigenvector `l` with eigenvalue `c ≠ 0`. With `z = c`, the map `l` intertwines the
twist on inertia and at the lift, hence on `G`. No irreducibility is assumed.

This is internal infrastructure for the Clifford-theoretic proof of unramified
descent (Henniart 1988, Proposition 2.2; operator route note, Proposition
`prop:unram`).
