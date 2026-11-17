# Supplied affine products of simple Cartan-component factors

Worker 634.

`RootComponentProduct M` packages the local product data needed to turn a
pinned affine model into a split finite étale Weil restriction. Its index is
the actual finite Cartan-component quotient of the model's constant full root
datum. It supplies reductive factors with almost-simple geometric fibres and
an actual isomorphism from the original group to their finite categorical
product. This is supplied data; no existence theorem is asserted here.

Each factor is affine and locally of finite type over the original affine
base, as required by the existing affine Weil restriction. The supplied
isomorphism gives the actual geometric-fibre product isomorphism through
preservation of finite products by base change. If any geometric fibre is
nontrivial, the component index must be nonempty: otherwise the product point
functor on that fibre is a product over an empty type and every point is the
identity.

This is an internal interface for the local-product and finite-family Weil
assembly steps motivated by Conrad, *Reductive group schemes* (2014),
Proposition 6.4.4, pp.232–233. Algebraic simple connectedness and adjointness
of factors are separate transfer properties; they are not asserted by this
structure or inferred without a corresponding proof.
