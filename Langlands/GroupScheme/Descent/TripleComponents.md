# Triple components from double components

For a morphism `p : S → B` of schemes in arbitrary universe `u`, let
`q i : Z i → Overlap p` be a finite coproduct decomposition indexed by
`I : Type`. The actual triple overlap is the pullback of the second and
first projections of `Overlap p`.

`componentPullbackMap` maps the pullback of `q i ≫ snd p` and
`q j ≫ fst p` to the actual triple overlap. Its coproduct is an
isomorphism. The proof uses finite extensivity of schemes to distribute
this pullback over the finite coproducts and then the isomorphism of the
coproduct of the given `q i` on both sides of the pullback.

If each `q j ≫ fst p` is an isomorphism, the pullback's first projection
is an isomorphism. `tripleComponent p q (i,j)` precomposes
`componentPullbackMap` with its inverse, giving a component with domain
`Z i`. These maps form a finite coproduct decomposition, by the preceding
result and the coproduct of the projection isomorphisms. Their first
endpoint is `q i ≫ fst p`; their third endpoint is the composite of
`q i ≫ snd p`, the inverse of `q j ≫ fst p`, and `q j ≫ snd p`.
Thus the first endpoint is an isomorphism, and the third is also an
isomorphism if all the double-component second endpoints are.

This is an internal deduction from the actual pullback and finite
coproduct constructions and Mathlib's finite extensivity theorem for
schemes. It needs no tensor-product decomposition of a triple tensor
product. The double-overlap decomposition and its specified projection
isomorphisms remain inputs.
