# The actual left action on a scheme coset quotient

This internal construction works over an arbitrary base scheme `S`. It starts
with a group scheme `G`, a subgroup functor `H`, and an actual morphism
`q : G.X ⟶ Q` which is quasi-compact, flat, and surjective and has the exact
right-coset fibers on every test scheme:

`g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ H.carrier T`.

`flagQuotientActionHom` constructs a morphism `G.X ⊗ Q ⟶ Q` over `S`.
The product is the actual relative scheme product. The construction descends
the morphism `μ[G.X] ≫ q` along `G.X ◁ q`. Left multiplication preserves
the displayed fiber relation by group cancellation. The product of `q`
with the identity remains fpqc, so it is an effective epimorphism of schemes.
`EffectiveEpi.desc` then constructs the underlying scheme map, and
epimorphism cancellation proves its equation over `S`.

`flagQuotientAct` evaluates that map on any test scheme. The theorem
`flagQuotientAct_lift` identifies its value at `(g, h ≫ q)` with
`(g * h) ≫ q`; `flagQuotientAct_naturality` proves compatibility with
pullback of test points. The identity and multiplication laws follow by
pulling back `q` along the given quotient point, checking the equation after
that fpqc cover, and cancelling the resulting epimorphism. They yield
`flagQuotientAct_inv_cancel`, including for a quotient point which has no
lift over its original test scheme.

The provenance is internal. The proof uses the Library's existing exact
coset-fiber convention, Mathlib's cartesian monoidal products and fpqc
effective epimorphisms, and the same descent method as the published
`Langlands.GroupScheme.ActionDescent`. That earlier module descends
automorphic actions through a group homomorphism; the present construction
instead descends multiplication to a possibly nongroup quotient scheme,
without a normality hypothesis. All quotient existence and geometric
properties assumed above remain explicit premises. No rational-point
density or lifting assertion is proved here.
