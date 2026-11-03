# Actual cocycle morphisms and their all-test conjugation orbit

This is a derived cocycle-coordinate construction for the section-functor
argument in Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition
(2015), proof of Proposition A.8.12, printed pp.553–554 (PDF pp.579–580).
The registered source is `conrad-gabber-prasad-2015-pseudo-reductive`,
SHA-256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The book uses sections of a semidirect projection; the declarations here
construct their cocycle equations directly from the published
`AutomorphicAction` morphism.

Over an arbitrary base scheme `S`, for an automorphic action `a` of `H` on `G`,
`a.Cocycle T` consists of an actual morphism `T ×_S H → G`, normalized at
the identity of `H`, whose values satisfy
`c(hh') = c(h) a(h,c(h'))` on every test scheme mapping to `T`.
The normalization and multiplication equations are part of this structure.
There is no restriction to rational or reduced points and no smoothness
assumption on `H`.

`Cocycle.eval` evaluates this actual morphism. Evaluation is natural, and
`eval_ext` proves that equality of all evaluations implies equality of
morphisms by testing the two universal projections of `T ×_S H`.
`Cocycle.restrict` precomposes the parameter factor with a map `T' → T`;
its identity and composition laws define `a.cocycleFunctor`.

`Cocycle.trivial` is the constant identity cocycle. `Cocycle.conjugate g c`
is the actual morphism with values
`g c(h) a(h,g⁻¹)`, with `g` pulled back to each test. The proof that this
is a cocycle uses the two action multiplication laws and cancellation in
the group of test points. The same identities prove the identity and
composition laws for conjugation and its compatibility with restriction.

`a.coboundary g` is the conjugate of the trivial cocycle, with values
`g a(h,g⁻¹)`. Naturality gives the natural transformation
`a.cocycleOrbit` from the point functor of `G` to the cocycle functor.
`coboundary_eq_iff` proves its exact right-coset fiber equation:
two points `g,g'` have equal cocycles if and only if `g⁻¹g'` lies in the
published all-test fixed subgroup functor of `a`.
In both directions the proof evaluates on every refinement, expands the
action of a product and inverse, and rearranges the group equality.

The construction does not assert representability, finite-type approximation,
smoothness of cocycle orbits, affineness of a quotient, or reductivity of a
fixed subgroup. Those geometric assertions remain separate proof obligations.
