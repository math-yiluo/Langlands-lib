# Successive supplied coefficient maps with the full acting order

This internal construction extends the actual formal composition comparison
to the entire acting order. It uses `AtlasBaseChangeAlongComposition`,
`AtlasOrderBaseChangeAlong`, and `AtlasOrderBaseChangeComposition`, with no
new original-literature assertion.

Let `O` be a commutative ring and `R`, `S`, `T` commutative supplied
`O`-algebras in universe `v`. Let `D` be a possibly noncommutative
`O`-algebra in an independent universe, and let `E : OrderAction D X`
on a formal `O`-atlas `X` with finite coordinates and possibly infinite
principal cover.

`baseAlongCompIso E f g`, for supplied algebra maps
`f : R →ₐ[O] S` and `g : S →ₐ[O] T`, compares

```text
(E.baseChangeAlong f).baseChangeAlong g  →  E.baseChangeAlong (g.comp f).
```

This is an actual full-order formal atlas isomorphism over
`X.baseAlongCompOpens_eq f g`. Both formal maps commute with every
element of `D`, are natural on coefficient tests, respect all overlaps,
and satisfy both formal inverse equations.

The helper `baseCompReAlgebraIso` transports the existing raw full-order
composition isomorphism at the intermediate and final bases. Equality
elimination on both scalar structures reduces it to exactly
`OrderAction.baseCompIso`. The target scalar equality uses
`BasicAtlas.coefficientAlgebra_comp_transport`. Thus no commutation
condition is discarded, and no new order action is substituted.
`baseCompReAlgebraIso_hom_val` and
`baseCompReAlgebraIso_inv_val` show that forgetting the order retains
exactly the corresponding transported basic formal maps, by the same
equality elimination.

The supplied-map construction specializes these helpers to
`coefficientTest f` and `coefficientTest g` and the two existing
`coefficientAlgebraAlong_eq` proofs. The direct raw restricted test is
definitionally the test for `g.comp f`. The supplied forward and reverse
map retention equations are `baseAlongCompIso_hom_val` and
`baseAlongCompIso_inv_val`.

`baseCompReAlgebra_onPoints` transports the existing raw full-family
composition equation. Its supplied specialization,
`baseAlongComp_onPoints`, says that extending an entire family first
along `f`, then along `g`, and applying this actual formal isomorphism
equals its direct extension along `g.comp f`. The first extension is
evaluated on the restriction of the final test along `g`. Successive
and direct restriction agree definitionally. `baseAlongComp_inv_onPoints`
gives the reverse equation for the same formal isomorphism using the
inverse law of its induced linear equivalence.

These equivalences are linear over the whole `D`, and concern complete
compatible families at all further tests, in universe `v+1`. No flatness,
injectivity or finite-cover hypothesis is added. Special tangent
conditions, height-certified quotients, varying-base moduli, framing,
levels and representability remain separate constructions.
