# Actual elementary kernel quotient on cohomology

This internal construction applies closed-immersion cohomology naturality to
the actual coefficient-sheaf square in `ArtinianKernelQuotientSheaf`.
The rings, schemes, modules, and finite index types have arbitrary common
universe `u`. The tests are actual augmented Artinian tests over a commutative
ring `k` with specified residue field `K`. The arrow `q : A → B` is an
elementary surjection, and `W` is any `K`-subspace of its actual kernel.
Write `AQ = A/W`, `π : A → AQ`, `r : AQ → B`, and
`h : X_AQ → X_A` for the actual intermediate closed immersion.
Both finite kernel bases may be empty.

`relativeCohomologyMap_eq` identifies the existing ideal-cohomology map
with `closedImmersionCohomologyMap` of the actual `idealMap`. Both use
the same pushforward comparison and base-ring comparison. Their vanishing
proofs agree by proof irrelevance.

`quotientProductCohomologyMap` is the closed-immersion cohomology map of
the independently constructed actual `quotientProductMap`. It maps the
cohomology of the finite product of pushed-forward residue structure
modules on `X_A` to that on `X_AQ`, restricting scalars along the specified
quotient map `π`. This definition requires neither flatness nor properness.

For flat `f`, `productToIdeal_relativeCohomologyMap` is the square

```text
Hⁿ(P_A)  --Hⁿ(productToIdeal)--> Hⁿ(I_q)
   |                                |
   | quotientProductCohomologyMap    | relativeCohomologyMap
   v                                v
Hⁿ(P_AQ) --Hⁿ(productToIdeal)--> Hⁿ(I_r),
```

where the lower row has its scalars restricted along `π`. The proof
applies the generic closed-immersion naturality lemma to the already
proved actual sheaf square.

`productCohomologyEquiv` first applies `relativeEquiv` to the unchanged
ideal-cohomology groups used in the actual Picard obstruction, then
applies cohomology to the inverse of `residueProductIdealIso`.
`productCohomologyEquiv_quotient` states that this presentation carries
the existing `cohomologySemilinearMap` to
`quotientProductCohomologyMap`. The proof evaluates the preceding square
and cancels the target product-to-ideal isomorphism.

These are consequences of the named imported constructions, without
external literature assertions. They do not yet compute the quotient map
in residue-fibre cohomology tensor coordinates, prove obstruction
naturality, construct a hull, or prove the exact atlas statement.
