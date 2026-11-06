# Actual finite-Galois inner twisting from a quasi-split group

`QuasiSplitInnerForm G` records an actual inner-form presentation of a field
group scheme `G`. It consists of a quasi-split group `H`, an actual adjoint
quotient `q : H → A`, quasi-splitness of `A`, and a finite Galois extension
`L/K` in the universe of `K`. It supplies a `LocalGroupIso H G` on
`Spec L → Spec K` and an actual `A`-valued natural cocycle on that cover.

The local isomorphisms are multiplicative equivalences on every relative
scheme-valued test, natural under every morphism of tests. Their discrepancy
is measured by the actual action `IsAdjointQuotient.innerAction` of `A` on
`H`. With the existing cocycle convention, the equation is
`e_a(action(ξ(a,b),h)) = e_b(h)` on every test. Thus neither the local
isomorphisms nor their discrepancy are only statements about rational
points. The adjoint quotient retains its full scheme-theoretic central
kernel, fppf properties and scheme and group universal properties.

This is an internal concrete interface for inner twisting. Its existence
for every connected reductive group is a separate unproved proposition,
`QuasiSplitInnerFormExistenceStatement`. No field dimension, norm,
perfectness or characteristic hypothesis occurs in the data.

The implemented conditional constructions are internal consequences of
these data. `isoOfTrivial` uses the published `fieldExtension_fpqc` theorem
to obtain the cover's three fpqc properties, then applies
`LocalGroupIso.descendOfTrivial` to the actual discrepancy cocycle.
`isQuasiSplit_of_isTrivial` transports the geometric Borel of `H` along
the resulting isomorphism using `IsQuasiSplit.of_iso`. These constructions
still require the presentation and a proof that its cocycle is trivial;
they assert neither of those existence or vanishing results.
