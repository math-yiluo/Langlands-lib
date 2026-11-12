# The Speh neighbor product at the complementary endpoint

`Langlands.Classification.spehNeighborProductEndpointSubquotient` proves the
unchanged proposition `SpehNeighborProductEndpointSubquotient.{uF,uV} F T`.
The field and carrier universes are independent. For every discrete-series
datum of length `k ≥ 2` and all actual Speh representatives `S`, `Sup` and
`Sdown`, the assumed irreducibility of the actual product `Sup × Sdown`
implies its occurrence as an actual smooth subquotient of
`ν^(1/2) S × ν^(-1/2) S`. The conclusion uses the exact rank equality supplied
by the caller, as the statement requires.

Choose a segment `Δ` whose strong special head is the supplied discrete-series
block `δ`, using the proved segment classification of essentially
square-integrable representations. Square-integrability gives essential
square-integrability with real exponent zero. The
`SpehSegmentParameters` construction identifies the supplied actual
representatives as Langlands heads of the centered multisegments
`a = a(Δ,k)`, `aup = a(Δ,k+1)` and `adown = a(Δ,k-1)`. In particular, this
step retains the given representatives and does not choose substitute Speh
quotients.

Choose a strong Langlands head `P` of `aup + adown`. Its degree is the sum of
the two neighbor degrees. The proved binary Langlands-head occurrence theorem
`langlandsHeadProductSubquotient` (Tadić A.4(ii)) makes `P` a subquotient of
the supplied neighbor product. Both are irreducible, so the Library's generic
irreducible-subquotient lemma supplies an actual isomorphism from `P` to that
product. This is the binary A.6(i) consequence needed here.

The elementary multiset identity in `SpehSegmentParameters` says

```
a.twist (1/2) + a.twist (-(1/2)) = aup + adown.
```

Transport `P` to the sum of two equal ranks `k r`. The proved real-twist
compatibility for multisegment heads identifies the supplied twists of `S`
with the heads of the two parameters on the left. A second application of
`langlandsHeadProductSubquotient` therefore puts this transported `P` in the
actual binary product of these two twists. Transporting the earlier
isomorphism transfers this occurrence to the supplied neighbor product.

The helper `complementaryInduced_eq_binary` compares that binary product with
the actual `complementaryInduced` in the target. The binary shape and uniform
two-block shape have identical ordered block sizes; both families have the
positive half-twist in block zero and the negative half-twist in block one.
A dependent congruence for actual normalized product induction gives equality
through the total-rank transport. The proof starts with the caller's exact rank equality and transports both
the chosen head and the neighbor product by it. A general equality-elimination
lemma moves the inverse equal-block-rank cast from the constituent to the
ambient representation. Thus the left-hand side of the final subquotient
already has the exact required transport. The private transport helpers are
proved by equality elimination; none introduces a representation-theoretic
hypothesis.

The source is Tadić 1986, Proposition A.4(ii), printed pp.372–374, and
Corollary A.6(i), printed p.375 (registered source `tadic-1986-unitary`, PDF
pages 39–42). The centered parameter notation is defined immediately before
Theorem A.8 on p.375. The implemented proof uses A.4(ii) twice and
irreducible-subquotient rigidity for its A.6(i) step; it does not use Tadić's
deformation argument directly. The classification and head-existence inputs are proved Library results, and
the entry module supplies the separately proved binary occurrence theorem. No unitarizability assertion about Speh
representations is added to the target's hypotheses or proved by this module.
