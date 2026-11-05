# Simply connected normalizer facet stabilizers

`Langlands.Geometry.Building.SimplyConnectedFacetFixingStatement.{u}` is a
proposition, not a proof. For every nonarchimedean local field `F : Type u`,
affine `F`-group `G`, and `B : ValuationBuildingData G`, it says that if `G`
is algebraically simply connected, every `n : normalizerPoints B.i` that
preserves an apartment facet `Fa` as a set fixes each point of `Fa`.

The field instances and the actual torus, root groups, affine roots and
normalizer action are those of `ValuationBuildingData`. These data include
connected reductivity, a maximal split torus, a full equipollence class of
V 0–V 5 valuations, the actual centralizer and full omega compatibility
V 6. The Library's `IsSimplyConnected G` includes semisimplicity. The facet
predicate is the existing `AffineRootSystem.IsFacet`: a full equivalence
class for equality of the signs of every affine root.

There is no premise asserting AS 5, a Tits system, a facet-fixing property,
topology compatibility V 7 or a comparison with a canonical building.
In particular, the statement applies to the supplied full omega-compatible
class, rather than only to an already identified descended apartment.

## Source and passage to the supplied data

The principal source is T. Kaletha and G. Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), paragraph 9.3.26, printed p. 344 (PDF p. 375).
For semisimple simply connected `G`, it gives `G(k)^0 = G(k)` and hence
pointwise fixing of a facet by its setwise stabilizer in the descended
building. Restricting that conclusion to the normalizer gives the desired
conclusion after identifying the apartment action and its facets.

That identification is part of the mathematical work required by this
derived proposition, with the following source route:

1. Theorem 9.6.5, printed pp. 366–367 (PDF pp. 397–398), associates a
   full omega-compatible valuation to each point of a descended apartment.
   The association is equivariant for the actual `V(S) ⋊ N(k)` action,
   and its image is a full equipollence class.
2. Proposition 6.2.6, printed p. 216 (PDF p. 247), makes any two full
   omega-compatible valuations equipollent. Definition 6.1.7, printed
   p. 201 (PDF p. 232), then identifies their full equipollence classes.
   Thus the class supplied in `B` agrees with the class obtained in
   Theorem 9.6.5. This step uses full centralizer V 6, already present
   in `B`, and does not assume V 7.
3. The first two paragraphs of §9.6.6, printed p. 367 (PDF p. 398),
   identify these apartments and their actual affine root groups. Hence
   they identify the affine roots defined from those groups. This is the
   apartment comparison; no comparison of the quotient building defined
   from `B` is a premise here.
4. Corollary 9.4.31, printed p. 361 (PDF p. 392), identifies the descended
   apartment's facets with those determined by its affine root
   hyperplanes. This gives the facets used in the Lean proposition.
   Equivariance transports setwise preservation and pointwise fixing, so
   paragraph 9.3.26 gives the displayed conclusion.

The authors' *Corrections and additions*, version of 1 November 2024,
pp. 32 and 39–41, were checked. They do not change Proposition 6.2.6,
paragraph 9.3.26, Corollary 9.4.31, Theorem 9.6.5, or the apartment
comparison in §9.6.6. The changes to §9.3.25 distinguish full and
restricted building actions; §9.4 is independent of that proposition.
The assertion used here is pointwise fixing on the descended apartment
and its facets, as in paragraph 9.3.26.

## Provenance and remaining proof

This is a derived normalizer restriction of the source facet-stabilizer
result, transported to an arbitrary supplied full omega-compatible
valuation class by the cited comparisons. It does not prove those
comparisons or this proposition, construct building data, or establish
AS 5. A proof must construct the equivariant comparison and verify the
root and facet identifications without adding them as hypotheses.
