# Quasi-étale restriction over an open analytic domain

Author: Worker 912.

`Langlands.Analytic.SaturatedAtlasPresentation.quasiEtaleOpenRestriction`
proves `QuasiEtaleOpenRestrictionStatement.{u,v}` at independent universes
`u` and `v`. Given a quasi-étale map `f : Y ⟶ Z` with Hausdorff underlying
source and an open subset `V` of `Z`, it proves that the actual restriction
`f⁻¹(V) ⟶ V` is quasi-étale. The arrow `preimageOpenDomainMap f V hV`
in the proof is definitionally the `domainRestrict` of the statement.

## Proof

* `isPullback_preimageOpenDomain` exhibits the restriction as a pullback
  along the canonical inclusion of `V`. The private lemma
  `factorization_of_openDomain_pullback` treats a map factoring as an
  analytic-domain embedding into `W` followed by an étale arrow
  `w : W ⟶ Z`. Pull `w` back to the open domain `W' = w⁻¹(V)`.
  The restriction `W' ⟶ V`, followed by the inclusion into `Z`, is the
  composite of the open inclusion `W' ⟶ W` and `w`, hence is étale by
  `etaleOpenDomainStatement` and `etale_comp`. Cancelling the target
  inclusion with `etale_of_comp_domainι` proves that `W' ⟶ V` is étale.
  The domain embedding into `W` is given by an isomorphism followed by
  an inclusion of a domain `D`. After transporting the pullback along the
  isomorphism, `isPullback_domainPreimage_comp` identifies the new source
  with the inverse image of `D` in `W'` by uniqueness of pullbacks.
  Its inclusion into `W'` gives a domain–étale factorization of the new map.
* At each point of `f⁻¹(V)`, take the finite family of analytic domains
  through its image in `Y` given by
  `hasLocalDomainEtaleFactorizations_of_quasiEtale`. This is where the
  Hausdorff hypothesis is used. Pull these domains back along
  `f⁻¹(V) ⟶ Y`: their union is a neighbourhood by continuity, and
  `isPullback_domainPreimage_comp` gives the pullback square for each
  restricted piece. The private lemma gives the required factorization on
  every piece. Finally, `HasLocalDomainEtaleFactorizations.quasiEtale`
  recovers the Library's quasi-étale predicate from these families.

## Source and scope

This is the open-immersion case of the base-change clause of Berkovich,
*Vanishing cycles for formal schemes*, Invent. Math. **115** (1994),
539–571, §3, Lemma 3.1(i), printed p. 544 (PDF p. 6 of the registered source
`berkovich-1994-vanishing-cycles-formal-schemes`, SHA-256
`f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`).
On printed p. 543, quasi-étaleness requires a finite family of affinoid
source domains whose union is a neighbourhood, each identified with an
affinoid domain in a space étale over the base. The proof uses the Library's
local analytic-domain factorization criterion instead of directly refining
the affinoid charts.
It retains the statement's Hausdorff-source hypothesis and does not assume
or prove general étale or quasi-étale base change.
