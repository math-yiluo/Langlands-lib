# Double averaging index and association multiplicity

`WeylParabolicPair` indexes the double sum in Waldspurger VI.3 by a relative Weyl element `s` and a parabolic in the actual fiber over `s.M`. `weylParabolicPairEquivProd` uses `weylParabolicFiberEquiv` to identify each fiber with the one over `M`. The resulting number of pairs is `|W^G| |P(M)|`. Finiteness follows from reductive relative Weyl finiteness and `SemistandardSpectralFiberFinitenessStatement`. The literal conjugate Levi uses `SemistandardSpectralDynamicCoverageStatement` and the all-test centralizer containment for `M`.

For a full index `t = (O,P)`, `weylParabolicTarget` selects the unique transported orbit over the parabolic in each pair, using `existsUnique_weylTransports_of_levi_eq`. The equivalence `weylParabolicPairEquivTransporters` regroups the pairs by their actual targets. A fiber over `q` consists of the Weyl elements sending `t` to `q`. Fixing one such element `r` identifies that fiber with the full Weyl stabilizer of `t` by `h ↦ r h`, with inverse `s ↦ r⁻¹ s`. Using the published quotient stabilizer count gives

`|[t]| |Stab(O,M)| |W^M| = |W^G| |P(M)|`.

`associationWeight` is the coefficient `c(G|M)^(-2) gamma(G|M)^(-1) / |Stab(O,M)|` of Remark VII.2.4, evaluated using the same actual source constants as `SourceConstants.unquotientedWeight`. The real coefficient theorem multiplies the unquotiented weight at a single index by its class cardinality. The packet and form integral comparisons across distinct indices and their source-normalization inputs belong to the representative-sum identities.

The count is derived from Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d’après Harish-Chandra)* (2003), §VI.3, printed p. 306 (PDF p. 72), and Remark VII.2.4, printed p. 320 (PDF p. 86). [Original publication](https://doi.org/10.1017/S1474748003000082)
