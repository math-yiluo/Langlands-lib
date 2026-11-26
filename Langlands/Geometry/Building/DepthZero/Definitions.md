# Depth-zero constructions on KP building data

Let \(F\) be a nonarchimedean local field of either characteristic, \(G\) an
affine group scheme over \(F\), \(D : \mathrm{KPBuildingDatum}\ G\), and \(x\)
any facet of the reduced building of \(D\). All constructions use the facet
model `D.models.facetModels.model x` and its supplied quotient data
`D.quotients.quotient x`. Write \(k_F\) for the residue field.

The declarations are in `Langlands.Geometry.Building.KPBuildingDatum`.

| Declaration | Object |
| --- | --- |
| `parahoric` | \(P_x = G_x^0(\mathcal O_F)\), the integral points of the neutral facet model inside \(G(F)\). Axiom 4.1.20 for \(D\) identifies this group with the pointwise fixer in \(G(F)^0\). The full stabilizer in \(G(F)\) and the fixer in \(G(F)^1\) have their own definitions. |
| `parahoricRadical` | \(P_{x,0+}\) as a subgroup of \(P_x\), obtained by restricting `SpecialFibreQuotientData.positivePoints` to \(P_x\). Its elements reduce into the specified radical of the neutral special fibre. |
| `reductiveQuotient`, `reductiveQuotientPoints` | The specified quotient scheme \(\bar G_x\) of the neutral special fibre and its point group \(\bar G_x(k_F)\). Axiom 4.1.22 for \(D\) identifies the projection as the quotient by the unipotent radical and gives connected reductivity of \(\bar G_x\). |
| `parahoricReduction` | The homomorphism \(P_x\to\bar G_x(k_F)\), obtained by composing reduction to the neutral special fibre with projection on residue-field points. It is `SpecialFibreQuotientData.parahoricReduction`. |
| `finiteReductiveQuotientGroup` | The same point group bundled as a `FiniteGrp`. It applies `SpecialFibreQuotientData.finiteQuotientGroup` using the connected-reductivity clause of `D.SatisfiesGroupAxioms` to obtain finite type. |
| `parahoricOpenSubgroup` | \(P_x\) bundled as an open subgroup via `RelativeComponentModelData.localFieldIntegralOpenSubgroup`. |
| `depthZeroInflation` | The inflation of a complex representation \(\sigma\) of \(\bar G_x(k_F)\) through `parahoricReduction`, given by `SpecialFibreQuotientData.inflation`. |
| `depthZeroCompactInduction` | The bundled smooth \(\mathrm{c\text{-}Ind}_{P_x}^{G(F)}\operatorname{infl}\sigma\), given by `SpecialFibreQuotientData.depthZeroInduction`. It uses the published openness of the level-one congruence subgroup. |

The topology on \(G(F)\) is `rationalPointTopology F G.X`. Compact induction
uses the topological group structure for this topology, which takes local
finite type of \(G\) as a premise. Connected reductivity supplies that premise
via smoothness. Smoothness means open vector stabilizers, as for a discrete
representation space. The constructions select objects from the supplied data
and make no existence claim for buildings, models or quotient schemes.

## Sources

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Axiom 4.1.20 and
  Definition 4.1.21 (printed p. 163, PDF p. 194) for the neutral parahoric
  model, Axiom 4.1.22(3), (7) (printed p. 164, PDF p. 195) for the maximal
  reductive quotient and radical preimage, and §13.2.6 (printed p. 470,
  PDF p. 501) for the composite reduction. Remark 2.10.3 (printed p. 122,
  PDF p. 153) describes the integral points in the analytic topology.
  Literature ID `kaletha-prasad-2023-bruhat-tits-new-approach`,
  SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024, PDF p. 27
  for the axiom list of Definition 4.1.26 used by the one-group predicate.
  Literature ID `kaletha-prasad-2024-corrections`,
  SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
- Vignéras, *Représentations ℓ-modulaires d'un groupe réductif p-adique avec
  ℓ ≠ p* (1996), I.5.1–5.2 (printed pp. 38–39, PDF pp. 56–57) for the
  covariant function model of compact induction and right translation.
  Inflation here is pullback along the KP reduction, to which that compact
  induction is applied.
  Literature ID `provided-74667a7cddb3bdafff85f01c658605ce7d929f6da73950d79457c46bcd761dd4`,
  SHA-256 `4d2daeee16515f994dfb04157915179b55b30d5bf2f874a16f13e7cb6fa7d657`.
