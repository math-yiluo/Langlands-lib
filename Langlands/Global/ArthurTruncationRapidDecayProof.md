# Arthur's Proposition 13.2 on `G(F) \ G(𝔸_F)¹`

**Sources.** J. Arthur, *An introduction to the trace formula* (2005),
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, §4, printed p. 24 (PDF p. 36), and §13,
Proposition 13.2 with (13.5)–(13.8), printed pp. 70–72 (PDF pp. 82–84); J. Arthur, *A trace formula
for reductive groups II* (1980), `arthur-1980-trace-formula-reductive-groups-II`, Lemma 1.4,
printed pp. 95–97 (PDF pp. 10–12).

The module `Langlands.Global.ArthurTruncationRapidDecayProof` proves the target
`Langlands.Global.ArthurTruncation.TruncationRapidDecayStatement`
([statement](ArthurTruncationRapidDecayStatement.md)) as `truncationRapidDecay`. All declarations
are in `Langlands.Global.ArthurTruncation`.

## The maximal compact subgroup

`exists_parabolicIwasawaCompact_positiveTorusCompatible`: for `G` connected reductive over a number
field, a maximal split torus `i` and a generic cocharacter `ν`, there is a subgroup `K` of
`G(𝔸_F)` with `IsParabolicIwasawaCompact` for the standard minimal parabolic `P₀` (so `K` is a
maximal compact subgroup with `P₀(𝔸_F) K = G(𝔸_F)`), whose parabolic part commutes with the positive
torus of every Siegel setup (`IsPositiveTorusCompatible`). It is assembled from an integral Iwasawa
family (`IntegralIwasawaFamily.existenceStatement`), the finite-place Iwasawa decompositions
(`FinitePlaceGroupPoints.parabolicIwasawaStatement`) and Levi-compatible archimedean Iwasawa compacts
(`InfinitePlaceGroupPoints.leviCompatibleIwasawaStatement`) by
`exists_leviCompatible_parabolicIwasawaCompact`. The compatibility with the positive torus follows
from the Levi compatibility of the archimedean factors
(`isPositiveTorusCompatible_coordinateSubgroup`).

## The proof

`normOneTruncationFamilyEstimate` proves `NormOneTruncationFamilyEstimateStatement`: for an embedded
atlas `At`, take `K` as above. For reflection data, the comparison and a closed matrix realization,
`exists_isNormOneFamilyEstimate` (module `Langlands.Global.ArthurNormOneFamilyEstimateProof`) gives
the threshold and the family estimate with the operators, differentiability order and constant
chosen before the family and its measure space.

`truncationRapidDecay` applies `truncationRapidDecayStatement_of_familyEstimate`
([reduction](ArthurTruncationRapidDecayReduction.md)). The reduction chooses the embedded atlas on
`G(F∞)¹` by `exists_normOneLieAtlas` and applies the family estimate to this atlas and the chosen
`K`. To deduce rapid decrease for a smooth uniformly tempered input, it specializes the family
estimate to a one-point measure space. Uniform temperedness bounds the finitely many derivatives
by a common height exponent, so a sufficiently large growth exponent in the family estimate gives
a finite bound for each decay order.
