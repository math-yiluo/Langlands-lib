# The split case of the rank-one rational-orbit height bound

Author: Worker 5253.

This module states the split rank-one proposition and retains the published
specialization lemma `splitRankOneParabolicRationalOrbitHeightBound_of_rankOne`.
The split height bound itself remains unproved.

## Statement

`SplitRankOneParabolicRationalOrbitHeightBoundStatement` is the published
`RankOneParabolicRationalOrbitHeightBoundStatement`
(`Langlands/Global/AdelicRankOneOrbitHeightBound.lean`) with exactly one
extra hypothesis: `IsMaximalTorus i`. All other quantifiers and hypotheses
are the same, in the same order. The statement quantifies in universe `u`
over:

- every number field `F`;
- every affine, locally finite type, connected reductive group scheme `G`
  over `Spec F`;
- every actual maximal split torus `i : T ⟶ G` that is also a maximal
  torus;
- every generic cocharacter `ν` of `T` whose set of simple relative roots
  is a singleton `{α}`.

For each such datum, take any actual finite-coordinate representation
`ρ` of `G` and any coordinate `j` whose exact coordinate-line stabilizer
is the empty-index standard parabolic `standardParabolic i ν ∅`. Then
`HasUniformNormOneRationalOrbitHeightBound F G ρ (Pi.single j 1)` holds.
This means there is one constant `C > 0` such that every point `g` of the
ambient norm-one group `G(𝔸_F)¹` has some rational right translate
`g · q`, with `q ∈ G(F)`, whose selected-vector height is at most `C`.

The setup already requires `i` to be a maximal split torus. Adding
`IsMaximalTorus i` therefore restricts the statement to split groups.
Mathematically, the minimal parabolic of such a group is a Borel subgroup,
and the group has semisimple rank one. The Lean statement does not use these
facts. This follows the convention of the published
`SplitAdelicFundamentalSetStatement`
(`Langlands/Global/AdelicSplitFundamentalSet.lean`), which also expresses
splitness by `IsMaximalTorus i` on top of a maximal split torus. No
compactness, Iwasawa, fundamental-set or chamber-coverage premise is
supplied.

The lemma `splitRankOneParabolicRationalOrbitHeightBound_of_rankOne` proves that
`RankOneParabolicRationalOrbitHeightBoundStatement` implies this statement:
forget the hypothesis `IsMaximalTorus i`. The intended proof route goes the other way: Springer
derives the general rank-one case from the split theorem (see below).

## Provenance and role

This is a derived, internal formulation. It is not a quotation of a
source theorem. Its source is Springer, *Reduction theory over global
fields* (1994; source ID `springer-1994-reduction-global-fields`),
§§3.2–3.3. There the split-group case of the fundamental-set theorem
(F) is proved by induction on the rank (Lemma 2.4). The induction
needs the theorem for split groups of semisimple rank one. Lemma 3.3
reduces those groups to `GL₂`, `SL₂` and `PGL₂` times a torus, and §§1.10–1.11
treat these cases.

In the Library, the published chamber-reduction chain
(`hasWeakChamberReduction_of_rankOne_height` in
`Langlands/Global/AdelicChamberFromRankOneHeight.lean`) applies the rank-one
height assertion only to the singleton-root standard Levi subgroups `L_α` of
the ambient group, each with its torus factor. For a split ambient group
these Levi subgroups are again split. So this split case is exactly the
arithmetic input that the split fundamental-set theorem needs. Springer
§3.6 then uses the split theorem over a splitting field to obtain the
general rank-one case.
