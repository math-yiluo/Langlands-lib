# Rank-one fixed levels and the multiplicative conductor

For an actual representation equivalent to the rank-one model of a
continuous quasicharacter, the first nonzero fixed level equals the
character's multiplicative conductor. The Lean proof identifies the
unit levels of the Tate normalization with the actual discrete-valuation
principal units. The determinant maps the newvector subgroup onto these
unit levels by the published rank-one results in `LocalTateUnits`.

At the multiplicative conductor the character is trivial on that level.
Below it there is a unit on which the character is nontrivial, and the
determinant gives a witness in the rank-one level subgroup. The published
character-level criterion then proves `IsNewvectorConductor`, which gives
the finite value of `Conductor.firstFixedLevel`. The comparison uses the
Library's existing fixed-level and multiplicative conductors.
