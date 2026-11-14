# Relative Borel conjugacy from relative parabolic conjugacy

Worker 607.

This derived internal reduction keeps both published statement definitions
unchanged. It uses the current Library's rational minimal-parabolic conjugacy
theorem to supply the residue-field hypothesis of
`RelativeParabolicEtaleLocalConjugacyStatement`.

`IsRelativeBorelSubgroup.residueFiber_conjugate` proves conjugacy of any two
relative Borel subgroup fibres over the actual residue field κ(s). The
published `IsReductive.isConnectedReductive_residueFiber` supplies a connected
reductive ambient field group. Each fibre is a geometric Borel by the
definition of a relative Borel. The published
`IsGeometricBorelSubgroup.isMinimalParabolicSubgroup` therefore makes each a
minimal rational parabolic. The published `minimalParabolicConjugacy` gives a
rational conjugating point and an isomorphism between the sources. Taking
all-test ranges removes that source isomorphism.

`relativeBorelEtaleConjugacyData` assumes the still separate proposition
`RelativeParabolicEtaleLocalConjugacyStatement.{u}` and constructs an actual
étale cover together with a conjugating section and its all-test range equality
on every member. Apply the assumed
parabolic proposition at each base point with the residue-field conjugacy
just proved. Choose its étale neighbourhood, a point over the original base
point, and a conjugating section. Indexing these neighbourhoods by the points
of the base gives a jointly surjective family of étale morphisms, constructed
with Mathlib's `Scheme.Cover.mkOfCovers`. The chosen sections give the desired
range equality on each member. This also covers an empty base: its point
index type and the resulting cover are empty.

`relativeBorelEtaleLocalConjugacy_of_parabolic` packages these chosen data as
the proposition `RelativeBorelEtaleLocalConjugacyStatement.{u}`. It retains
the parabolic-conjugacy premise.

The source target is Conrad, *Reductive group schemes* (2014), Theorem
5.2.11(2), p.157; its proof on p.158 refers to Corollary 5.2.7. This Lean
reduction uses rational conjugacy of minimal parabolics, rather than a
separate geometric-point spreading argument, to satisfy the published
residue-field version of that corollary. The mathematical inputs are the
published Library declarations cited above, whose paired Markdown records
their original-source provenance. The implication does not discharge its
parabolic-conjugacy premise and is not an unconditional proof of the target.
