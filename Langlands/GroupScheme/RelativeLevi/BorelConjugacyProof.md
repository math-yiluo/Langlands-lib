# Borel subgroup schemes are conjugate étale-locally

`Langlands.GroupScheme.relativeBorelEtaleLocalConjugacyStatement` proves
the unchanged `RelativeBorelEtaleLocalConjugacyStatement.{u}` in every
universe, over an arbitrary scheme and with precisely the reductivity and
relative Borel hypotheses of that statement.

The proof applies `relativeBorelEtaleLocalConjugacy_of_parabolic` to
`relativeParabolicEtaleLocalConjugacyStatement`. The latter proves the
relative parabolic conjugacy proposition. The former supplies its
residue-field conjugacy hypothesis using rational conjugacy of minimal
parabolics: each relative Borel fibre is a geometric Borel, hence a
minimal rational parabolic, in the connected reductive residue fibre.
It then chooses an étale neighbourhood with a conjugating section for
each point of the base and assembles these into the required jointly
surjective étale cover. The conclusion compares subgroup-functor ranges
on every test scheme over every cover member.

All mathematical inputs are Library declarations explained in their
paired Markdown. This proof composes those inputs and introduces no
additional hypotheses or changes to the target statement.
