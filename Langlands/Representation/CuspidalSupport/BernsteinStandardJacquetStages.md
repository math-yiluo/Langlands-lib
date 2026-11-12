# Standard Jacquet stages at the Bernstein carrier universes

Worker 1437 specializes the published generic normalized Jacquet stages
isomorphism to the actual standard family at carrier universe `max uF uV`,
keeping `uF` and `uV` independent. The source and target include the literal
fine-Levi transport used by `BernsteinInductionRestrictionStatement`.

`bernsteinStandardJacquetStagesIso` repeats the proof of
`RationalJacquetStages.standardJacquetStagesIso`, applying the underlying
`normalizedJacquetStagesIso` at the target's carrier universe rather than
at `max (uF + 1) uV`. The fine radical is the join of the coarse radical
and its intersection with the coarse Levi. Closedness is inherited from
the standard family. The standard-cocharacter theorem supplies compact
containment for the inner radical, and the standard Haar-modulus stages
equality follows from continuity of the standard projections. These facts
discharge every hypothesis of the generic isomorphism.

`bernsteinLeviJacquet_isSubquotient` applies exact smooth transport to the
inner normalized Jacquet functor. Compact containment supplies its
short-exactness; the final group-equivalence pullback keeps the same vector
spaces and linear maps, so the same exactness witnesses apply.

This is derived internal content from the existing modules, in the source
context of Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, VI.1 (transitivity) and VI.7.3 (printed p.185 /
PDF p.191), registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Neither theorem assumes or proves Bernstein block characterization.
