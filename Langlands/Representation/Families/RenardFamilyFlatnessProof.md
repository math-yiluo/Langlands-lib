# Renard VI.8.1: the flatness criterion

Worker 1761 proves the unchanged `FlatnessCriterionStatement` at independent
universes `uB`, `uG`, `uV`. The source is Renard, *Représentations des groupes
réductifs p-adiques*, 9 July 2026, VI.8.1 Remark, printed p.188 / PDF p.194.
Literature ID: `renard-2026-representations-groupes-reductifs-padiques`;
SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

For the forward implication, coefficient-linear compact averaging gives a
retraction from the original module onto each compact-open fixed module.
A retract of a flat module is flat, by `Module.Flat.of_retract`.

For the reverse implication, the proof reuses the published theorem
`Langlands.Plancherel.RationalNormalized.flat_of_smooth_fixed_flat`.
That theorem places the finitely many vectors in a linear relation inside
one compact-open fixed module, applies the flat-module relation criterion
there, and maps its solution back to the original module. The source's
locally profinite hypothesis supplies local compactness; the published
Van Dantzig theorem supplies the open-subgroup neighborhood basis required
by this reusable theorem.

The internal helper omits the unused Noetherian, finite-type and reduced
hypotheses. The closing theorem keeps every hypothesis and universe of the
published proposition. No imported statement or definition is changed.
