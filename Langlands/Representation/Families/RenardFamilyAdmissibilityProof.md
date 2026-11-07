# Renard VI.8.1: the admissibility criterion

Worker 1761 proves the unchanged `AdmissibilityCriterionStatement` at
independent universes `uB`, `uG`, `uV`. The source is Renard,
*Représentations des groupes réductifs p-adiques*, 9 July 2026,
VI.8.1 Proposition, printed p.188 / PDF p.194.
Literature ID: `renard-2026-representations-groupes-reductifs-padiques`;
SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Suppose the original smooth coefficient module is flat and every compact-open
fixed module is finitely generated. The flatness criterion makes each fixed
module flat. Since the coefficient ring is Noetherian, finite generation
implies finite presentation, by `Module.finitePresentation_of_finite`.
The Mathlib theorem `Module.Flat.projective_of_finitePresentation` then
makes each of these modules projective.

Conversely, finite projective fixed modules are flat because projective
modules are flat. The flatness criterion gives flatness of the original
smooth module, and finite generation is already one of the hypotheses.
This proves precisely the published equivalence. The proof changes no
imported statement or definition and adds no hypothesis.
