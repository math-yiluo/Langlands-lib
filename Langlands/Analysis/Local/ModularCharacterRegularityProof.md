# Modular-character regularity and compact-subgroup triviality

Proof: Worker 103. Documentation and submission: Worker 1580.

`Langlands.Haar.modularCharacterRegularity` proves exactly
`Langlands.Haar.ModularCharacterRegularityStatement.{u}` for every universe
`u`. For every locally compact nonarchimedean group, Mathlib's actual
`MeasureTheory.Measure.modularCharacter` has open kernel, is locally
constant and continuous, and is one on every compact subgroup. The theorem
adds no hypotheses to the published statement; in particular, it assumes
neither Hausdorffness nor second countability.

The proof first establishes
`modularCharacter_eq_one_of_mem_compactOpen` for every locally compact
topological group. It uses the canonical Borel Haar measure, whose right
translate is regular because right translation is a homeomorphism. Regular
Haar uniqueness, together with `modularCharacterFun_eq_haarScalarFactor`,
identifies that translate with the modular character times the original
measure. An element of a compact open subgroup preserves that subgroup by
right translation. Evaluating the equality of measures on the subgroup and
cancelling its positive finite Haar mass gives character value one. The
proof uses regular Haar uniqueness directly, avoiding an additional
inner-regularity premise on the right-scaling lemma.

`Langlands.compactOpenSubgroupBasis` supplies a compact open subgroup in the
nonarchimedean case. It lies in the character's kernel, so
`Subgroup.isOpen_mono` proves that the kernel is open. The proof of
`isLocallyConstant_modularCharacter` uses the open neighborhood of each
`x` consisting of `y` with `y * x⁻¹` in the kernel. Multiplicativity and
positivity of the character make its value constant there. Local constancy
then gives `continuous_modularCharacter`.

For any compact subgroup `K`, the restricted character is locally constant
on the compact subtype `K`, so its range is finite. The helper
`positiveCharacter_eq_one_of_finite_range` lifts a nonnegative-real
character to units, regards its image as a finite group, and uses the
finite order of each image element. A nonnegative real whose positive
integral power is one equals one. This proves
`modularCharacter_eq_one_of_mem_compact`, and the final theorem packages
the four conclusions.

The compact-subgroup assertion is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, II.3.7(i), printed
page 47 / PDF page 53; source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The cited page was read and its modular-function formula checked. Renard
uses the reciprocal of Mathlib's convention, which preserves all four
conclusions. The implemented proof uses the finite-image consequence of
local constancy in place of Renard's compact-positive-real subgroup
argument. Open kernel, local constancy, continuity and the extension without
Hausdorffness are internal derived content, as recorded in the unchanged
statement companion. This proof establishes the analytic prerequisite;
reductive unimodularity and the rational-parabolic modulus formula remain
separate obligations.
