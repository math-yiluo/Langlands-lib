# Geometric-fibre reduction for relative Levi self-normalization

This internal construction and its transport lemmas retain the original relative
Levi multiplication decomposition on the canonical geometric fibres. For a
reductive group scheme, a relative parabolic and a relative Levi subgroup, the
construction `geometricComplement` chooses one supplied relative radical, pulls
its inclusion to the geometric fibre and retains its actual unipotent-radical
property and the multiplication isomorphism there. It also retains connected
reductivity of the ambient fibre and parabolicity of its inclusion. The latter
uses the published field-extension theorem on the residue fibre, followed by
the natural comparison for successive pullbacks.

The accompanying detection theorem is more general: a smooth closed subgroup
of a smooth affine group over any scheme is self-normalizing if its canonical
geometric fibres are self-normalizing as subgroup functors on all test schemes.
No geometric connectedness premise is needed. Equality first descends from an
algebraic closure to the residue field by the published fpqc reflection lemma.
Every field-valued point of the base factors through its residue field, so the
normalizer base-change theorem supplies equality after all field-valued base
changes. The published smooth affine detection helper then gives range
membership on affine tests, and affine-cover descent gives membership on all
tests. The reverse inclusion is the general inclusion into a normalizer.

These are derived implementation results, not transcriptions of additional
source claims. Their inputs are the published relative predicates and the
published parabolic extension, product comparison, fpqc descent and smooth
field-detection theorems. The construction supplies the geometric-fibre input
needed to apply a field complement theorem in the proof of Conrad's relative
Levi self-normalizer assertion. This module does not itself discharge the
field complement theorem.

Shared declarations `isIso_subgroupMultiplication_baseChange` are imported from `Langlands.GroupScheme.RelativeLevi.ConjugatorUniquenessBaseChange`; their mathematical hypotheses, conclusions and data are unchanged.
