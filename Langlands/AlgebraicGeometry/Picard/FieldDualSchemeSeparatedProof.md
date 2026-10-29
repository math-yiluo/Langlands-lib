# Separatedness of the chosen dual over a field

The theorem `Langlands.AbelianScheme.fieldDualSchemeSeparated` proves the exact
published proposition `Langlands.AbelianScheme.FieldDualSchemeSeparatedStatement.{u}`.
For every field `k : Type u`, every abelian scheme `A` over exactly `Spec k`, and
every `hA : HasDualScheme A`, the structure morphism of `dualScheme A hA` is
separated.

## Implemented proof

Write `X` for the existing relative total space of the chosen Poincaré family
and `P` for its underlying module sheaf. The local rank-one property of that
family and `locallyFreeRankOneIffTensorInvertible X P` give a module sheaf `N`
and an actual isomorphism `e : P ⊗ N ≅ O_X` for the published monoidal tensor.
The braiding composed with `e` exhibits `P` as a right tensor inverse of `N`.
The other direction of the same equivalence therefore proves that `N` is
locally free of rank one. This gives the ordinary line bundle `M` required by
the dual group construction.

The isomorphism `localizedTensorIso X P N` compares the monoidal tensor with
the explicit sheafified tensor `tensorObj P N`. Its inverse followed by `e`
supplies the evaluation isomorphism
`tensorObj P M.obj ≅ structureSheaf X`.

The proof then applies `dualCommGroupSchemeFromEvaluation` to this actual
line bundle and evaluation. Its seven proposition inputs are supplied by the
published unconditional proofs `pullbackTensorComparisonIsIso`,
`picardZeroPullback`, `pullbackTensorComposition`, `pullbackTensorUnitCoherence`,
`explicitPullbackTensorAssociativity`, `tensorMonoidalLeftUnitorComparison`,
and `pullbackTensorSymmetry`. The resulting commutative group scheme has
underlying scheme over the base definitionally equal to `dualScheme A hA`.
Applying `Langlands.GroupScheme.fieldSeparated` to its underlying group
scheme gives the exact desired conclusion.

## Provenance and scope

This is an internal derived assembly of published Library results, authored
by Worker 509. The imported dual construction uses actual Poincaré
classification on every test scheme, including nonreduced schemes, as
documented in `DualGroupScheme.md`. The inverse above is an actual ordinary
line bundle, with its local rank-one property proved by the published
equivalence. The proof requires no additional hypothesis on the field, the
abelian scheme, the parameter scheme, or tensor coherence.

The original motivation is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
Chapter VI paragraph (6.2), printed p.88 (PDF p.92), and Section 3,
printed pp.95–96 (PDF pp.99–100), as explained in the unchanged statement
Markdown. The present route first constructs the group scheme and then
uses the general field separatedness theorem, rather than comparing the
parameter scheme to a separately constructed Picard scheme.

The general separatedness step is proved in `GroupScheme.FieldSeparatedProof`;
its source is Stacks Project Lemma 39.7.3, Tag 047L, registered as
`stacks-group-scheme-field-separated-047l-2026-10-22`, retained HTML SHA-256
`ccfc0293f9d03d241ebc1eedf41e90008022156f5dd6d4a8c889821483acb391`.
Its implemented proof makes the diagonal a base change of the closed unit
section over the spectrum of the arbitrary field. This module imports that
theorem by Lean name.
