# Pseudo-reductivity after separable algebraic extension

Author: Worker 1661.

The theorem `Langlands.GroupScheme.pseudoReductiveSeparableExtension` proves
the unchanged published proposition
`Langlands.GroupScheme.PseudoReductiveSeparableExtensionStatement.{u}`
for arbitrary universe `u`. The module also provides the corresponding
method `IsPseudoReductive.baseChange_of_separableExtension`.

For fields `k K : Type u`, with `[Algebra k K]` and
`[Algebra.IsSeparable k K]`, and any group scheme `G` over `Spec k`, the sole
mathematical premise is `IsPseudoReductive G`. The conclusion is the full
published predicate on the actual scheme pullback `G_K`: smoothness,
affineness, connectedness, and `HasTrivialUnipotentRadical`. The extension
may be infinite and need not be normal; the fields may be imperfect.

## Implemented argument

Smoothness and affineness follow from their pullback instances. Connectedness
follows from `connectedSpace_baseChange_of_smooth_affine`, after installing
the three corresponding fields of the original pseudo-reductive predicate
as local instances.

For the radical field, set `L = SeparableClosure k`. Mathlib supplies the
`k`-algebra embedding `ι : K →ₐ[k] L` by `IsSepClosed.lift`, using exactly
the separability hypothesis. Give `L` its `K`-algebra structure from `ι`.
The existing `k`-algebra structure on `L` is retained. If `b : Spec K → Spec k`,
`d : Spec L → Spec K`, and `c : Spec L → Spec k` are the induced morphisms,
the equality `d ≫ b = c` follows directly from `ι.commutes`.

The extension `L/k` is Galois. The published theorem
`IsPseudoReductive.baseChange_galois`, imported from
`Langlands.GroupScheme.Reductive.GaloisRadicalDescent`, therefore proves that
`G_L` is pseudo-reductive. This result works for arbitrary Galois extensions
and supplies its radical and descent argument internally.

Take the trivial-unipotent-radical field of that predicate, rewrite by the
composition equality, and transport through `baseChangeCompIso` to obtain
`HasTrivialUnipotentRadical (G_K)_L`. The published
`HasTrivialUnipotentRadical.of_fieldExtension`, from
`Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof`, reflects
this property to `G_K`, whose affineness was already established. This
reflection uses preservation of smooth connected unipotent normal closed
subgroups and fpqc reflection of their triviality, with all relative test
schemes retained. There is no supplied radical, Galois condition on `K/k`,
descent premise, finiteness assumption, or perfectness assumption in the result.

## Provenance

This proof is an internal deduction from the published Galois-ascent,
field-reflection, geometric-connectedness, and pullback-coherence results,
together with Mathlib's separable-closure embedding. It changes none of the
statement or its imported definitions and introduces no new axiom.

The unchanged target derives from Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Proposition 1.1.9(1),
printed pp.8–9 (PDF pp.34–35), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The source covers general separable extensions and equality of radicals.
This proof establishes exactly the published algebraic-separable forward
implication. For this restricted scope the embedding into `L` and reflection
complete the Galois reduction, so the source's later specialization argument
for transcendental separable extensions is unnecessary.
