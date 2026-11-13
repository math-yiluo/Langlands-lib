# `⁰A₁ = A₁ ∩ ⁰A₂` for split tori `A₁ ⊆ A₂` (Renard V.2.5)

Author: Worker 103 (Task 5711, `8f1184cf-8c14-4ede-a502-96f1d8f66ec2`).

Module `Langlands.Representation.Plancherel.RationalNormKernelRestrictionProof`.
The theorem `Langlands.Plancherel.rationalNormKernelRestriction` proves exactly the
published proposition
`Langlands.Plancherel.RationalNormKernelRestrictionStatement.{u}` (module
[`RationalNormKernelRemarksStatements`](RationalNormKernelRemarksStatements.md)).
It holds at every universe `u` and adds no hypotheses.

## Statement

Let `F : Type u` be a nonarchimedean local field, of any characteristic, and let `A₁`, `A₂`
be commutative group schemes over `Spec F` with a morphism `f : A₁ ⟶ A₂`. Assume that
`A₂` is a split torus (`IsSplitTorus A₂.toGrp`) and that `f` is a split subtorus
(`IsSplitSubtorus f`: `A₁` is a split torus and `f` is a closed immersion). Then
`(rationalCommonNormKernel A₂.toGrp).comap (rationalPoints.map f) = rationalCommonNormKernel A₁.toGrp`.
That is, a point `t ∈ A₁(F)` lies in `⁰A₁` exactly when `f(t)` lies in `⁰A₂`.

## Implemented proof

The proof shows both inclusions (`le_antisymm`).

- **`comap ⁰A₂ ≤ ⁰A₁`.** Let `t ∈ A₁(F)` with `f(t) ∈ ⁰A₂`. By
  `mem_rationalCommonNormKernel`, it suffices to show that
  `fieldNormUnits F (χ(t)) = 1` for every rational character `χ` of `A₁`.
  - The closed-immersion half of `IsSplitSubtorus f` is installed as an instance. Mathlib's
    instance `IsPreimmersion f → Mono f` (priority 900) then makes
    `f.hom.hom.left` a monomorphism of schemes.
  - The published `IsSplitTorus.characterRestrict_surjective_of_mono` (module
    [`SplitTorusCharacterRestriction`](../../GroupScheme/Rational/SplitTorusCharacterRestriction.md))
    applies to the split tori `A₁`, `A₂` and the monomorphism `f`. It says that restriction
    of characters `characterRestrict f : X*(A₂) → X*(A₁)` is surjective. Choose `χ'` with
    `characterRestrict f χ' = χ`.
  - `GroupScheme.rationalCharacterEval_characterRestrict` rewrites `χ(t)` as `χ'(f(t))`.
    Since `f(t) ∈ ⁰A₂`, `fieldNormUnits F (χ'(f(t))) = 1`.
- **`⁰A₁ ≤ comap ⁰A₂`.** This is the published `rationalCommonNormKernel_le_comap f`
  (module [`RationalUnramifiedRestriction`](RationalUnramifiedRestriction.md)). Rational
  characters of `A₂` restrict to rational characters of `A₁`, so the point map of any
  morphism sends the norm kernel into the norm kernel.

The first inclusion is the only one that uses the split-torus hypotheses.

`lean_check` reports that the theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Relation to the literature

David Renard, *Représentations des groupes réductifs p-adiques* (registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`), V.2.5, last paragraph
(printed p.107 / PDF p.113): « Si `A₁` et `A₂` sont deux tores déployés définis sur `F`,
avec `A₁ ⊂ A₂`, alors `Λ(A₁) ⊂ Λ(A₂)`. En effet, d'après ce qui précède, on voit
facilement que `⁰A₁ = A₁ ∩ ⁰A₂`. » Renard leaves the argument to the reader. The Lean
proof uses the standard fact behind it: every character of a closed subtorus of a split
torus extends to the ambient torus. As the statement's Markdown explains, the inverse-image
form is Renard's intersection `A₁ ∩ ⁰A₂`, since `f` is injective on points.

## Scope

This proves only `RationalNormKernelRestrictionStatement`. It does not prove the
consequence `Λ(A₁) ⊂ Λ(A₂)`, nor the analogous V.2.6 Lemma for the split component, which
is the separate `RenardCartan.SplitComponentKernelStatement`. The other two statements of
the module are proved in
[`RationalNormKernelUnimodularProof`](RationalNormKernelUnimodularProof.md) and
[`RationalNormKernelCompactCenterProof`](RationalNormKernelCompactCenterProof.md).

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Plancherel.RationalNormKernelRemarksStatements` | the target statement, `rationalCommonNormKernel`, `mem_rationalCommonNormKernel` (through its imports) |
| `Langlands.GroupScheme.Rational.SplitTorusCharacterRestriction` | `IsSplitTorus.characterRestrict_surjective_of_mono` |
| `Langlands.Representation.Plancherel.RationalUnramifiedRestriction` | `rationalCommonNormKernel_le_comap` |
