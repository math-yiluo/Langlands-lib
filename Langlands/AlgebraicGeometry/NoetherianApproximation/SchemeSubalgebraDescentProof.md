# Descent of schemes of finite presentation to finitely generated subalgebras (proof)

Proof module of task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`.

## Statement proved

`Langlands.AlgebraicGeometry.NoetherianApproximation.schemeSubalgebraDescent :
SchemeSubalgebraDescentStatement.{u}`, for an arbitrary universe `u`, without additional hypotheses.
The statement is the published proposition of module
`Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements`: for commutative
rings `A₀`, `A` in `Type u` with `[Algebra A₀ A]`, a quasi-compact, quasi-separated morphism
`g : X ⟶ Spec A` that is locally of finite presentation, and a finite set `s ⊆ A`, there are a
finitely generated `A₀`-subalgebra `T ⊇ s` of `A`, a morphism `f₀ : X₀ ⟶ Spec T` that is locally of
finite presentation, quasi-compact and quasi-separated, and `π : X ⟶ X₀` with
`IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))`. Source: Stacks Project
Lemma 32.10.1(1) (tag 01ZM), applied to the presentation of `A` as the directed union of its finitely
generated `A₀`-subalgebras; see the statement module's Markdown for the exact citation.

## Proof

The proposition body is word for word the statement of the ported FLT theorem
`AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation` (module
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation`).
The Lean proof introduces the morphism `g`, its three morphism-property instances and the finite
set `s` (the rings and algebra instances are implicit binders, filled by unification) and applies
that theorem to `g` and `s`.

The ported FLT proof runs as follows; the Markdown files of the modules named here describe each step.

1. Affine case
   (`AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation`):
   `A` is the direct limit (`IsDirectLimit`) of its finitely generated `A₀`-subalgebras containing a
   given finite set and the image of an auxiliary finite-type `A₀`-algebra `R`, and the finitely
   presented `A`-algebra `Γ(X, ⊤)` descends to a finitely presented algebra over one of them
   (`Algebra.exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit`); `Spec` turns the
   tensor-product pushout square into the required pullback square.
2. Limit presentation (`AlgebraicGeometry.SubalgebraStages.nonempty_isLimit_cone`): for a directed
   family of subalgebras exhausting `A`, the base change of a scheme over `Spec A₀` to `Spec A` is the
   limit of its base changes to the `Spec` of the subalgebras.
3. Descent of quasi-compact opens, morphisms, equalities of morphisms and isomorphisms
   (`exists_fg_subalgebra_opens_preimage_eq_of_isCompact`,
   `exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation`,
   `exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType`,
   `exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation`), from step 2
   and Mathlib's results on cofiltered limits of schemes with affine transition maps.
4. Two-open step (`exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation`):
   models of two quasi-compact opens `U`, `V` are moved to a common subalgebra, the open `U ∩ V` is
   descended into both models, the comparison isomorphism of the two induced models of `U ∩ V` is
   descended, and the two models are glued along it
   (`exists_isPullback_glue_of_isPullback_of_isOpenImmersion`); every enlargement of the subalgebra
   stays finitely generated (`Subalgebra.fg_restrictScalars_and_le_of_fg`).
5. Conclusion: Mathlib's `compact_open_induction_on` (every quasi-compact open is obtained from `⊥`
   by adding affine opens) combines steps 1 and 4 into models of every quasi-compact open of `X`;
   `X` is quasi-compact, and the open `⊤` is isomorphic to `X`.

## Dependencies

- `Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements` (Library; the
  target statement).
- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation`
  and its import closure of 23 further ported FLT modules under `Langlands/AnthropicFLT/` (submitted
  with this proof). These are ported from the Anthropic Lean formalization of Fermat's Last Theorem,
  commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, Apache License 2.0, Copyright 2026 Anthropic, PBC;
  see `licenses/Anthropic-FLT/` and the "Source and licence" section of each ported module's Markdown.
- Mathlib only otherwise. The theorem uses only the axioms `propext`, `Classical.choice` and
  `Quot.sound`.
