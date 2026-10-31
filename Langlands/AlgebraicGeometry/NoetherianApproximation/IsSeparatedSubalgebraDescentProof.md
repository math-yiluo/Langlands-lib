# Descent of separatedness to finitely generated subalgebras (proof)

Proof module of task `8b63dc1d-84d3-43fa-a1d5-9657a89c8df1`.

## Statement proved

`Langlands.AlgebraicGeometry.NoetherianApproximation.isSeparatedSubalgebraDescent :
IsSeparatedSubalgebraDescentStatement.{u}`, for an arbitrary universe `u`, without additional
hypotheses. The statement is the published proposition of module
`Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements`: for commutative
rings `A₀`, `A` in `Type u` with `[Algebra A₀ A]`, a quasi-compact, quasi-separated morphism
`f : X ⟶ Spec A₀` whose base change
`pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A)))` is separated, and a finite set
`s ⊆ A`, there is a finitely generated `A₀`-subalgebra `T ⊇ s` of `A` such that the base change
`pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))` is separated. Source: Stacks
Project Lemma 32.8.6 (tag 01ZQ), applied to the presentation of `A` as the directed union of its
finitely generated `A₀`-subalgebras; see the statement module's Markdown for the exact citation.

## Proof

The proposition body is word for word the statement of the ported FLT theorem
`AlgebraicGeometry.IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd` (module
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd`).
The Lean proof introduces the morphism `f`, its three morphism-property instances (quasi-compact,
quasi-separated, separated base change) and the finite set `s` (the rings and algebra instances are
implicit binders, filled by unification) and applies that theorem to `f` and `s`.

The ported FLT proof runs as follows; the Markdown files of the modules named here describe each step.

1. Affineness descends
   (`AlgebraicGeometry.exists_fg_subalgebra_isAffine_pullback_of_isAffine_pullback`): the base change
   to `Spec A` of a quasi-compact, quasi-separated scheme over `Spec A₀` is the limit of its base
   changes to the `Spec T` (`AlgebraicGeometry.SubalgebraStages.nonempty_isLimit_cone`, ported by task
   `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`), and Mathlib's `Scheme.exists_isAffine_of_isLimit` makes
   some stage affine if the limit is.
2. Surjectivity of ring maps descends
   (`Algebra.TensorProduct.exists_fg_subalgebra_surjective_map_of_surjective_map`): if
   `A ⊗[A₀] D → A ⊗[A₀] C` is surjective for a finite-type algebra map `D → C`, so is
   `T ⊗[A₀] D → T ⊗[A₀] C` for a finitely generated `T ⊇ s`.
3. Closed immersions with affine target descend
   (`AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map`):
   for `m : W ⟶ V` quasi-compact, quasi-separated and locally of finite type with `V` affine, the
   base change of `W` to `Spec A` is a closed subscheme of an affine scheme, hence affine, and step 1
   makes the base change of `W` affine at some stage. There the base change of `m` is `Spec` of a ring
   map of finite type, and over every further stage being a closed immersion is surjectivity of that
   ring map tensored with the stage, which descends by step 2.
4. Conclusion (`P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.solution`):
   take a finite affine open cover `Uᵢ` of `X`. For an affine `Y` over `Spec A₀`, the base change of
   `f` to `Y` is separated if and only if, for every pair `i, j`, the base change to `Y` of the chart
   map `Uᵢ ×_X Uⱼ → Uᵢ ×_{A₀} Uⱼ` is a closed immersion (the diagonal checked on the cover). These
   finitely many chart maps satisfy the hypotheses of step 3, so each condition descends to a finitely
   generated subalgebra. An induction over the finite list of pairs collects them in one finitely
   generated `T ⊇ s`; a closed immersion over a stage stays one over every larger stage, by base
   change along `Spec T ⟶ Spec T₁`.

## Dependencies

- `Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements` (Library; the
  target statement).
- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd`
  and its import closure. Seven further ported FLT modules of that closure are submitted with this
  proof: the `Theorems/Thm_*` and `P2M/Sol/S_*` modules of the three theorems of steps 1–3, and the
  solution module of the root theorem. The other three modules of the closure,
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SubalgebraStages`,
  `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone` and
  `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone`, are
  ported by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83` and imported from the Library. All are ported
  from the Anthropic Lean formalization of Fermat's Last Theorem, commit
  `6e837e75355538c7f80bab5b956861e86c4eacc2`, Apache License 2.0, Copyright 2026 Anthropic, PBC; see
  `licenses/Anthropic-FLT/` and the "Source and licence" section of each ported module's Markdown.
- Mathlib only otherwise. The theorem uses only the axioms `propext`, `Classical.choice` and
  `Quot.sound`.
