# Descent of properness to finitely generated subalgebras (proof)

Proof submitted by task `e36ae7da-512e-4a4d-a902-71146c92ec82`.

## Statement proved

`Langlands.AlgebraicGeometry.NoetherianApproximation.isProperSubalgebraDescent :
IsProperSubalgebraDescentStatement.{u}`, for an arbitrary universe `u`. The statement is the published
proposition of module `Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements`
(statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`): for a noetherian commutative ring `A₀`,
an `A₀`-algebra `A` (both in `Type u`), a separated, quasi-compact morphism `f : X ⟶ Spec A₀` that is
locally of finite type and whose base change `pullback.snd f (Spec.map (algebraMap A₀ A))` is proper,
and a finite set `s ⊆ A`, there is a finitely generated `A₀`-subalgebra `T ⊇ s` of `A` such that the
base change `pullback.snd f (Spec.map (algebraMap A₀ ↥T))` is proper.
Source: Stacks Project Lemma 32.13.1 (tag 081F, properness descends along limits), applied to the
presentation of `A` as the directed union of its finitely generated `A₀`-subalgebras; the FLT proof
uses the noetherian hypothesis for Chow's lemma.

## Proof

The proposition body is word for word the statement of the ported FLT theorem
`AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd` (module
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd`).
The proof binds the morphism `f`, its four instance hypotheses (separated, quasi-compact, locally of
finite type, proper base change) and the finite set `s` (the rings, the noetherian instance and the
algebra instances are implicit binders) and applies that theorem.

The FLT proof, in the imported port modules, runs as follows (see their Markdown files): a Chow-type
theorem (`exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated`, built from the integral
case over the irreducible components of the noetherian scheme `X`, using projective space
`ProjSpace`) gives a proper surjective `π : X' ⟶ X` and an open immersion `j : X' ⟶ P` into a proper
`P ⟶ Spec A₀` with `j ≫ q = π ≫ f`. A base change of `f` is proper exactly when the preimage of the
image of `j` is closed in the base change of `P`. Over `A` this preimage is open and closed; its
complement, a quasi-compact open, descends to a finitely generated subalgebra by Mathlib's limit
lemmas (`exists_preimage_eq`, `exists_map_preimage_eq_map_preimage`) along the limit cone
`SubalgebraStages.nonempty_isLimit_cone` of task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`, which makes the preimage closed over some
`T ⊇ s`.

## Dependencies

- `Langlands.AlgebraicGeometry.NoetherianApproximation.SubalgebraDescentStatements` (Library).
- `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_IsProper_exists_fg_subalgebra_of_isProper_pullback_snd`
  and its import closure: 7 further ported FLT modules submitted with this proof, the three modules
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SubalgebraStages`,
  `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone` and
  `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone`
  (port of task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`), and
  `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (published with the FLT port
  of task `69435287-9f1e-4abd-8483-5e65ff23668a`). All three dependency ports are imported from the
  Library, not resubmitted here. Apache License 2.0, Copyright 2026 Anthropic, PBC, see
  `licenses/Anthropic-FLT/`.
