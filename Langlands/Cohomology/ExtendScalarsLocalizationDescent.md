# Morphisms of scalar extensions to a localization

Author: Worker 1103.

This internal helper module collects lemmas about morphisms between ordinary
scalar extensions `(ModuleCat.extendScalars φ).obj M` along a ring
homomorphism `φ : R →+* A`, where `A` is a localization of `R` at a submonoid
`T` in the sense of `T.IsLocalizationMap φ`. Rings and module carriers live in
one universe `u`. The lemmas are used by
`Langlands.Cohomology.PrimeFreeHomotopyDescentProof` to descend a homotopy
equivalence from `R_p` to some `R_r`. They are standard finite-presentation
facts about localization, the mechanism described in the statement Markdown
`Langlands/Cohomology/PrimeFreeHomotopyDescentStatement.md`. They are derived
here from Mathlib's single-module results and make no claim beyond the Lean
statements below; no literature statement is formalized.

## Single morphisms

- `extendScalars_map_smul`: extension of scalars carries `r • v` to
  `φ r • (extendScalars φ).map v`. The proof checks this on tensors `1 ⊗ m`
  with `ModuleCat.ExtendScalars.hom_ext`.
- `exists_extendScalars_map_eq_smul_of_isLocalizationMap`: for `M` finitely
  presented over `R`, every morphism
  `g : extendScalars φ M ⟶ extendScalars φ N` satisfies
  `(extendScalars φ).map v = φ t • g` for some `t ∈ T` and some `v : M ⟶ N`.
  The proof regards `N → A ⊗[R] N`, `n ↦ 1 ⊗ n`, as a localized module (via
  `isLocalizedModule_iff_isBaseChange` and `TensorProduct.isBaseChange`), and
  applies Mathlib's `Module.FinitePresentation.exists_lift_of_isLocalizedModule`
  to the restriction of `g` along `m ↦ 1 ⊗ m`.
- `exists_smul_eq_of_extendScalars_map_eq_of_isLocalizationMap`: for `M`
  finite over `R`, two morphisms `v w : M ⟶ N` with equal scalar extensions
  satisfy `t • v = t • w` for some `t ∈ T`. This is Mathlib's
  `Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule`, applied to the
  same localized module.
- `exists_extendScalars_map_eq_smul_mul` and
  `exists_extendScalars_map_eq_smul_of_dvd`: if `φ s • g` is an extension of
  scalars, so is `φ (t * s) • g` for every `t`, hence so is `φ s' • g` for
  every multiple `s'` of `s` (multiply the lift by `t`).
- `extendScalars_map_eq_of_smul_eq`: if `φ t` is a unit and `t • v = t • w`,
  then `v` and `w` have equal scalar extensions (apply the functor and cancel
  the unit with `IsUnit.smul_left_cancel`).

## Finite families

- `exists_mem_forall_of_finset`: a family of properties `Q i` of elements of
  `R`, each stable under multiplication by arbitrary elements, holding for
  every element outside a finite set `s` of indices and realized in `T` at
  every index of `s`, is realized by one common element of `T` at all indices.
  The proof is induction on `s`, multiplying the elements together.
- `exists_mem_forall_extendScalars_map_eq_smul`: for a family of morphisms
  `g i` between scalar extensions of finitely presented modules, where for
  `i ∉ s` the source or the target `M i`, `N i` is zero, one common `t ∈ T`
  makes every `φ t • g i` an extension of scalars. Outside `s` the zero
  morphism works because extension of scalars preserves zero objects.
- `exists_mem_forall₂_extendScalars_map_eq_smul`: the same for a doubly
  indexed family `g i j` between two families that are both zero outside `s`,
  obtained from the previous lemma on `s ×ˢ s`.
- `exists_mem_forall_smul_eq_of_extendScalars_map_eq`: finitely many pairs of
  morphisms `v i, w i` from finite modules, with equal scalar extensions and
  with zero source outside `s`, satisfy `t • v i = t • w i` for one common
  `t ∈ T` and all `i`.

## Free modules

`nonempty_extendScalars_pi_equiv`: the scalar extension of the standard free
module `Fin n → R` is linearly equivalent over `A` to `Fin n → A`, by
Mathlib's `TensorProduct.piScalarRight`.
