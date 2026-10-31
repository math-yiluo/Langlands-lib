# `Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation`

## Source

Port of `Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation.lean`
from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `P2M.Sol.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib`
  is unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` is dropped, and its two uses are replaced:
  - `p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry~exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType~exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation NeronModelInfra GoodReductionJacobian"`
    becomes `open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian` followed by
    `open AlgebraicGeometry hiding exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation`
    (`~name` in `p2m_open` hides `name`).
  - The proof `by p2m_exact_reverting @_root_.P2MW.S_….solution` becomes the term
    `P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation.solution f L s`.
    The solution theorem has the same binders and the same conclusion as this theorem.
- The statement is the FLT text.

## Contents

- theorem `GoodReductionJacobian.RelativeGroupLaw.exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation`
  (FLT name). Let `A₀ → A` be a ring map, `f : X ⟶ Spec A₀` quasi-compact, quasi-separated and locally of finite
  presentation, `L` a `RelativeGroupLaw A` on the base change `pullback.snd f (Spec.map (algebraMap A₀ A))`, and
  `s : Finset A`. Then there are:
  - a finitely generated `A₀`-subalgebra `T ⊆ A` containing `s`;
  - a `RelativeGroupLaw T` `Lₜ` on the base change of `f` to `Spec T`;
  - an isomorphism `c` from `pullback f (Spec A ⟶ Spec A₀)` onto the base change along `Spec A ⟶ Spec T` of
    `pullback.snd f (Spec T ⟶ Spec A₀)`.

  `c` commutes with the maps to `Spec A` and to `X`. It carries `L.mul` to the multiplication of
  `Lₜ.baseChange (Spec A ⟶ Spec T)`. If `L` is commutative, so is `Lₜ`.

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange`,
`Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_fg_subalgebra_relativeGroupLaw_pullback_snd_of_locallyOfFinitePresentation`.
