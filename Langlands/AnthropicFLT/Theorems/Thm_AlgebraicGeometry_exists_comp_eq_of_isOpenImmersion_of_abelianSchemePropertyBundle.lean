/-
Ported from `Theorems/Thm_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle
    {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k))
    [Smooth g] [IsSeparated g] [QuasiCompact g] [IrreducibleSpace X]
    {A : Scheme.{u}} {fA : A ⟶ Spec (CommRingCat.of k)} (hA : AbelianSchemePropertyBundle k fA)
    {U : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u] [Nonempty U]
    (φ : U ⟶ A) (hφ : φ ≫ fA = u ≫ g) :
    ∃ ψ : X ⟶ A, ψ ≫ fA = g ∧ u ≫ ψ = φ :=
  P2MW.S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle.solution g hA u φ hφ
