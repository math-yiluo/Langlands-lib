/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_quotient_of_forall_exists_quotient_restrict
    {X R : Scheme.{u}} (s t : R ⟶ X)
    (W : X → X.Opens) (hxW : ∀ x, x ∈ W x) (hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x)
    (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) :=
  P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.solution s t W hxW hinv loc
