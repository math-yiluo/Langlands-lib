/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified in Langlands-lib, 26 November 2026: FLT module names are prefixed by
`Langlands.AnthropicFLT`; `import Mathlib` is replaced by `import Langlands.MathlibBase`; the
FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof
`by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; the automorphism `ρ γ` is unfolded as `(ρ γ).asIso.hom`, since `Aut X` is a
structure in the Library's Mathlib. The paired Markdown file lists the changes.
-/
import Langlands.MathlibBase
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj
    (B : Type) [CommRing B] (X : Scheme.{0}) [CompactSpace X] (πX : X ⟶ Spec (CommRingCat.of B))
    (hQP : ∃ (qpm : ℕ) (qpι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpm + 1)) B)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpm = πX)
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (hρ : ∀ γ : Γ, (ρ γ).asIso.hom ≫ πX = πX) :
    ∃ (r : ℕ) (U : Fin r → X.Opens) (hinv : ∀ (γ : Γ) (i : Fin r), (ρ γ).asIso.hom ⁻¹ᵁ U i = U i)
      (w : ∀ i j : Fin r, Γ(X, U i)),
      (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ ∧
      (∀ i, w i i = 1) ∧
      (∀ i j k : Fin r,
        X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i k) =
          X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i j) *
            X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (w j k)) ∧
      (∀ i j : Fin r, X.basicOpen (w i j) = U i ⊓ U j) ∧
      (∀ (γ : Γ) (i j : Fin r), (ρ γ).asIso.hom.appLE (U i) (U i) (le_of_eq (hinv γ i).symm) (w i j) = w i j) :=
  P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.solution B X πX hQP Γ ρ hρ
