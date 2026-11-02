import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation
import Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationStatements

/-! # Invariant affine opens for finite locally free equivalence relations

A proof of `FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenStatement` (Stacks 03JE for
a finite set of points), by the ported Anthropic FLT theorem
`AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Stacks 03JE for a finite set of points: a finite set `E` whose `R`-orbit lies in an affine
open lies in an `R`-invariant affine open. -/
theorem finiteLocallyFreeEquivalenceRelationInvariantAffineOpen :
    FiniteLocallyFreeEquivalenceRelationInvariantAffineOpenStatement.{u} := by
  intro U R t s _ hrefl hsymm htrans _ _ _ _ _ _ E W hE hW hEW
  have hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ U => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y := by
    intro T
    refine ⟨fun x => ?_, fun h => ?_, fun h h' => ?_⟩
    · obtain ⟨r, hrt, hrs⟩ := hrefl T x
      exact ⟨r, hrs, hrt⟩
    · obtain ⟨φ, hφs, hφt⟩ := h
      obtain ⟨r, hrt, hrs⟩ := hsymm T φ
      exact ⟨r, hrs.trans hφt, hrt.trans hφs⟩
    · obtain ⟨φ, hφs, hφt⟩ := h
      obtain ⟨ψ, hψs, hψt⟩ := h'
      obtain ⟨r, hrt, hrs⟩ := htrans T ψ φ (hψs.trans hφt.symm)
      exact ⟨r, hrs.trans hφs, hrt.trans hψt⟩
  obtain ⟨V, hV, hEV, -, hst⟩ :=
    Scheme.exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation
      s t hequiv hE hW (fun x hx r hr => hEW r (hr ▸ hx))
  exact ⟨V, hV, hEV, hst⟩

end Langlands.AlgebraicGeometry
