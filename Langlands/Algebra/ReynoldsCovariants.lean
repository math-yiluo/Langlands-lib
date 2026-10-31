import Mathlib.RingTheory.Noetherian.Basic

/-! # Compatible Reynolds projections and finite covariants -/

noncomputable section
universe u v w
set_option autoImplicit false

namespace Langlands.Algebra

variable (A : Type u) (S : Type v) (M : Type w)
  [CommRing A] [Ring S] [Algebra A S]
  [AddCommGroup M] [Module S M] [Module A M]

/-- A coefficient projection and a retraction onto a submodule, compatible
with multiplying a vector in that submodule by an ambient coefficient. -/
structure ReynoldsPair (W : Submodule A M) where
  coefficient : S →ₗ[A] A
  projection : M →ₗ[A] W
  projection_fixed : ∀ x : W, projection x.val = x
  projection_smul : ∀ (s : S) (x : W),
    projection (s • x.val) = coefficient s • x

namespace ReynoldsPair

variable {A S M} {W : Submodule A M}

/-- In a Noetherian ambient module, compatible Reynolds projections make
the retracted submodule finite over the coefficient ring. -/
theorem moduleFinite [IsNoetherian S M] (P : ReynoldsPair A S M W) :
    Module.Finite A W := by
  classical
  obtain ⟨t, ht, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := S) (W : Set M)).mp
      (IsNoetherian.noetherian _)
  let T : Submodule A M := Submodule.span A (t : Set M)
  have hproj {y : M} (hy : y ∈ Submodule.span S (t : Set M)) :
      (P.projection y).val ∈ T := by
    induction hy using Submodule.closure_induction with
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa only [map_add, Submodule.coe_add] using T.add_mem ihx ihy
    | smul_mem s x hx =>
      have h := P.projection_smul s ⟨x, ht hx⟩
      rw [h]
      exact T.smul_mem (P.coefficient s) (Submodule.subset_span hx)
  have hT : T = W := by
    apply le_antisymm (Submodule.span_le.mpr ht)
    intro x hx
    have hxspan : x ∈ Submodule.span S (t : Set M) := by
      rw [← hspan]
      exact Submodule.subset_span hx
    have h := hproj hxspan
    rw [P.projection_fixed ⟨x, hx⟩] at h
    exact h
  exact Module.Finite.iff_fg.mpr ⟨t, hT⟩

/-- The usual Noetherian-algebra application: a finite ambient module
over a Noetherian coefficient algebra has finite covariants. -/
theorem moduleFinite_of_noetherianRing
    [IsNoetherianRing S] [Module.Finite S M] (P : ReynoldsPair A S M W) :
    Module.Finite A W :=
  P.moduleFinite

end ReynoldsPair
end Langlands.Algebra
