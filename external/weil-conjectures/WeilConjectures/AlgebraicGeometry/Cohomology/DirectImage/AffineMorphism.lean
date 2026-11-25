/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-!
# Finiteness and vanishing of coherent cohomology over a field

The cohomology of a coherent sheaf on a proper scheme over a field is finite dimensional, and the
cohomology of a quasi-coherent sheaf on it vanishes in large degrees.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)


section Finiteness

variable {k : Type u} [Field k] [X.Over (Spec (.of k))]

/-- **Finiteness of coherent cohomology.** On a scheme `X` proper over a field `k`, the
cohomology groups `H^q(X, ℱ)` of a coherent `𝒪_X`-module `ℱ` are finite-dimensional over `k`.
Coherence is spelled as quasi-coherence together with finite presentation.

This is the case `T = Spec k` of the finiteness of the higher direct images along a proper
morphism to a Noetherian affine scheme
(`AlgebraicGeometry.Scheme.Modules.finite_sections_higherDirectImage`), transported along the
identification `Γ(Spec k, R^q f_* ℱ) ≅ H^q(X, ℱ)`, which holds for every morphism to the
spectrum of a field (`exists_bijective_semilinearMap_sections_higherDirectImage_H_of_field`).
-/
@[stacks 02O5]
theorem finiteDimensional_H_of_isProper [IsProper (X ↘ Spec (.of k))] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    FiniteDimensional k (ℱ.H q) := by
  classical
  have := isGrothendieckAbelian X
  have : IsNoetherianRing Γ(Spec (.of k), ⊤) :=
    isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H_of_field
    (X ↘ Spec (.of k)) ℱ q
  obtain ⟨s, hs⟩ := (finite_sections_higherDirectImage (X ↘ Spec (.of k)) ℱ q).fg_top
  have key (x) (hx : x ∈ Submodule.span Γ(Spec (.of k), ⊤) (s : Set _)) :
      e x ∈ Submodule.span k (e '' s) := by
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx =>
      obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2 a
      have hc : c • e x = e ((Scheme.ΓSpecIso (.of k)).inv c • x) := by
        rw [smul_H_eq_globalSectionsRingHom_smul, e.map_smulₛₗ]
        rfl
      rw [← hc]
      exact Submodule.smul_mem _ c hx
  refine ⟨⟨s.image e, eq_top_iff.2 fun y _ ↦ ?_⟩⟩
  obtain ⟨x, rfl⟩ := he.2 y
  rw [Finset.coe_image]
  exact key x (hs ▸ Submodule.mem_top)

end Finiteness

end AlgebraicGeometry.Scheme.Modules
