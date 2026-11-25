/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Modules.LocalSplittingFiniteFree
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeMorphism
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-!
# Construction of the determinant isomorphism
-/

@[expose] public section

universe v

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Existence, without uniqueness or invertibility assertions, of the determinant
isomorphism with its inverse characterized on wedges and arbitrary quotient lifts. -/
theorem determinant_shortExact_exists {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₂.IsFiniteLocallyFreeOfRank r₂]
    [S.X₃.IsFiniteLocallyFreeOfRank r₃] :
    ∃ e : exteriorPower S.X₂ r₂ ≅ exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        e.inv.val.app (op U)
          (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
            (wedge (M := S.X₃) (r := r₃) (U := U) b)) =
          wedge (M := S.X₂) (r := r₂) (U := U)
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) :=
  by
  obtain ⟨φ, hφ⟩ := determinant_wedgeMorphism_exists S hS r₁ r₂ r₃ hr
  obtain ⟨ι, U, hU, hsplit⟩ := exists_openCover_split_shortExact S hS r₁ r₂ r₃
  have hφiso : IsIso φ := by
    apply Hom.isIso_of_forall_bijective_app
    intro x
    have hx : x ∈ (⨆ i, U i) := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨e, hf, hg⟩ := hsplit i
    exact ⟨U i, hi,
      determinant_wedgeMorphism_bijective_of_split S r₁ r₂ r₃ hr φ hφ (U i) e hf hg⟩
  exact ⟨(asIso φ).symm, hφ⟩

end AlgebraicGeometry.Scheme.Modules
