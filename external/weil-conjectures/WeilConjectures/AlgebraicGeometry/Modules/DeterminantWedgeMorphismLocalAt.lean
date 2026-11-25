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
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafMapExists
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- For a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` with `S.X₁` finite locally free of
rank `r₁` and an open `U`, there is a morphism `⋀^{r₁} S.X₁ ⊗ ⋀^{r₃} S.X₃ ⟶ ⋀^{r₂} S.X₂` sending
`(a₁ ∧ ⋯ ∧ a_{r₁}) ⊗ (b₁ ∧ ⋯ ∧ b_{r₃})` over `U` to `f(a₁) ∧ ⋯ ∧ f(a_{r₁}) ∧ c₁ ∧ ⋯ ∧ c_{r₃}`
for any lifts `c` of `b` along `S.g`. -/
theorem determinant_wedgeMorphism_local_data_at {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] (U : X.Opens) :
    ∃ φU : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶
      exteriorPower S.X₂ r₂,
      ∀ (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φU.val.app (op U)
          (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
            (wedge (M := S.X₃) (r := r₃) (U := U) b)) =
          wedge (M := S.X₂) (r := r₂) (U := U)
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  obtain ⟨e, he⟩ := exteriorSheaf_map_exists S.g r₃
  obtain ⟨ψ, hψ⟩ := exteriorSheaf_wedgeMap_exists S.f r₁ r₃ r₂ hr
  let q : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₂ r₃ ⟶
      exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ := 𝟙 _ ⊗ₘ e
  have hq : ∀ (V : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op V))
      (c : Fin r₃ → S.X₂.val.obj (op V)),
      q.val.app (op V)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := V) a)
          (wedge (M := S.X₂) (r := r₃) (U := V) c)) =
        tmulSection (M := exteriorPower S.X₁ r₁)
          (N := exteriorPower S.X₃ r₃) (U := V)
          (wedge (M := S.X₁) (r := r₁) (U := V) a)
          (wedge (M := S.X₃) (r := r₃) (U := V) (fun i ↦ S.g.val.app (op V) (c i))) := by
    intro V a c
    change ((𝟙 _ ⊗ₘ e).app V) _ = _
    rw [tensorHom_app_tmulSection]
    change tmulSection (M := exteriorPower S.X₁ r₁) (N := exteriorPower S.X₃ r₃)
      (U := V) (wedge (M := S.X₁) (r := r₁) (U := V) a)
      (e.val.app (op V) (wedge (M := S.X₂) (r := r₃) (U := V) c)) = _
    exact congrArg (fun z ↦ tmulSection (M := exteriorPower S.X₁ r₁)
      (N := exteriorPower S.X₃ r₃) (U := V) (wedge (M := S.X₁) (r := r₁) (U := V) a) z)
      (he V c)
  obtain ⟨φ, hφ⟩ := determinant_wedge_quotient_factor S hS r₁ r₂ r₃ hr q ψ hq hψ
  refine ⟨φ, ?_⟩
  intro a b c hc
  have hb : (fun i ↦ S.g.val.app (op U) (c i)) = b := funext hc
  have h := congrArg
    (fun k ↦ k.val.app (op U)
      (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
        (wedge (M := S.X₂) (r := r₃) (U := U) c))) hφ
  change φ.val.app (op U) (q.val.app (op U)
      (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
        (wedge (M := S.X₂) (r := r₃) (U := U) c))) =
    ψ.val.app (op U)
      (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
        (wedge (M := S.X₂) (r := r₃) (U := U) c)) at h
  rw [hq U a c, hb, hψ U a c] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
