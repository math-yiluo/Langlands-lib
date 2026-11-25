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
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorQuotient
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorKernelRelations
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt

/-!
# Factorization of the pre-quotient wedge map
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Let `0 → S.X₁ → S.X₂ → S.X₃ → 0` be short exact with `S.X₁` finite locally free of rank
`r₁`. If `q` acts as `𝟙 ⊗ ⋀^{r₃} S.g` on pure wedges and `ψ` sends `a ⊗ c` to `f(a) ∧ c` on pure
wedges, then `ψ` factors through `q`. -/
theorem determinant_wedge_quotient_factor {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ)
    (hr : r₂ = r₁ + r₃) [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (q : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₂ r₃ ⟶
      exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃)
    (ψ : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₂ r₃ ⟶ exteriorPower S.X₂ r₂)
    (hq : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      q.val.app (op U)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₂) (r := r₃) (U := U) c)) =
        tmulSection (M := exteriorPower S.X₁ r₁)
          (N := exteriorPower S.X₃ r₃) (U := U)
          (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₃) (r := r₃) (U := U) (fun i ↦ S.g.val.app (op U) (c i))))
    (hψ : ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
      (c : Fin r₃ → S.X₂.val.obj (op U)),
      ψ.val.app (op U)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₂) (r := r₃) (U := U) c)) =
        wedge (M := S.X₂) (r := r₂) (U := U)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))) :
    ∃ φ : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶ exteriorPower S.X₂ r₂,
      q ≫ φ = ψ := by
  have hgepi : Epi S.g := hS.epi_g
  obtain ⟨q₀, hq₀epi, hq₀⟩ :=
    exteriorTensor_quotient_exists S.X₁ S.X₂ S.X₃ S.g r₁ r₃
  have hqq : q = q₀ := by
    apply exteriorTensor_lift_hom_ext (𝟙 S.X₂) r₁ r₃ q q₀
    intro U a c
    change q.val.app (op U)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₂) (r := r₃) (U := U) c)) =
      q₀.val.app (op U)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₂) (r := r₃) (U := U) c))
    rw [hq U a c, hq₀ U a c]
  have : Epi q := hqq ▸ hq₀epi
  have hzero : CategoryTheory.Limits.kernel.ι q ≫ ψ = 0 := by
    apply exteriorTensor_kernel_eq_zero_of_relations S hS S.X₁
      (exteriorPower S.X₂ r₂) r₁ r₃ q ψ hq
    intro U a c j d hc
    rw [hψ U a c]
    exact exteriorSheaf_rank_wedge_eq_zero S.f r₁ r₂ r₃ hr U a c j d hc
  refine ⟨Abelian.epiDesc q ψ hzero, ?_⟩
  exact Abelian.comp_epiDesc q ψ hzero

end AlgebraicGeometry.Scheme.Modules
