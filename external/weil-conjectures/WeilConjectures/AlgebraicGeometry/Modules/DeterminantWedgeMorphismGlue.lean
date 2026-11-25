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
import WeilConjectures.AlgebraicGeometry.Modules.DeterminantLiftWedgeKernel

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option linter.unusedVariables false in
/-- A chosen family of local wedge maps glues to a global morphism.
-/
theorem determinant_wedgeMorphism_glue_family {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁]
    (φU : ∀ U : X.Opens, exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶
      exteriorPower S.X₂ r₂)
    (hformula : ∀ (U : X.Opens)
      (a : Fin r₁ → S.X₁.val.obj (op U))
      (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
      (∀ i, S.g.val.app (op U) (c i) = b i) →
      (φU U).val.app (op U)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
          (wedge (M := S.X₃) (r := r₃) (U := U) b)) =
        wedge (M := S.X₂) (r := r₂) (U := U)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i))) :
    ∃ φ : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶ exteriorPower S.X₂ r₂,
      ∀ (U : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op U))
        (b : Fin r₃ → S.X₃.val.obj (op U)) (c : Fin r₃ → S.X₂.val.obj (op U)),
        (∀ i, S.g.val.app (op U) (c i) = b i) →
        φ.val.app (op U)
          (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
            (wedge (M := S.X₃) (r := r₃) (U := U) b)) =
          wedge (M := S.X₂) (r := r₂) (U := U)
            (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op U) (a j)) c (Fin.cast hr i)) := by
  clear φU hformula
  have : Epi S.g := hS.epi_g
  obtain ⟨q, hqepi, hq⟩ := exteriorTensor_quotient_exists S.X₁ S.X₂ S.X₃ S.g r₁ r₃
  have : Epi q := hqepi
  obtain ⟨w, hwzero, hw⟩ := determinant_liftWedge_kernel_exists S hS r₁ r₂ r₃ hr q hq
  let φ := Abelian.epiDesc q w hwzero
  have hcomp : q ≫ φ = w := Abelian.comp_epiDesc q w hwzero
  refine ⟨φ, ?_⟩
  intro U a b c hc
  have hb : (fun i ↦ S.g.val.app (op U) (c i)) = b := funext hc
  rw [← hb, ← hq U a c]
  have he := congrArg (fun k ↦ k.val.app (op U)
    (tmulSection (wedge (M := S.X₁) (r := r₁) (U := U) a)
      (wedge (M := S.X₂) (r := r₃) (U := U) c))) hcomp
  exact he.trans (hw U a c)

end AlgebraicGeometry.Scheme.Modules
