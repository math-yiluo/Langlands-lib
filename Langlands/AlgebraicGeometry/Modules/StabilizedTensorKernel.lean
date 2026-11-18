import Langlands.AlgebraicGeometry.Modules.StabilizedSectionGenerators

/-! # Surjectivity and actual kernels of stabilized tensor generator maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

open Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {R : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec R) (M : X.Modules)
    {E : Type u} [AddCommGroup E] [Module R E]
    (q : E →ₗ[R] (relativeGlobalSections p).obj M) (C : ModuleCat.{u} R)

/-- The actual stabilized kernel model: the original actual tensor-generator
kernel times zero, transported by the standard tensor/product equivalence. -/
def stabilizedKernelModel (U : X.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    Submodule Γ(X, U) (Γ(X, U) ⊗[R] (E × C)) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
  exact ((globalFamilyTensorMap p M q U).ker.prod
    (⊥ : Submodule Γ(X, U) (Γ(X, U) ⊗[R] C))).comap
      (TensorProduct.prodRight R Γ(X, U) Γ(X, U) E C).toLinearMap

/-- The actual stabilized tensor map is zero exactly when the original
component is zero and the added complement tensor component is zero. -/
theorem stabilizedTensorMap_eq_zero_iff (U : X.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    ∀ z : Γ(X, U) ⊗[R] (E × C),
      stabilizedTensorMap p M q C U z = 0 ↔
        globalFamilyTensorMap p M q U
          ((TensorProduct.prodRight R Γ(X, U) Γ(X, U) E C) z).1 = 0 ∧
        ((TensorProduct.prodRight R Γ(X, U) Γ(X, U) E C) z).2 = 0 := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom p U
  intro z
  rw [← (biprodSectionsEquiv M ((Scheme.Modules.pullback p).obj (tilde C)) U).map_eq_zero_iff,
    stabilizedTensorMap_product, Prod.mk_eq_zero,
    (pullbackTildeSectionsEquiv p C U).map_eq_zero_iff]

/-- Adding the canonical base complement gives precisely the actual modeled
kernel, without any orbit or classified-point input. -/
theorem stabilizedTensorMap_ker (U : X.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    (stabilizedTensorMap p M q C U).ker = stabilizedKernelModel p M q C U := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom p U
  ext z
  change stabilizedTensorMap p M q C U z = 0 ↔ _
  rw [stabilizedTensorMap_eq_zero_iff]
  rfl

/-- A surjective original actual tensor generator map remains surjective
under the genuine canonical base-complement stabilization. -/
theorem stabilizedTensorMap_surjective (U : X.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    Function.Surjective (globalFamilyTensorMap p M q U) →
      Function.Surjective (stabilizedTensorMap p M q C U) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom p U
  intro h s
  let es := biprodSectionsEquiv M ((Scheme.Modules.pullback p).obj (tilde C)) U s
  obtain ⟨x, hx⟩ := h es.1
  let y := (pullbackTildeSectionsEquiv p C U).symm es.2
  refine ⟨(TensorProduct.prodRight R Γ(X, U) Γ(X, U) E C).symm (x, y), ?_⟩
  apply (biprodSectionsEquiv M ((Scheme.Modules.pullback p).obj (tilde C)) U).injective
  rw [stabilizedTensorMap_product, LinearEquiv.apply_symm_apply]
  exact Prod.ext hx ((pullbackTildeSectionsEquiv p C U).apply_symm_apply es.2)

end Langlands.Scheme.Modules
