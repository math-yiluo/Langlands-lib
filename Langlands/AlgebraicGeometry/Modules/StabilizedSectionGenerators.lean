import Langlands.AlgebraicGeometry.Modules.PullbackTildeSections
import Langlands.AlgebraicGeometry.Picard.DeterminantBiproduct
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Actual stabilized global generators and affine tensor maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

open Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {R : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec R) (M : X.Modules)
    {E : Type u} [AddCommGroup E] [Module R E]
    (q : E →ₗ[R] (relativeGlobalSections p).obj M)

/-- The restricted actual global family as an R-linear section map, with the
canonical R-action through the actual open section ring. -/
def globalFamilyRestriction (U : X.Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    letI : Module R Γ(M, U) := Module.compHom _ (algebraMap R Γ(X, U))
    E →ₗ[R] Γ(M, U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
  letI : Module R Γ(M, U) := Module.compHom _ (algebraMap R Γ(X, U))
  refine
    { toFun := fun e => M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (q e)
      map_add' := fun e e' => by simp only [map_add]
      map_smul' := ?_ }
  intro r e
  rw [q.map_smul]
  change M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (p.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) •
        (show Γ(M, ⊤) from q e)) =
    (algebraMap R Γ(X, U) r) •
      M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (q e)
  rw [Scheme.Modules.map_smul]
  congr 1

/-- Extend the restricted actual global family to the actual coefficient tensor. -/
def globalFamilyTensorMap (U : X.Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    Γ(X, U) ⊗[R] E →ₗ[Γ(X, U)] Γ(M, U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
  letI : Module R Γ(M, U) := Module.compHom _ (algebraMap R Γ(X, U))
  letI : IsScalarTower R Γ(X, U) Γ(M, U) :=
    ⟨fun r a s => by
      change (algebraMap R Γ(X, U) r * a) • s =
        (algebraMap R Γ(X, U) r) • (a • s)
      exact mul_smul _ _ _⟩
  exact (globalFamilyRestriction p M q U).liftBaseChange Γ(X, U)

@[simp]
theorem globalFamilyTensorMap_tmul (U : X.Opens) (a : Γ(X, U)) (e : E) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    globalFamilyTensorMap p M q U (a ⊗ₜ[R] e) =
      a • M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (q e) := rfl

/-- The coefficient tensor map induced by any actual global R-linear family
commutes with restriction to a smaller open. -/
theorem globalFamilyTensorMap_restrict {U V : X.Opens} (h : V ≤ U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p V
    ∀ z : Γ(X, U) ⊗[R] E,
      M.presheaf.map (homOfLE h).op (globalFamilyTensorMap p M q U z) =
        globalFamilyTensorMap p M q V
          (TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom p h).toLinearMap
            (LinearMap.id : E →ₗ[R] E) z) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom p U
  let := Scheme.TwoAffineOpenCover.algebraOfHom p V
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e =>
    rw [TensorProduct.map_tmul, globalFamilyTensorMap_tmul,
      globalFamilyTensorMap_tmul, Scheme.Modules.map_smul]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

variable (C : ModuleCat.{u} R)

/-- The actual R-linear global generator in the genuine stabilized biproduct. -/
def stabilizedGlobalGenerator :
    E × C →ₗ[R] (relativeGlobalSections p).obj
      (M ⊞ (Scheme.Modules.pullback p).obj (tilde C)) :=
  ((relativeGlobalSections p).map
      (biprod.inl : M ⟶ M ⊞ (Scheme.Modules.pullback p).obj (tilde C))).hom.comp
        (q.comp (LinearMap.fst R E C)) +
    ((relativeGlobalSections p).map
      (biprod.inr : (Scheme.Modules.pullback p).obj (tilde C) ⟶
        M ⊞ (Scheme.Modules.pullback p).obj (tilde C))).hom.comp
          ((pullbackTildeGlobalSections p C).hom.comp (LinearMap.snd R E C))

/-- The actual projections recover the two prescribed actual global families. -/
theorem stabilizedGlobalGenerator_product (z : E × C) :
    biprodSectionsEquiv M ((Scheme.Modules.pullback p).obj (tilde C)) ⊤
      (stabilizedGlobalGenerator p M q C z) =
        (q z.1, pullbackTildeGlobalSections p C z.2) := by
  apply Prod.ext
  · change (biprod.fst : M ⊞ (Scheme.Modules.pullback p).obj (tilde C) ⟶ M).app ⊤
      ((biprod.inl : M ⟶ M ⊞ (Scheme.Modules.pullback p).obj (tilde C)).app ⊤ (q z.1) +
        (biprod.inr : (Scheme.Modules.pullback p).obj (tilde C) ⟶
          M ⊞ (Scheme.Modules.pullback p).obj (tilde C)).app ⊤
            (pullbackTildeGlobalSections p C z.2)) = _
    rw [map_add]
    change ((biprod.inl ≫ biprod.fst : M ⟶ M).app ⊤) (q z.1) +
      ((biprod.inr ≫ biprod.fst : (Scheme.Modules.pullback p).obj (tilde C) ⟶ M).app ⊤) (pullbackTildeGlobalSections p C z.2) = _
    simp
  · change (biprod.snd : M ⊞ (Scheme.Modules.pullback p).obj (tilde C) ⟶ _).app ⊤
      ((biprod.inl : M ⟶ M ⊞ (Scheme.Modules.pullback p).obj (tilde C)).app ⊤ (q z.1) +
        (biprod.inr : (Scheme.Modules.pullback p).obj (tilde C) ⟶
          M ⊞ (Scheme.Modules.pullback p).obj (tilde C)).app ⊤
            (pullbackTildeGlobalSections p C z.2)) = _
    rw [map_add]
    change ((biprod.inl ≫ biprod.snd : M ⟶ (Scheme.Modules.pullback p).obj (tilde C)).app ⊤) (q z.1) +
      ((biprod.inr ≫ biprod.snd : (Scheme.Modules.pullback p).obj (tilde C) ⟶
        (Scheme.Modules.pullback p).obj (tilde C)).app ⊤) (pullbackTildeGlobalSections p C z.2) = _
    simp

/-- The canonical affine coefficient tensor map for the actual stabilized family. -/
def stabilizedTensorMap (U : X.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    Γ(X, U) ⊗[R] (E × C) →ₗ[Γ(X, U)]
      Γ(M ⊞ (Scheme.Modules.pullback p).obj (tilde C), U) :=
  globalFamilyTensorMap p _ (stabilizedGlobalGenerator p M q C) U

@[simp]
theorem stabilizedTensorMap_tmul (U : X.affineOpens) (a : Γ(X, U)) (z : E × C) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    stabilizedTensorMap p M q C U (a ⊗ₜ[R] z) =
      a • (M ⊞ (Scheme.Modules.pullback p).obj (tilde C)).presheaf.map
        (homOfLE (show (U : X.Opens) ≤ ⊤ from le_top)).op
          (stabilizedGlobalGenerator p M q C z) := rfl

/-- The actual stabilized tensor map is the product of the original family
tensor map and the canonical complement equivalence, under actual biproduct sections. -/
theorem stabilizedTensorMap_product (U : X.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    ∀ z : Γ(X, U) ⊗[R] (E × C),
      biprodSectionsEquiv M ((Scheme.Modules.pullback p).obj (tilde C)) U
        (stabilizedTensorMap p M q C U z) =
      (globalFamilyTensorMap p M q U ((TensorProduct.prodRight R Γ(X, U) Γ(X, U) E C) z).1,
        pullbackTildeSectionsEquiv p C U ((TensorProduct.prodRight R Γ(X, U) Γ(X, U) E C) z).2) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom p U
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, Prod.fst_add, Prod.snd_add, hx, hy]
    rfl
  | tmul a z =>
    rw [stabilizedTensorMap_tmul, map_smul, biprodSectionsEquiv_restrict,
      stabilizedGlobalGenerator_product, TensorProduct.prodRight_tmul,
      globalFamilyTensorMap_tmul, pullbackTildeSectionsEquiv_tmul]
    rfl

/-- The genuine stabilized tensor map also retains the actual global-family
restriction compatibility for every coefficient tensor. -/
theorem stabilizedTensorMap_restrict {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p V
    ∀ z : Γ(X, U) ⊗[R] (E × C),
      (M ⊞ (Scheme.Modules.pullback p).obj (tilde C)).presheaf.map (homOfLE h).op
        (stabilizedTensorMap p M q C U z) =
      stabilizedTensorMap p M q C V
        (TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom p h).toLinearMap
          (LinearMap.id : E × C →ₗ[R] E × C) z) :=
  globalFamilyTensorMap_restrict p _ (stabilizedGlobalGenerator p M q C) h

end Langlands.Scheme.Modules

