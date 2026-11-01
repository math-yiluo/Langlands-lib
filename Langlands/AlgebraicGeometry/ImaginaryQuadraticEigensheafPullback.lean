import Langlands.AlgebraicGeometry.ImaginaryQuadraticEigensheafNaturality
import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackProofs
import Langlands.AlgebraicGeometry.ScalarEigensheafAction

/-! # Pullback of the actual imaginary quadratic eigensheaves -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField Algebra
open Langlands.Shimura.ImaginaryQuadratic
open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w z

namespace Langlands.Scheme.Modules

variable (L : Type u) [Field L] [NumberField L] [IsCMField L]
  (K : Type v) [Field K] [CharZero K] [Algebra L K]
  [IsQuadraticExtension ℚ L]
  {S T : AlgebraicGeometry.Scheme.{w}}
  [Algebra K Γ(S, ⊤)] [Algebra ℚ Γ(S, ⊤)] [IsScalarTower ℚ K Γ(S, ⊤)]
  [Algebra K Γ(T, ⊤)] [Algebra ℚ Γ(T, ⊤)] [IsScalarTower ℚ K Γ(T, ⊤)]
  (b : T ⟶ S) (c : Γ(S, ⊤) →ₐ[K] Γ(T, ⊤)) (hc : c.toRingHom = b.appTop.hom)
  {M : S.Modules} {N : T.Modules}
  (ρ : L →+* End M) (τ : L →+* End N)
  (f : (AlgebraicGeometry.Scheme.Modules.pullback b).obj M ⟶ N)
  (hf : ∀ t : L,
    (AlgebraicGeometry.Scheme.Modules.pullback b).map (ρ t) ≫ f = f ≫ τ t)

omit [IsCMField L] [Algebra L K] [IsQuadraticExtension ℚ L] in
include hc hf in
/-- Tensor-action intertwiners after pullback use the actual pullback of coefficients. -/
theorem sheafTensorAction_pullback (a : Γ(S, ⊤) ⊗[ℚ] L) :
    (AlgebraicGeometry.Scheme.Modules.pullback b).map (sheafTensorAction L M ρ a) ≫ f =
      f ≫ sheafTensorAction L N τ (coefficientMap L K Γ(S, ⊤) Γ(T, ⊤) c a) := by
  induction a using TensorProduct.inductionOn with
  | tmul r t =>
    rw [coefficientMap_tmul, sheafTensorAction_tmul, sheafTensorAction_tmul,
      pullback_map_smul, Linear.smul_comp, Linear.comp_smul, hf t]
    rw [show c r = b.appTop r from congrArg (fun h : Γ(S, ⊤) →+* Γ(T, ⊤) => h r) hc]
  | add a d ha hd =>
    rw [map_add, map_add, map_add]
    change ((AlgebraicGeometry.Scheme.Modules.pullback b).map
      ((sheafTensorAction L M ρ a : M ⟶ M) + sheafTensorAction L M ρ d)) ≫ f = _
    rw [Functor.map_add]
    change ((AlgebraicGeometry.Scheme.Modules.pullback b).map
      (sheafTensorAction L M ρ a) +
      (AlgebraicGeometry.Scheme.Modules.pullback b).map (sheafTensorAction L M ρ d)) ≫ f =
      f ≫ ((sheafTensorAction L N τ (coefficientMap L K Γ(S, ⊤) Γ(T, ⊤) c a) : N ⟶ N) +
        sheafTensorAction L N τ (coefficientMap L K Γ(S, ⊤) Γ(T, ⊤) c d))
    rw [Preadditive.add_comp, Preadditive.comp_add, ha, hd]

include hc hf in
/-- Actual pullback and an ambient intertwiner preserve each complementary projector. -/
theorem sheafProjector_pullback (conjugate : Bool) :
    (AlgebraicGeometry.Scheme.Modules.pullback b).map (sheafProjector L K M ρ conjugate) ≫ f =
      f ≫ sheafProjector L K N τ conjugate := by
  simpa only [sheafProjector, coefficientMap_factorIdempotent] using
    sheafTensorAction_pullback L K b c hc ρ τ f hf
      (factorIdempotent L K Γ(S, ⊤) conjugate)

/-- Restrict a pulled-back ambient map by the actual source inclusion and target projection. -/
def sheafEigenPullbackMap (conjugate : Bool) :
    (AlgebraicGeometry.Scheme.Modules.pullback b).obj
        (scalarEigensheaf ρ (sheafFactorCharacter L K conjugate)) ⟶
      scalarEigensheaf τ (sheafFactorCharacter L K conjugate) :=
  (AlgebraicGeometry.Scheme.Modules.pullback b).map
      (scalarEigensheafι ρ (sheafFactorCharacter L K conjugate)) ≫
    f ≫ sheafEigenProjection L K N τ conjugate

include hc hf in
/-- The constructed eigenmap is the restriction of the supplied ambient map. -/
@[reassoc]
theorem sheafEigenPullbackMap_ι (conjugate : Bool) :
    sheafEigenPullbackMap L K b ρ τ f conjugate ≫
        scalarEigensheafι τ (sheafFactorCharacter L K conjugate) =
      (AlgebraicGeometry.Scheme.Modules.pullback b).map
        (scalarEigensheafι ρ (sheafFactorCharacter L K conjugate)) ≫ f := by
  unfold sheafEigenPullbackMap
  rw [Category.assoc, Category.assoc, sheafEigenProjection_ι,
    ← sheafProjector_pullback L K b c hc ρ τ f hf conjugate,
    ← Category.assoc, ← Functor.map_comp]
  simp only [← sheafEigenProjection_ι, ← Category.assoc, ι_sheafEigenProjection,
    Category.id_comp]

include hc hf in
/-- The actual eigenprojection commutes with the constructed pulled-back eigenmap. -/
@[reassoc]
theorem sheafEigenProjection_pullback (conjugate : Bool) :
    (AlgebraicGeometry.Scheme.Modules.pullback b).map (sheafEigenProjection L K M ρ conjugate) ≫
        sheafEigenPullbackMap L K b ρ τ f conjugate =
      f ≫ sheafEigenProjection L K N τ conjugate := by
  unfold sheafEigenPullbackMap
  rw [← Category.assoc, ← Functor.map_comp, sheafEigenProjection_ι,
    ← Category.assoc, sheafProjector_pullback L K b c hc ρ τ f hf conjugate]
  simp only [← sheafEigenProjection_ι, Category.assoc, ι_sheafEigenProjection,
    Category.comp_id]

include hc hf in
/-- The eigenmap intertwines the restrictions of any commuting ambient algebra actions. -/
theorem sheafEigenPullbackMap_intertwines {A : Type z} [Ring A]
    (σ : A →+* End M) (υ : A →+* End N)
    (hσ : ∀ (r : L) (a : A), ρ r ≫ σ a = σ a ≫ ρ r)
    (hυ : ∀ (r : L) (a : A), τ r ≫ υ a = υ a ≫ τ r)
    (hA : ∀ a : A,
      (AlgebraicGeometry.Scheme.Modules.pullback b).map (σ a) ≫ f = f ≫ υ a)
    (conjugate : Bool) (a : A) :
    (AlgebraicGeometry.Scheme.Modules.pullback b).map
        (scalarEigensheafAction ρ (sheafFactorCharacter L K conjugate) σ hσ a) ≫
        sheafEigenPullbackMap L K b ρ τ f conjugate =
      sheafEigenPullbackMap L K b ρ τ f conjugate ≫
        scalarEigensheafAction τ (sheafFactorCharacter L K conjugate) υ hυ a := by
  apply (cancel_mono (scalarEigensheafι τ (sheafFactorCharacter L K conjugate))).mp
  simp only [Category.assoc, scalarEigensheafAction_ι,
    sheafEigenPullbackMap_ι L K b c hc ρ τ f hf conjugate]
  rw [← Category.assoc, ← Functor.map_comp, scalarEigensheafAction_ι,
    Functor.map_comp, Category.assoc, hA a]
  rw [sheafEigenPullbackMap_ι_assoc L K b c hc ρ τ f hf conjugate]

variable (e : (AlgebraicGeometry.Scheme.Modules.pullback b).obj M ≅ N)
  (he : ∀ t : L,
    (AlgebraicGeometry.Scheme.Modules.pullback b).map (ρ t) ≫ e.hom = e.hom ≫ τ t)

include hc he in
/-- The full natural or conjugate eigensubsheaf commutes with actual scheme pullback.
The inverse uses the ambient inverse and the pulled-back source projection. -/
def sheafEigenPullbackIso (conjugate : Bool) :
    (AlgebraicGeometry.Scheme.Modules.pullback b).obj
        (scalarEigensheaf ρ (sheafFactorCharacter L K conjugate)) ≅
      scalarEigensheaf τ (sheafFactorCharacter L K conjugate) where
  hom := sheafEigenPullbackMap L K b ρ τ e.hom conjugate
  inv := scalarEigensheafι τ (sheafFactorCharacter L K conjugate) ≫
    e.inv ≫ (AlgebraicGeometry.Scheme.Modules.pullback b).map
      (sheafEigenProjection L K M ρ conjugate)
  hom_inv_id := by
    simp only [← Category.assoc]
    rw [sheafEigenPullbackMap_ι L K b c hc ρ τ e.hom he conjugate]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
      ι_sheafEigenProjection]
    exact (AlgebraicGeometry.Scheme.Modules.pullback b).map_id _
  inv_hom_id := by
    simp only [Category.assoc]
    rw [sheafEigenProjection_pullback L K b c hc ρ τ e.hom he conjugate,
      Iso.inv_hom_id_assoc, ι_sheafEigenProjection]

@[simp]
theorem sheafEigenPullbackIso_hom (conjugate : Bool) :
    (sheafEigenPullbackIso L K b c hc ρ τ e he conjugate).hom =
      sheafEigenPullbackMap L K b ρ τ e.hom conjugate := rfl

end Langlands.Scheme.Modules
