import Langlands.GroupScheme.Torus.WeilRestrictionEmbeddings

/-! # Embedding coordinates for tensor-valued affine points -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.AffineWeil

open Langlands.Algebra.SeparableTensor

variable (F k Ω : Type u) [CommRing F] [CommRing k] [CommRing Ω]
  [Algebra F k] [Algebra F Ω] [Finite (k →ₐ[F] Ω)]
  (hsplit : Function.Bijective (embeddingEvaluation F k Ω))
  (R : Type u) [CommRing R] [Algebra Ω R] [Algebra F R] [IsScalarTower F Ω R]

/-- Canonical embedding coordinates for the original tensor coefficient ring. -/
def tensorEmbeddingEquiv : k ⊗[F] R ≃+* ((k →ₐ[F] Ω) → R) :=
  WeilGm.decompositionTensorEquiv F Ω k R (k →ₐ[F] Ω)
    (WeilGm.embeddingDecomposition F k Ω hsplit)

@[simp] theorem tensorEmbeddingEquiv_tmul (b : k) (r : R) (τ : k →ₐ[F] Ω) :
    tensorEmbeddingEquiv F k Ω hsplit R (b ⊗ₜ[F] r) τ =
      algebraMap Ω R (τ b) * r := by
  simp [tensorEmbeddingEquiv, Algebra.smul_def]

/-- Evaluation of the original coefficient tensor at a specified embedding. -/
def tensorEmbeddingEvaluation (τ : k →ₐ[F] Ω) : k ⊗[F] R →+* R :=
  (Pi.evalRingHom _ τ).comp (tensorEmbeddingEquiv F k Ω hsplit R).toRingHom

@[simp] theorem tensorEmbeddingEvaluation_tmul (τ : k →ₐ[F] Ω) (b : k) (r : R) :
    tensorEmbeddingEvaluation F k Ω hsplit R τ (b ⊗ₜ[F] r) =
      algebraMap Ω R (τ b) * r :=
  tensorEmbeddingEquiv_tmul F k Ω hsplit R b r τ

variable (D : Type u) [CommRing D] [Algebra k D]

/-- A family of ring-valued points whose scalar action in coordinate `τ` is the
original `k`-action followed by `τ` and the specified coefficient inclusion. -/
def EmbeddingPointFamily :=
  ∀ τ : k →ₐ[F] Ω, { f : D →+* R //
    ∀ b : k, f (algebraMap k D b) = algebraMap Ω R (τ b) }

/-- Tensor-valued algebra points are exactly the families with the conjugate scalar actions. -/
def tensorPointEmbeddingEquiv :
    (D →ₐ[k] k ⊗[F] R) ≃ EmbeddingPointFamily F k Ω R D where
  toFun f τ := ⟨(tensorEmbeddingEvaluation F k Ω hsplit R τ).comp f.toRingHom, by
    intro b
    change tensorEmbeddingEvaluation F k Ω hsplit R τ (f (algebraMap k D b)) = _
    rw [f.commutes]
    change tensorEmbeddingEvaluation F k Ω hsplit R τ (b ⊗ₜ[F] 1) = _
    simp⟩
  invFun p := {
    toRingHom := (tensorEmbeddingEquiv F k Ω hsplit R).symm.toRingHom.comp
      (RingHom.pi fun τ => (p τ).1)
    commutes' b := by
      apply (tensorEmbeddingEquiv F k Ω hsplit R).injective
      funext τ
      change tensorEmbeddingEquiv F k Ω hsplit R
          ((tensorEmbeddingEquiv F k Ω hsplit R).symm _) τ =
        tensorEmbeddingEquiv F k Ω hsplit R (b ⊗ₜ[F] 1) τ
      rw [RingEquiv.apply_symm_apply]
      simpa only [RingHom.pi_apply, tensorEmbeddingEquiv_tmul, mul_one] using
        (p τ).2 b }
  left_inv f := by
    ext d
    apply (tensorEmbeddingEquiv F k Ω hsplit R).injective
    funext τ
    change tensorEmbeddingEquiv F k Ω hsplit R
        ((tensorEmbeddingEquiv F k Ω hsplit R).symm _) τ = _
    rw [RingEquiv.apply_symm_apply]
    rfl
  right_inv p := by
    funext τ
    apply Subtype.ext
    ext d
    change tensorEmbeddingEquiv F k Ω hsplit R
        ((tensorEmbeddingEquiv F k Ω hsplit R).symm _) τ = _
    rw [RingEquiv.apply_symm_apply]
    rfl

@[simp] theorem tensorPointEmbeddingEquiv_apply (f : D →ₐ[k] k ⊗[F] R)
    (τ : k →ₐ[F] Ω) (d : D) :
    (tensorPointEmbeddingEquiv F k Ω hsplit R D f τ).1 d =
      tensorEmbeddingEvaluation F k Ω hsplit R τ (f d) := rfl

variable {R D} {R' : Type u} [CommRing R'] [Algebra Ω R'] [Algebra F R']
  [IsScalarTower F Ω R']

/-- Embedding evaluation commutes with every coefficient-algebra map. -/
theorem tensorEmbeddingEvaluation_naturality (a : R →ₐ[Ω] R') (τ : k →ₐ[F] Ω)
    (x : k ⊗[F] R) :
    tensorEmbeddingEvaluation F k Ω hsplit R' τ
        (Algebra.TensorProduct.lTensor (S := k) k (a.restrictScalars F) x) =
      a (tensorEmbeddingEvaluation F k Ω hsplit R τ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b r => simp [a.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Changing the coefficient ring preserves the specified conjugate scalar action. -/
def mapEmbeddingPointFamily (a : R →ₐ[Ω] R')
    (p : EmbeddingPointFamily F k Ω R D) : EmbeddingPointFamily F k Ω R' D :=
  fun τ => ⟨a.toRingHom.comp (p τ).1, by
    intro b
    rw [RingHom.comp_apply, (p τ).2]
    exact a.commutes _⟩

/-- The point decomposition is natural for arbitrary maps of coefficient algebras. -/
theorem tensorPointEmbeddingEquiv_naturality (a : R →ₐ[Ω] R')
    (f : D →ₐ[k] k ⊗[F] R) :
    tensorPointEmbeddingEquiv F k Ω hsplit R' D
        ((Algebra.TensorProduct.lTensor (S := k) k (a.restrictScalars F)).comp f) =
      mapEmbeddingPointFamily F k Ω a (tensorPointEmbeddingEquiv F k Ω hsplit R D f) := by
  funext τ
  apply Subtype.ext
  ext d
  exact tensorEmbeddingEvaluation_naturality F k Ω hsplit a τ (f d)

end Langlands.GroupScheme.AffineWeil
