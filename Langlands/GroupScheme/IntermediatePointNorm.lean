import Langlands.GroupScheme.GaloisPointNorm
import Mathlib.FieldTheory.Galois.Basic

/-! # Norms of group points over intermediate fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.GaloisPoint

variable (F E : Type u) [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E]
  (L : IntermediateField F E) (T : CommGroupScheme (Spec (CommRingCat.of F)))

/-- The product of the images at the embeddings of the intermediate field. -/
def embeddingProduct : Lie.AffinePoints T.toGrp L →* Lie.AffinePoints T.toGrp E where
  toFun x := ∏ i : L →ₐ[F] E, Lie.affineMap T.toGrp i x
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, Finset.prod_mul_distrib]

private def postcomposeEmbedding (σ : E ≃ₐ[F] E) : (L →ₐ[F] E) ≃ (L →ₐ[F] E) where
  toFun i := σ.toAlgHom.comp i
  invFun i := σ.symm.toAlgHom.comp i
  left_inv i := AlgHom.ext fun a => σ.symm_apply_apply (i a)
  right_inv i := AlgHom.ext fun a => σ.apply_symm_apply (i a)

/-- Conjugation permutes the embeddings in the product, so the product is fixed. -/
theorem embeddingProduct_fixed (x : Lie.AffinePoints T.toGrp L) :
    embeddingProduct F E L T x ∈ fixedSubgroup F E T.toGrp := by
  intro σ
  change conjugate F E T.toGrp σ (∏ i : L →ₐ[F] E, Lie.affineMap T.toGrp i x) = _
  rw [map_prod]
  change (∏ i : L →ₐ[F] E,
      Lie.affineMap T.toGrp σ.toAlgHom (Lie.affineMap T.toGrp i x)) = ∏ i, Lie.affineMap T.toGrp i x
  simp only [← Lie.affineMap_comp]
  exact Fintype.prod_equiv (postcomposeEmbedding F E L σ) _ _ (fun _ => rfl)

variable [IsGalois F E] [IsAffine T.X.left]

/-- Descend the product of all conjugate coefficient points to the base field. -/
def intermediateNorm : Lie.AffinePoints T.toGrp L →* Lie.AffinePoints T.toGrp F :=
  (fixedEquiv F E T.toGrp).symm.toMonoidHom.comp
    ((embeddingProduct F E L T).codRestrict _ (embeddingProduct_fixed F E L T))

/-- The descended norm extends to the product indexed by intermediate-field embeddings. -/
theorem extend_intermediateNorm (x : Lie.AffinePoints T.toGrp L) :
    extend F E T.toGrp (intermediateNorm F E L T x) =
      ∏ i : L →ₐ[F] E, Lie.affineMap T.toGrp i x :=
  extend_fixedEquiv_symm F E T.toGrp _

/-- Coefficient change along an embedding of the Galois field evaluates the
norm by the same embeddings followed by the chosen inclusion. -/
theorem map_intermediateNorm {M : Type u} [Field M] [Algebra F M]
    (e : E →ₐ[F] M) (x : Lie.AffinePoints T.toGrp L) :
    extend F M T.toGrp (intermediateNorm F E L T x) =
      ∏ i : L →ₐ[F] E, Lie.affineMap T.toGrp (e.comp i) x := by
  have h := congrArg (Lie.affineMap T.toGrp e) (extend_intermediateNorm F E L T x)
  change Lie.affineMap T.toGrp e (Lie.affineMap T.toGrp (Algebra.ofId F E)
    (intermediateNorm F E L T x)) = _ at h
  rw [← Lie.affineMap_comp, map_prod] at h
  have he : e.comp (Algebra.ofId F E) = Algebra.ofId F M := Subsingleton.elim _ _
  rw [he] at h
  change Lie.affineMap T.toGrp (Algebra.ofId F M) (intermediateNorm F E L T x) = _
  refine h.trans (Finset.prod_congr rfl fun i _ => ?_)
  exact (Lie.affineMap_comp T.toGrp i e x).symm

/-- Over a finite Galois extension the embedding product of an intermediate
point descends, and its extension is computed by the same embeddings. -/
def IntermediatePointNormStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (L : IntermediateField F E) (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left],
    ∀ x : Lie.AffinePoints T.toGrp L, ∃ y : Lie.AffinePoints T.toGrp F,
      ∀ (M : Type u) [Field M] [Algebra F M] (e : E →ₐ[F] M),
        extend F M T.toGrp y = ∏ i : L →ₐ[F] E, Lie.affineMap T.toGrp (e.comp i) x

theorem intermediatePointNorm : IntermediatePointNormStatement.{u} := by
  intro F E _ _ _ _ _ L T _ x
  exact ⟨intermediateNorm F E L T x, fun _ _ _ e => map_intermediateNorm F E L T e x⟩

end Langlands.GroupScheme.GaloisPoint
