import Langlands.GroupScheme.AffineWeilEmbeddingCoordinateMorphism
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleConjugateProductGalois

/-! # Canonical Galois compatibility of the original Weil-product comparison -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
set_option maxRecDepth 4000

namespace Langlands.GroupScheme.EmbeddingProduct

variable {k E L : Type u} [Field k] [Field E] [Field L]
  [Algebra k E] [Algebra k L] [Finite (E →ₐ[k] L)]
  (W : GroupScheme (Spec (CommRingCat.of k)))
  (H : GroupScheme (Spec (CommRingCat.of E)))
  (e : (GroupScheme.baseChange (algebraBaseMap k E)).obj W ⟶ H)
  (f : (GroupScheme.baseChange (algebraBaseMap k L)).obj W ⟶ pi (family (k := k) (L := L) H))
  (hf : ∀ τ : E →ₐ[k] L,
    f ≫ Pi.π (family H) τ =
      evaluationComponent (algebraBaseMap k E) (algebraBaseMap k L)
        (Spec.map (CommRingCat.ofHom τ.toRingHom))
        (AffineWeil.embeddingBaseMap_over k E L τ) W H e)

include e hf in
/-- Evaluation components on original embeddings imply canonical Galois compatibility. -/
theorem evaluation_product_descent (σ : L ≃ₐ[k] L) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).map f ≫ (galoisIso H σ).hom =
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) W).hom ≫ f := by
  apply Pi.hom_ext
  intro υ
  obtain ⟨τ, rfl⟩ := (embeddingEquiv (E := E) σ).surjective υ
  rw [Category.assoc, galoisIso_hom_π, ← Category.assoc, ← Functor.map_comp, hf,
    Category.assoc (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
      (galoisBaseMap_over k L σ) W).hom, hf]
  exact evaluationComponent_descent (algebraBaseMap k E) (algebraBaseMap k L)
    (Spec.map (CommRingCat.ofHom τ.toRingHom)) (AffineWeil.embeddingBaseMap_over k E L τ)
    W (galoisBaseMap k L σ) (galoisBaseMap_over k L σ)
    (Spec.map (CommRingCat.ofHom (embeddingEquiv σ τ).toRingHom))
    (AffineWeil.embeddingBaseMap_over k E L (embeddingEquiv σ τ))
    (embedding_baseMap_comp σ τ) H e

end Langlands.GroupScheme.EmbeddingProduct

namespace Langlands.GroupScheme.AffineWeil
open Langlands.Algebra.SeparableTensor

variable (k E L : Type u) [Field k] [Field E] [Field L]
  [Algebra k E] [Algebra k L] [FiniteDimensional k E]
  [Finite (E →ₐ[k] L)]
  (hsplit : Function.Bijective (embeddingEvaluation k E L))
  (H : GroupScheme (Spec (CommRingCat.of E)))
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

/-- The original tensor-product Weil comparison respects canonical Galois descent. -/
theorem embeddingProductIsoOfBijective_descent (σ : L ≃ₐ[k] L) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).map
        (embeddingProductIsoOfBijective k E L hsplit H).hom ≫
      (EmbeddingProduct.galoisIso H σ).hom =
    (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
      (galoisBaseMap_over k L σ) (groupScheme k E H)).hom ≫
        (embeddingProductIsoOfBijective k E L hsplit H).hom :=
  EmbeddingProduct.evaluation_product_descent (groupScheme k E H) H (evaluation k E H)
    (embeddingProductIsoOfBijective k E L hsplit H).hom
    (embeddingProductIsoOfBijective_hom_π k E L hsplit H) σ

end Langlands.GroupScheme.AffineWeil
