import Langlands.GroupScheme.SimplyConnected.AlmostSimpleConjugateFactors

/-! # The original upper-field group as the actual embedding-conjugate product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    (D : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    [IsGalois k L] [IsAffineHom G.X.hom]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom]

/-- The actual scalar extensions of the selected stabilizer-field model
along all embeddings of that field into the upper field. -/
abbrev embeddingConjugateFamily (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    GroupScheme (Spec (CommRingCat.of L)) :=
  (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj
    (D.factorStabilizerDescent i).1

/-- The actual product of embedding-conjugate models is the original
upper-field group. -/
def embeddingConjugateProductIso (hG : IsAlmostSimple G) (i : D.Index) :
    pi (D.embeddingConjugateFamily i) ≅
      (GroupScheme.baseChange (algebraBaseMap k L)).obj G :=
  Pi.mapIso (D.embeddingConjugateFactorIso i) ≪≫
    Pi.reindex (D.factorEmbeddingEquiv hG i) D.factor ≪≫ D.iso.symm

/-- Its coordinates are exactly the original factor projections followed
backwards through the conjugate-factor isomorphisms. -/
@[reassoc] theorem embeddingConjugateProductIso_hom_projection
    (hG : IsAlmostSimple G) (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    (D.embeddingConjugateProductIso hG i).hom ≫
        D.projection (D.factorEmbeddingEquiv hG i τ) =
      Pi.π (D.embeddingConjugateFamily i) τ ≫ (D.embeddingConjugateFactorIso i τ).hom := by
  simp only [embeddingConjugateProductIso, Iso.trans_hom, Iso.symm_hom,
    projection, Category.assoc, Iso.inv_hom_id_assoc, Pi.reindex_hom_π]
  exact Pi.mapIso_hom_π (D.embeddingConjugateFactorIso i) τ

/-- Projection from the inverse product comparison recovers the actual
embedding scalar-extension coordinate. -/
@[reassoc] theorem embeddingConjugateProductIso_inv_π
    (hG : IsAlmostSimple G) (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    (D.embeddingConjugateProductIso hG i).inv ≫ Pi.π (D.embeddingConjugateFamily i) τ =
      D.projection (D.factorEmbeddingEquiv hG i τ) ≫
        (D.embeddingConjugateFactorIso i τ).inv := by
  apply (cancel_epi (D.embeddingConjugateProductIso hG i).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc,
    D.embeddingConjugateProductIso_hom_projection]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
