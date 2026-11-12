import Langlands.GroupScheme.SimplyConnected.AlmostSimpleConjugateProductGalois
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties
import Langlands.GroupScheme.Reductive.SeparablyClosedAlmostSimpleAbsoluteProof
import Langlands.GroupScheme.Descent.GaloisHom
import Langlands.GroupScheme.AffineWeilRestriction

/-! # Descent of a compatible actual Weil-product comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000

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

/-- Over a separably closed upper field, the actual stabilizer-field factor
is absolutely almost-simple. -/
theorem isAbsolutelyAlmostSimple_factorStabilizerDescent_of_isSepClosed
    [IsSepClosed L] (i : D.Index) :
    IsAbsolutelyAlmostSimple (D.factorStabilizerDescent i).1 :=
  D.isAbsolutelyAlmostSimple_factorStabilizerDescent i
    (separablyClosedAlmostSimpleAbsolute L (D.factor i) (D.isAlmostSimple i))

local instance factorStabilizerDescent_isAffine (i : D.Index) :
    IsAffine (D.factorStabilizerDescent i).1.X.left :=
  (D.factorStabilizerDescent i).2.2.2.1

local instance factorStabilizerDescent_locallyOfFiniteType (i : D.Index) :
    LocallyOfFiniteType (D.factorStabilizerDescent i).1.X.hom := by
  let : Smooth (D.factorStabilizerDescent i).1.X.hom :=
    (D.isSimplyConnected_factorStabilizerDescent i).isSemisimple.isConnectedReductive.smooth
  infer_instance

variable (hG : IsAlmostSimple G) (i : D.Index)
    (p : (GroupScheme.baseChange (algebraBaseMap k L)).obj
        (AffineWeil.groupScheme k (D.factorStabilizerField i)
          (D.factorStabilizerDescent i).1) ≅ pi (D.embeddingConjugateFamily i))
    (hp : ∀ σ : L ≃ₐ[k] L,
      (GroupScheme.baseChange (galoisBaseMap k L σ)).map p.hom ≫
          (EmbeddingProduct.galoisIso (D.factorStabilizerDescent i).1 σ).hom =
        (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ)
          (AffineWeil.groupScheme k (D.factorStabilizerField i)
            (D.factorStabilizerDescent i).1)).hom ≫ p.hom)

/-- Compose a supplied canonically compatible actual Weil-product comparison
with the actual conjugate-factor product and descend the resulting isomorphism. -/
def weilRestrictionIsoOfCompatibleEmbeddingProduct :
    G ≅ AffineWeil.groupScheme k (D.factorStabilizerField i)
      (D.factorStabilizerDescent i).1 := by
  let f := p ≪≫ D.embeddingConjugateProductIso hG i
  have hf : ∀ σ : L ≃ₐ[k] L,
      (GroupScheme.baseChange (galoisBaseMap k L σ)).map f.hom ≫
          (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
            (galoisBaseMap_over k L σ) G).hom =
        (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
          (galoisBaseMap_over k L σ)
          (AffineWeil.groupScheme k (D.factorStabilizerField i)
            (D.factorStabilizerDescent i).1)).hom ≫ f.hom := by
    intro σ
    simp only [f, Iso.trans_hom, Functor.map_comp, Category.assoc]
    rw [D.embeddingConjugateProductIso_descent hG i σ,
      ← Category.assoc, hp σ, Category.assoc]
  exact (Descent.GaloisHom.iso f.hom hf).symm

/-- The descended comparison recovers exactly the supplied Weil comparison
followed by the original conjugate-product comparison. -/
theorem weilRestrictionIsoOfCompatibleEmbeddingProduct_baseChange_inv :
    (GroupScheme.baseChange (algebraBaseMap k L)).map
        (D.weilRestrictionIsoOfCompatibleEmbeddingProduct hG i p hp).inv =
      p.hom ≫ (D.embeddingConjugateProductIso hG i).hom := by
  unfold weilRestrictionIsoOfCompatibleEmbeddingProduct
  apply Descent.GaloisHom.baseChange_iso_hom
  intro σ
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
  rw [D.embeddingConjugateProductIso_descent hG i σ,
    ← Category.assoc, hp σ, Category.assoc]

include D hG i p hp

/-- With a separably closed upper field, a supplied compatible actual
Weil-product comparison gives every witness in the structural conclusion. -/
theorem exists_weilRestriction_of_compatibleEmbeddingProduct [IsSepClosed L] :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E)
      (_ : FiniteDimensional k E) (_ : Algebra.IsSeparable k E)
      (H : GroupScheme (Spec (CommRingCat.of E)))
      (_ : IsAffine H.X.left) (_ : LocallyOfFiniteType H.X.hom),
      IsSimplyConnected H ∧ IsAbsolutelyAlmostSimple H ∧
        Nonempty (G ≅ AffineWeil.groupScheme k E H) := by
  refine ⟨D.factorStabilizerField i, inferInstance, inferInstance,
    inferInstance, inferInstance, (D.factorStabilizerDescent i).1,
    inferInstance, inferInstance, D.isSimplyConnected_factorStabilizerDescent i,
    D.isAbsolutelyAlmostSimple_factorStabilizerDescent_of_isSepClosed i, ?_⟩
  exact ⟨D.weilRestrictionIsoOfCompatibleEmbeddingProduct hG i p hp⟩

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
