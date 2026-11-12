import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorStabilizerDescent
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorEmbeddings

/-! # Actual conjugate factors and their specified inclusions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

@[reassoc] private theorem conjugate_baseChange_map_fst {S T : Scheme.{u}}
    (b : T ⟶ S) {G H : GroupScheme S} (f : G ⟶ H) :
    ((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.fst H.X.hom b =
      pullback.fst G.X.hom b ≫ f.hom.hom.left := by
  change ((Over.pullback b).map f.hom.hom).left ≫ _ = _
  simp only [Over.pullback_map_left, pullback.lift_fst]

/-- Projection-compatible direct and iterated comparisons commute with
canonical descent and with the corresponding changed intermediate map. -/
theorem comparison_descent_coherence {B C S : Scheme.{u}}
    (b : C ⟶ B) (c : S ⟶ C) (d : S ⟶ B) (a : S ⟶ S)
    (ha : a ≫ d = d) (t : S ⟶ C) (ht : a ≫ c = t) (htb : t ≫ b = d)
    (G : GroupScheme B)
    (e : (GroupScheme.baseChange c).obj ((GroupScheme.baseChange b).obj G) ≅
      (GroupScheme.baseChange d).obj G)
    (he : e.hom.hom.hom.left ≫ pullback.fst G.X.hom d =
      pullback.fst ((GroupScheme.baseChange b).obj G).X.hom c ≫
        pullback.fst G.X.hom b) :
    (GroupScheme.baseChange a).map e.hom ≫ (descentBaseChangeIso d a ha G).hom =
      (Descent.pullbackComparison c a t ht ((GroupScheme.baseChange b).obj G)).hom ≫
        (Descent.pullbackComparison b t d htb G).hom := by
  apply hom_ext_points
  intro T x
  apply (baseChangePointsEquiv d G T).injective
  apply Over.OverMorphism.ext
  simp only [baseChangePointsEquiv_left, Over.comp_left, Grp.comp_hom_hom,
    Category.assoc, descentBaseChangeIso_hom_fst,
    Descent.pullbackComparison_hom_fst]
  change x.left ≫ ((GroupScheme.baseChange a).map e.hom).hom.hom.left ≫
      pullback.fst ((GroupScheme.baseChange d).obj G).X.hom a ≫ pullback.fst G.X.hom d =
    x.left ≫ (Descent.pullbackComparison c a t ht
      ((GroupScheme.baseChange b).obj G)).hom.hom.hom.left ≫
      pullback.fst ((GroupScheme.baseChange b).obj G).X.hom t ≫ pullback.fst G.X.hom b
  rw [conjugate_baseChange_map_fst_assoc, Descent.pullbackComparison_hom_fst_assoc]
  simp only [he]

namespace SimplyConnectedAlmostSimpleProduct

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    (D : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))

/-- The transported actual factor has precisely its selected factor's range. -/
theorem range_galoisFactorInclusion (σ : L ≃ₐ[k] L) (i : D.Index) :
    SubgroupFunctor.range (D.galoisFactorInclusion σ i) =
      SubgroupFunctor.range (D.inclusion (D.galoisFactorIndex σ i)) := by
  rw [D.range_inclusion_galoisFactorIndex]
  exact (SubgroupFunctor.descentTransport_range _ _ _ _ _).symm

/-- The actual transported factor is isomorphic to the factor selected by
its canonical Galois index. -/
def galoisFactorIso (σ : L ≃ₐ[k] L) (i : D.Index) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).obj (D.factor i) ≅
      D.factor (D.galoisFactorIndex σ i) :=
  (D.isClosedSubgroup_galoisFactorInclusion σ i).sourceIsoOfRangeEq
    (D.isClosedSubgroup_inclusion _) (D.range_galoisFactorInclusion σ i)

/-- The source comparison retains the actual transported inclusion. -/
@[reassoc] theorem galoisFactorIso_hom_comp (σ : L ≃ₐ[k] L) (i : D.Index) :
    (D.galoisFactorIso σ i).hom ≫ D.inclusion (D.galoisFactorIndex σ i) =
      D.galoisFactorInclusion σ i :=
  IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp _ _ _

variable [IsGalois k L] [IsAffineHom G.X.hom]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom]

omit [IsAffineHom G.X.hom] [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
  [LocallyOfFinitePresentation G.X.hom] in
/-- The chosen automorphism above an embedding has precisely that embedding's
map on spectra after projection to the stabilizer field. -/
theorem factorEmbeddingExtension_baseMap (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    galoisBaseMap k L (D.factorEmbeddingExtension i τ) ≫
        algebraBaseMap (D.factorStabilizerField i) L =
      Spec.map (CommRingCat.ofHom τ.toRingHom) := by
  unfold galoisBaseMap algebraBaseMap
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact D.factorEmbeddingExtension_apply i τ x

/-- Scalar extension of the actual descended model along an embedding is
isomorphic to the actual factor indexed by that embedding. -/
def embeddingConjugateFactorIso (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj
        (D.factorStabilizerDescent i).1 ≅
      D.factor (D.factorIndexOfEmbedding i τ) :=
  (Descent.pullbackComparison (algebraBaseMap (D.factorStabilizerField i) L)
      (galoisBaseMap k L (D.factorEmbeddingExtension i τ))
      (Spec.map (CommRingCat.ofHom τ.toRingHom))
      (D.factorEmbeddingExtension_baseMap i τ) (D.factorStabilizerDescent i).1).symm ≪≫
    (GroupScheme.baseChange (galoisBaseMap k L (D.factorEmbeddingExtension i τ))).mapIso
      (D.factorStabilizerDescent i).2.2.1 ≪≫
    D.galoisFactorIso (D.factorEmbeddingExtension i τ) i

/-- The conjugate-factor isomorphism recovers the specified transported
inclusion of the original selected factor. -/
@[reassoc] theorem embeddingConjugateFactorIso_hom_comp (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    (D.embeddingConjugateFactorIso i τ).hom ≫
        D.inclusion (D.factorIndexOfEmbedding i τ) =
      (Descent.pullbackComparison (algebraBaseMap (D.factorStabilizerField i) L)
        (galoisBaseMap k L (D.factorEmbeddingExtension i τ))
        (Spec.map (CommRingCat.ofHom τ.toRingHom))
        (D.factorEmbeddingExtension_baseMap i τ) (D.factorStabilizerDescent i).1).inv ≫
      (GroupScheme.baseChange (galoisBaseMap k L (D.factorEmbeddingExtension i τ))).map
        (D.factorStabilizerDescent i).2.2.1.hom ≫
      D.galoisFactorInclusion (D.factorEmbeddingExtension i τ) i := by
  simp only [embeddingConjugateFactorIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, factorIndexOfEmbedding, galoisFactorIso_hom_comp]

omit [IsAffineHom G.X.hom] [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
  [LocallyOfFinitePresentation G.X.hom] [IsGalois k L] in
/-- An embedding over k has its map of spectra over the original base. -/
theorem factorEmbedding_baseMap_over (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
        algebraBaseMap k (D.factorStabilizerField i) = algebraBaseMap k L := by
  unfold algebraBaseMap
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact τ.commutes

/-- The actual ambient comparison for scalar extension along an embedding
of the stabilizer field. -/
def embeddingAmbientIso (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj
        ((GroupScheme.baseChange (algebraBaseMap k (D.factorStabilizerField i))).obj G) ≅
      (GroupScheme.baseChange (algebraBaseMap k L)).obj G :=
  Descent.pullbackComparison (algebraBaseMap k (D.factorStabilizerField i))
    (Spec.map (CommRingCat.ofHom τ.toRingHom)) (algebraBaseMap k L)
    (D.factorEmbedding_baseMap_over i τ) G

/-- Scalar extension of the actual descended inclusion, regarded in the
original upper-field group through the ambient comparison. -/
def embeddingFactorInclusion (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj
        (D.factorStabilizerDescent i).1 ⟶
      (GroupScheme.baseChange (algebraBaseMap k L)).obj G :=
  (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).map
      (D.factorStabilizerDescent i).2.1 ≫ (D.embeddingAmbientIso i τ).hom

/-- The recovery isomorphism retains the original selected inclusion after
the standard tower comparison. -/
theorem factorStabilizerDescent_recovery_comp (i : D.Index) :
    (D.factorStabilizerDescent i).2.2.1.hom ≫ D.inclusion i =
      (GroupScheme.baseChange (algebraBaseMap (D.factorStabilizerField i) L)).map
        (D.factorStabilizerDescent i).2.1 ≫
      (GaloisPointComparison.towerBaseChangeIso k (D.factorStabilizerField i) L G).hom := by
  have h := congrArg (fun f => f ≫
      (GaloisPointComparison.towerBaseChangeIso k (D.factorStabilizerField i) L G).hom)
    (D.factorStabilizerDescent i).2.2.2.2.2
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h.symm

/-- The embedding-conjugate comparison recovers the original descended
inclusion after scalar extension along that embedding. -/
theorem embeddingConjugateFactorIso_hom_inclusion (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    (D.embeddingConjugateFactorIso i τ).hom ≫ D.inclusion (D.factorIndexOfEmbedding i τ) =
      D.embeddingFactorInclusion i τ := by
  let E := D.factorStabilizerField i
  let dH := D.factorStabilizerDescent i
  let σ := D.factorEmbeddingExtension i τ
  let a := galoisBaseMap k L σ
  let b := algebraBaseMap k E
  let c := algebraBaseMap E L
  let t := Spec.map (CommRingCat.ofHom τ.toRingHom)
  let e := GaloisPointComparison.towerBaseChangeIso k E L G
  let qH := Descent.pullbackComparison c a t (D.factorEmbeddingExtension_baseMap i τ) dH.1
  let qG := Descent.pullbackComparison c a t (D.factorEmbeddingExtension_baseMap i τ)
    ((GroupScheme.baseChange b).obj G)
  have hcoh : (GroupScheme.baseChange a).map e.hom ≫
      (descentBaseChangeIso (algebraBaseMap k L) a (galoisBaseMap_over k L σ) G).hom =
      qG.hom ≫ (D.embeddingAmbientIso i τ).hom :=
    comparison_descent_coherence b c (algebraBaseMap k L) a (galoisBaseMap_over k L σ)
      t (D.factorEmbeddingExtension_baseMap i τ) (D.factorEmbedding_baseMap_over i τ) G e
      (GaloisPointComparison.towerBaseChangeIso_hom_fst k E L G)
  rw [D.embeddingConjugateFactorIso_hom_comp]
  change qH.inv ≫ (GroupScheme.baseChange a).map dH.2.2.1.hom ≫
    D.galoisFactorInclusion σ i = _
  calc
    _ = qH.inv ≫ (GroupScheme.baseChange a).map (dH.2.2.1.hom ≫ D.inclusion i) ≫
        (descentBaseChangeIso (algebraBaseMap k L) a (galoisBaseMap_over k L σ) G).hom := by
      simp only [galoisFactorInclusion, Functor.map_comp, Category.assoc]
      rfl
    _ = qH.inv ≫ (GroupScheme.baseChange a).map
        ((GroupScheme.baseChange c).map dH.2.1 ≫ e.hom) ≫
        (descentBaseChangeIso (algebraBaseMap k L) a (galoisBaseMap_over k L σ) G).hom := by
      rw [D.factorStabilizerDescent_recovery_comp]
    _ = qH.inv ≫ (GroupScheme.baseChange a).map
        ((GroupScheme.baseChange c).map dH.2.1) ≫ qG.hom ≫
        (D.embeddingAmbientIso i τ).hom := by
      rw [Functor.map_comp, Category.assoc, hcoh]
    _ = D.embeddingFactorInclusion i τ := by
      rw [← Category.assoc _ qG.hom, Descent.pullbackComparison_naturality]
      simp only [← Category.assoc, qH, Iso.inv_hom_id, Category.id_comp,
        embeddingFactorInclusion]
      rfl

end SimplyConnectedAlmostSimpleProduct

end Langlands.GroupScheme
