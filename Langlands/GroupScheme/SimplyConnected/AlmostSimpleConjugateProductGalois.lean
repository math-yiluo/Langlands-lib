import Langlands.GroupScheme.SimplyConnected.AlmostSimpleConjugateProduct
import Mathlib.Data.Finset.NoncommProd

/-! # Canonical Galois transport of the actual conjugate-factor product -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Products

variable {S T : Scheme.{u}} {I : Type u} [Finite I] (A : I → GroupScheme S)

/-- A factor insertion has its original point in that coordinate and the
identity in every other coordinate. -/
theorem piPointsEquiv_piFactorInclusionHom [DecidableEq I] (i : I) (U : Over S)
    (x : U ⟶ (A i).X) :
    piPointsEquiv A U (x ≫ (piFactorInclusionHom A i).hom.hom) =
      Pi.mulSingle (M := fun j => U ⟶ (A j).X) i x := by
  classical
  funext j
  by_cases h : i = j
  · subst j
    simp only [Pi.mulSingle_eq_same]
    exact piFactorInclusionHom_points_self A i x
  · rw [piPointsEquiv_apply, piFactorInclusionHom_points_ne A i j h,
      Pi.mulSingle_eq_of_ne (Ne.symm h)]

/-- Homomorphisms out of a finite product of arbitrary group schemes are
determined by their restrictions to the original factor insertions. -/
theorem pi_hom_ext_of_factorInclusion {H : GroupScheme S} {f g : pi A ⟶ H}
    (h : ∀ i, piFactorInclusionHom A i ≫ f = piFactorInclusionHom A i ≫ g) :
    f = g := by
  classical
  apply hom_ext_points
  intro U x
  let fU := ((pointsMap f).app (Opposite.op U)).hom.comp
    (piPointsEquiv A U).symm.toMonoidHom
  let gU := ((pointsMap g).app (Opposite.op U)).hom.comp
    (piPointsEquiv A U).symm.toMonoidHom
  have hU : fU = gU := by
    apply MonoidHom.pi_ext
    intro i y
    have hy : (piPointsEquiv A U).symm (Pi.mulSingle i y) =
        y ≫ (piFactorInclusionHom A i).hom.hom := by
      apply (piPointsEquiv A U).injective
      rw [MulEquiv.apply_symm_apply, piPointsEquiv_piFactorInclusionHom]
    change (piPointsEquiv A U).symm (Pi.mulSingle i y) ≫ f.hom.hom =
      (piPointsEquiv A U).symm (Pi.mulSingle i y) ≫ g.hom.hom
    rw [hy, Category.assoc, Category.assoc,
      ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, h i]
  have hx := DFunLike.congr_fun hU (piPointsEquiv A U x)
  change (piPointsEquiv A U).symm (piPointsEquiv A U x) ≫ f.hom.hom =
    (piPointsEquiv A U).symm (piPointsEquiv A U x) ≫ g.hom.hom at hx
  simpa only [MulEquiv.symm_apply_apply] using hx

/-- Coordinate isomorphisms retain the original product insertions. -/
@[reassoc] theorem piFactorInclusionHom_mapIso {B : I → GroupScheme S}
    (e : ∀ i, A i ≅ B i) (i : I) :
    piFactorInclusionHom A i ≫ (Pi.mapIso e).hom =
      (e i).hom ≫ piFactorInclusionHom B i := by
  apply Pi.hom_ext
  intro j
  rw [Category.assoc, Pi.mapIso_hom_π e j, ← Category.assoc,
    Category.assoc (e i).hom]
  by_cases h : i = j
  · subst j
    simp only [piFactorInclusionHom_π_self, Category.id_comp, Category.comp_id]
  · rw [piFactorInclusionHom_π_ne A i j h, piFactorInclusionHom_π_ne B i j h]
    apply Grp.hom_ext
    change (1 : _ ⟶ _) ≫ _ = _ ≫ (1 : _ ⟶ _)
    rw [MonObj.one_comp, MonObj.comp_one]

/-- Reindexing retains each original factor insertion. -/
@[reassoc] theorem piFactorInclusionHom_reindex {J : Type u} [Finite J]
    (B : J → GroupScheme S) (ε : I ≃ J) (i : I) :
    piFactorInclusionHom (B ∘ ε) i ≫ (Pi.reindex ε B).hom =
      piFactorInclusionHom B (ε i) := by
  apply Pi.hom_ext
  intro j
  obtain ⟨l, rfl⟩ := ε.surjective j
  rw [Category.assoc, Pi.reindex_hom_π]
  by_cases h : i = l
  · subst l
    rw [piFactorInclusionHom_π_self, piFactorInclusionHom_π_self]
    rfl
  · rw [piFactorInclusionHom_π_ne _ _ _ h,
      piFactorInclusionHom_π_ne _ _ _ (fun he => h (ε.injective he))]
    rfl

/-- A product comparison built from coordinate isomorphisms, reindexing and
an ambient isomorphism retains every factor inclusion. -/
theorem piFactorInclusionHom_comparison {J : Type u} [Finite J]
    (B : J → GroupScheme S) (ε : I ≃ J) (e : ∀ i, A i ≅ B (ε i))
    {G : GroupScheme S} (r : pi B ≅ G) (i : I) :
    piFactorInclusionHom A i ≫ (Pi.mapIso e ≪≫ Pi.reindex ε B ≪≫ r).hom =
      (e i).hom ≫ (piFactorInclusionHom B (ε i) ≫ r.hom) := by
  simp only [Iso.trans_hom, ← Category.assoc]
  rw [piFactorInclusionHom_mapIso]
  have hr : piFactorInclusionHom (fun b => B (ε b)) i ≫ (Pi.reindex ε B).hom =
      piFactorInclusionHom B (ε i) :=
    piFactorInclusionHom_reindex B ε i
  simp only [Category.assoc]
  rw [← Category.assoc (piFactorInclusionHom (fun b => B (ε b)) i), hr]

/-- Pullback preserves the trivial homomorphism even for noncommutative groups. -/
theorem baseChange_trivialHom (b : T ⟶ S) (G H : GroupScheme S) :
    (GroupScheme.baseChange b).map (Grp.homMk
      (CategoryTheory.CartesianMonoidalCategory.toUnit G.X ≫ η[H.X])) =
    Grp.homMk (CategoryTheory.CartesianMonoidalCategory.toUnit
      ((GroupScheme.baseChange b).obj G).X ≫ η[((GroupScheme.baseChange b).obj H).X]) := by
  apply Grp.hom_ext
  exact (Over.pullback b).map_one (X := G.X) (M := H.X)

/-- The product comparison preserves each actual factor insertion. -/
@[reassoc] theorem baseChange_piFactorInclusionHom (b : T ⟶ S) (i : I) :
    (GroupScheme.baseChange b).map (piFactorInclusionHom A i) ≫
        (PreservesProduct.iso (GroupScheme.baseChange b) A).hom =
      piFactorInclusionHom (fun j => (GroupScheme.baseChange b).obj (A j)) i := by
  classical
  apply Pi.hom_ext
  intro j
  rw [Category.assoc, PreservesProduct.iso_hom, piComparison_comp_π,
    ← Functor.map_comp]
  by_cases h : i = j
  · subst j
    simp only [piFactorInclusionHom_π_self]
    exact (GroupScheme.baseChange b).map_id (A i)
  · rw [piFactorInclusionHom_π_ne A i j h, baseChange_trivialHom,
      piFactorInclusionHom_π_ne _ i j h]

/-- Original pulled-back factor insertions determine homomorphisms out of
the actual base change of a finite product. -/
theorem baseChange_pi_hom_ext (b : T ⟶ S) {H : GroupScheme T}
    {f g : (GroupScheme.baseChange b).obj (pi A) ⟶ H}
    (h : ∀ i, (GroupScheme.baseChange b).map (piFactorInclusionHom A i) ≫ f =
      (GroupScheme.baseChange b).map (piFactorInclusionHom A i) ≫ g) :
    f = g := by
  let e := PreservesProduct.iso (GroupScheme.baseChange b) A
  apply (cancel_epi e.inv).mp
  apply pi_hom_ext_of_factorInclusion (fun i => (GroupScheme.baseChange b).obj (A i))
  intro i
  have hi :
      piFactorInclusionHom (fun j => (GroupScheme.baseChange b).obj (A j)) i ≫ e.inv =
        (GroupScheme.baseChange b).map (piFactorInclusionHom A i) := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (baseChange_piFactorInclusionHom A b i).symm
  simpa only [← Category.assoc, hi] using h i

end Products

namespace EmbeddingProduct

variable {k E L : Type u} [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra k L]

/-- The canonical permutation of embeddings induced by an automorphism of
the upper field. -/
def embeddingEquiv (σ : L ≃ₐ[k] L) : (E →ₐ[k] L) ≃ (E →ₐ[k] L) where
  toFun τ := σ.toAlgHom.comp τ
  invFun τ := σ.symm.toAlgHom.comp τ
  left_inv τ := by ext x; exact σ.symm_apply_apply (τ x)
  right_inv τ := by ext x; exact σ.apply_symm_apply (τ x)

/-- Composition on embeddings is contravariant composition on spectra. -/
theorem embedding_baseMap_comp (σ : L ≃ₐ[k] L) (τ : E →ₐ[k] L) :
    galoisBaseMap k L σ ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) =
      Spec.map (CommRingCat.ofHom (σ.toAlgHom.comp τ).toRingHom) := by
  unfold galoisBaseMap
  rw [← Spec.map_comp]
  rfl

variable [Finite (E →ₐ[k] L)] (H : GroupScheme (Spec (CommRingCat.of E)))

/-- Actual scalar extensions of one group scheme along its ground-field
embeddings into the upper field. -/
abbrev family (τ : E →ₐ[k] L) : GroupScheme (Spec (CommRingCat.of L)) :=
  (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom τ.toRingHom))).obj H

/-- The direct and iterated scalar extensions of one original embedding
coordinate are compared along the composed embedding. -/
def coordinateIso (σ : L ≃ₐ[k] L) (τ : E →ₐ[k] L) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).obj (family H τ) ≅
      family H (embeddingEquiv σ τ) :=
  Descent.pullbackComparison
    (Spec.map (CommRingCat.ofHom τ.toRingHom)) (galoisBaseMap k L σ)
    (Spec.map (CommRingCat.ofHom (σ.toAlgHom.comp τ).toRingHom))
    (embedding_baseMap_comp σ τ) H

/-- Canonical Galois transport of the actual embedding product, built from
pullback comparisons and the permutation of embeddings. -/
def galoisIso (σ : L ≃ₐ[k] L) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).obj (pi (family (k := k) (L := L) H)) ≅
      pi (family (k := k) (L := L) H) :=
  PreservesProduct.iso (GroupScheme.baseChange (galoisBaseMap k L σ)) (family H) ≪≫
    Pi.mapIso (coordinateIso H σ) ≪≫
    Pi.reindex (embeddingEquiv σ) (family H)

/-- The original coordinate of canonical transport is its pulled-back
projection followed by the direct/iterated comparison. -/
@[reassoc] theorem galoisIso_hom_π (σ : L ≃ₐ[k] L) (τ : E →ₐ[k] L) :
    (galoisIso H σ).hom ≫ Pi.π (family H) (embeddingEquiv σ τ) =
      (GroupScheme.baseChange (galoisBaseMap k L σ)).map (Pi.π (family H) τ) ≫
        (coordinateIso H σ τ).hom := by
  have hπ :
      (Pi.mapIso (coordinateIso H σ)).hom ≫
          Pi.π (family H ∘ embeddingEquiv σ) τ =
        Pi.π (fun υ => (GroupScheme.baseChange (galoisBaseMap k L σ)).obj
          (family H υ)) τ ≫ (coordinateIso H σ τ).hom :=
    Pi.mapIso_hom_π (coordinateIso H σ) τ
  simp only [galoisIso, Iso.trans_hom, Category.assoc, Pi.reindex_hom_π,
    PreservesProduct.iso_hom]
  rw [hπ, piComparison_comp_π_assoc]

/-- Canonical transport carries each original insertion to the coordinate
indexed by the composed embedding. -/
theorem map_inclusion_galoisIso (σ : L ≃ₐ[k] L) (τ : E →ₐ[k] L) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).map
        (piFactorInclusionHom (family H) τ) ≫ (galoisIso H σ).hom =
      (coordinateIso H σ τ).hom ≫
        piFactorInclusionHom (family H) (embeddingEquiv σ τ) := by
  have hm :
      piFactorInclusionHom
          (fun υ => (GroupScheme.baseChange (galoisBaseMap k L σ)).obj (family H υ)) τ ≫
        (Pi.mapIso (coordinateIso H σ)).hom =
      (coordinateIso H σ τ).hom ≫
        piFactorInclusionHom (family H ∘ embeddingEquiv σ) τ :=
    piFactorInclusionHom_mapIso _ (coordinateIso H σ) τ
  simp only [galoisIso, Iso.trans_hom, ← Category.assoc]
  rw [baseChange_piFactorInclusionHom, hm, Category.assoc,
    piFactorInclusionHom_reindex]

end EmbeddingProduct

namespace SimplyConnectedAlmostSimpleProduct

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    (D : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    [IsGalois k L] [IsAffineHom G.X.hom]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom]

/-- The actual product comparison retains every original embedding inclusion. -/
theorem embeddingConjugateProductIso_inclusion (hG : IsAlmostSimple G) (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    piFactorInclusionHom (D.embeddingConjugateFamily i) τ ≫
        (D.embeddingConjugateProductIso hG i).hom =
      D.embeddingFactorInclusion i τ := by
  calc
    _ = (D.embeddingConjugateFactorIso i τ).hom ≫
        D.inclusion (D.factorIndexOfEmbedding i τ) :=
      piFactorInclusionHom_comparison (D.embeddingConjugateFamily i) D.factor
        (D.factorEmbeddingEquiv hG i) (D.embeddingConjugateFactorIso i) D.iso.symm τ
    _ = D.embeddingFactorInclusion i τ :=
      D.embeddingConjugateFactorIso_hom_inclusion i τ

/-- The canonical descent of the ambient original group carries an embedding
inclusion to the inclusion at the composed embedding. -/
theorem embeddingFactorInclusion_descent (i : D.Index) (σ : L ≃ₐ[k] L)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).map
        (D.embeddingFactorInclusion i τ) ≫
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) G).hom =
      (EmbeddingProduct.coordinateIso (D.factorStabilizerDescent i).1 σ τ).hom ≫
        D.embeddingFactorInclusion i (EmbeddingProduct.embeddingEquiv σ τ) := by
  let E := D.factorStabilizerField i
  let dH := D.factorStabilizerDescent i
  let b := algebraBaseMap k E
  let c := Spec.map (CommRingCat.ofHom τ.toRingHom)
  let a := galoisBaseMap k L σ
  let t := Spec.map (CommRingCat.ofHom
    (EmbeddingProduct.embeddingEquiv σ τ).toRingHom)
  let ht : a ≫ c = t := EmbeddingProduct.embedding_baseMap_comp σ τ
  let e := D.embeddingAmbientIso i τ
  let qH := Descent.pullbackComparison c a t ht dH.1
  let qG := Descent.pullbackComparison c a t ht ((GroupScheme.baseChange b).obj G)
  have hcoh : (GroupScheme.baseChange a).map e.hom ≫
      (descentBaseChangeIso (algebraBaseMap k L) a (galoisBaseMap_over k L σ) G).hom =
      qG.hom ≫ (D.embeddingAmbientIso i (EmbeddingProduct.embeddingEquiv σ τ)).hom :=
    comparison_descent_coherence b c (algebraBaseMap k L) a (galoisBaseMap_over k L σ)
      t ht (D.factorEmbedding_baseMap_over i (EmbeddingProduct.embeddingEquiv σ τ)) G e
      (Descent.pullbackComparison_hom_fst b c (algebraBaseMap k L)
        (D.factorEmbedding_baseMap_over i τ) G)
  change (GroupScheme.baseChange a).map
      ((GroupScheme.baseChange c).map dH.2.1 ≫ e.hom) ≫
        (descentBaseChangeIso (algebraBaseMap k L) a (galoisBaseMap_over k L σ) G).hom =
      qH.hom ≫ D.embeddingFactorInclusion i (EmbeddingProduct.embeddingEquiv σ τ)
  rw [Functor.map_comp, Category.assoc, hcoh, ← Category.assoc _ qG.hom,
    Descent.pullbackComparison_naturality]
  rw [Category.assoc]
  rfl

/-- The actual conjugate-product comparison commutes with the independently
defined canonical Galois transport on the original embedding coordinates. -/
theorem embeddingConjugateProductIso_descent (hG : IsAlmostSimple G) (i : D.Index)
    (σ : L ≃ₐ[k] L) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).map
        (D.embeddingConjugateProductIso hG i).hom ≫
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) G).hom =
      (EmbeddingProduct.galoisIso (D.factorStabilizerDescent i).1 σ).hom ≫
        (D.embeddingConjugateProductIso hG i).hom := by
  apply baseChange_pi_hom_ext (D.embeddingConjugateFamily i) (galoisBaseMap k L σ)
  intro τ
  have ht :
      (GroupScheme.baseChange (galoisBaseMap k L σ)).map
          (piFactorInclusionHom (D.embeddingConjugateFamily i) τ) ≫
        (EmbeddingProduct.galoisIso (D.factorStabilizerDescent i).1 σ).hom =
      (EmbeddingProduct.coordinateIso (D.factorStabilizerDescent i).1 σ τ).hom ≫
        piFactorInclusionHom (D.embeddingConjugateFamily i)
          (EmbeddingProduct.embeddingEquiv σ τ) :=
    EmbeddingProduct.map_inclusion_galoisIso (D.factorStabilizerDescent i).1 σ τ
  rw [← Category.assoc, ← Functor.map_comp,
    D.embeddingConjugateProductIso_inclusion hG i τ, D.embeddingFactorInclusion_descent]
  rw [← Category.assoc _ (EmbeddingProduct.galoisIso
    (D.factorStabilizerDescent i).1 σ).hom, ht, Category.assoc,
    D.embeddingConjugateProductIso_inclusion]

end SimplyConnectedAlmostSimpleProduct

end Langlands.GroupScheme
