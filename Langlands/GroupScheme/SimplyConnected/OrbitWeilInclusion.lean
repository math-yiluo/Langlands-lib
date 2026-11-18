import Langlands.GroupScheme.SimplyConnected.SelectedGeometricWeilFactorCover
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleSubproductGalois
import Langlands.GroupScheme.Descent.ClosedSubgroups

/-! # The actual Weil subgroup associated with a geometric factor orbit -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

namespace Langlands.GroupScheme

section Products

variable {S : Scheme.{u}} {I : Type u} [Finite I] (A : I → GroupScheme S)

/-- A coordinate insertion in a subproduct retains its original insertion
in the full product. -/
@[reassoc] theorem piFactorInclusionHom_subset (s : Set I) (i : s) :
    piFactorInclusionHom (fun j : s => A j.val) i ≫ piSubsetInclusionHom A s =
      piFactorInclusionHom A i.val := by
  classical
  apply Pi.hom_ext
  intro j
  by_cases hj : j ∈ s
  · rw [Category.assoc, piSubsetInclusionHom_π_mem A s ⟨j, hj⟩]
    by_cases hij : i.val = j
    · subst j
      change piFactorInclusionHom (fun j : s => A j.val) i ≫
        Pi.π (fun j : s => A j.val) i = piFactorInclusionHom A i.val ≫ Pi.π A i.val
      rw [piFactorInclusionHom_π_self, piFactorInclusionHom_π_self]
    · rw [piFactorInclusionHom_π_ne _ i ⟨j, hj⟩
        (fun he => hij (congrArg Subtype.val he)), piFactorInclusionHom_π_ne A i.val j hij]
  · have hij : i.val ≠ j := fun he => hj (he ▸ i.property)
    rw [Category.assoc, piFactorInclusionHom_π_ne A i.val j hij]
    simp only [piSubsetInclusionHom, Pi.lift_comp_π, dite_eq_right hj]
    apply Grp.hom_ext
    exact MonObj.comp_one _

end Products

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

/-- The embeddings of the exact stabilizer field index exactly the selected
actual geometric factor orbit, without a ground-field almost-simplicity premise. -/
def factorOrbitEmbeddingEquiv (i : D.Index) :
    (D.factorStabilizerField i →ₐ[k] L) ≃ D.galoisFactorOrbit i :=
  Equiv.ofBijective
    (fun τ => ⟨D.factorIndexOfEmbedding i τ, ⟨D.factorEmbeddingExtension i τ, rfl⟩⟩)
    ⟨fun _ _ h => D.factorIndexOfEmbedding_injective i (congrArg Subtype.val h), by
      rintro ⟨j, σ, hσ⟩
      exact ⟨D.factorStabilizerEmbedding i σ,
        Subtype.ext ((D.factorIndexOfEmbedding_restrict i σ).trans hσ)⟩⟩

/-- The actual embedding-conjugate product is the actual selected orbit
subproduct of the whole geometric group. -/
def embeddingConjugateOrbitIso (i : D.Index) :
    pi (D.embeddingConjugateFamily i) ≅ D.subproduct (D.galoisFactorOrbit i) :=
  Pi.mapIso (D.embeddingConjugateFactorIso i) ≪≫
    Pi.reindex (D.factorOrbitEmbeddingEquiv i)
      (fun j : D.galoisFactorOrbit i => D.factor j.val)

/-- Insert the embedding-conjugate product into the original geometric group
as the whole selected orbit subproduct. -/
def embeddingConjugateOrbitInclusion (i : D.Index) :
    pi (D.embeddingConjugateFamily i) ⟶
      (GroupScheme.baseChange (algebraBaseMap k L)).obj G :=
  (D.embeddingConjugateOrbitIso i).hom ≫ D.subproductInclusion (D.galoisFactorOrbit i)

/-- This inclusion retains every original embedding-coordinate inclusion. -/
@[reassoc] theorem embeddingConjugateOrbitInclusion_inclusion (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    piFactorInclusionHom (D.embeddingConjugateFamily i) τ ≫
      D.embeddingConjugateOrbitInclusion i = D.embeddingFactorInclusion i τ := by
  have he :
      piFactorInclusionHom (D.embeddingConjugateFamily i) τ ≫
          (D.embeddingConjugateOrbitIso i).hom =
        (D.embeddingConjugateFactorIso i τ).hom ≫
          piFactorInclusionHom (fun j : D.galoisFactorOrbit i => D.factor j.val)
            (D.factorOrbitEmbeddingEquiv i τ) := by
    simp only [embeddingConjugateOrbitIso, Iso.trans_hom]
    rw [← Category.assoc, piFactorInclusionHom_mapIso, Category.assoc]
    exact congrArg (fun f => (D.embeddingConjugateFactorIso i τ).hom ≫ f)
      (piFactorInclusionHom_reindex
        (fun j : D.galoisFactorOrbit i => D.factor j.val) (D.factorOrbitEmbeddingEquiv i) τ)
  rw [embeddingConjugateOrbitInclusion, ← Category.assoc, he]
  simp only [subproductInclusion, inclusion, Category.assoc,
    piFactorInclusionHom_subset_assoc]
  exact D.embeddingConjugateFactorIso_hom_inclusion i τ

/-- The orbit inclusion commutes with the full canonical Galois descent
on every embedding coordinate. -/
theorem embeddingConjugateOrbitInclusion_descent (i : D.Index) (σ : L ≃ₐ[k] L) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).map
        (D.embeddingConjugateOrbitInclusion i) ≫
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) G).hom =
      (EmbeddingProduct.galoisIso (D.factorStabilizerDescent i).1 σ).hom ≫
        D.embeddingConjugateOrbitInclusion i := by
  apply baseChange_pi_hom_ext (D.embeddingConjugateFamily i) (galoisBaseMap k L σ)
  intro τ
  have ht := EmbeddingProduct.map_inclusion_galoisIso (D.factorStabilizerDescent i).1 σ τ
  rw [← Category.assoc, ← Functor.map_comp,
    D.embeddingConjugateOrbitInclusion_inclusion, D.embeddingFactorInclusion_descent]
  rw [← Category.assoc _ (EmbeddingProduct.galoisIso
    (D.factorStabilizerDescent i).1 σ).hom, ht, Category.assoc,
    D.embeddingConjugateOrbitInclusion_inclusion]

variable [IsSepClosed L]

attribute [local instance] factorStabilizerDescent_isAffine
  factorStabilizerDescent_locallyOfFiniteType

/-- The actual geometric Weil inclusion is exactly the canonical embedding
comparison followed by insertion of the selected orbit subproduct. -/
def geometricOrbitWeilInclusion (i : D.Index) :
    (GroupScheme.baseChange (algebraBaseMap k L)).obj
        (AffineWeil.groupScheme k (D.factorStabilizerField i) (D.factorStabilizerDescent i).1) ⟶
      (GroupScheme.baseChange (algebraBaseMap k L)).obj G :=
  (D.stabilizerEmbeddingProductIso i).hom ≫ D.embeddingConjugateOrbitInclusion i

/-- The full geometric Weil inclusion has canonical descent to the ground field. -/
theorem geometricOrbitWeilInclusion_descent (i : D.Index) (σ : L ≃ₐ[k] L) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).map
        (D.geometricOrbitWeilInclusion i) ≫
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) G).hom =
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ)
        (AffineWeil.groupScheme k (D.factorStabilizerField i)
          (D.factorStabilizerDescent i).1)).hom ≫ D.geometricOrbitWeilInclusion i := by
  simp only [geometricOrbitWeilInclusion, Functor.map_comp, Category.assoc]
  rw [D.embeddingConjugateOrbitInclusion_descent,
    ← Category.assoc, D.stabilizerEmbeddingProductIso_descent, Category.assoc]

/-- The actual ground-field Weil subgroup associated with the selected geometric
factor, retaining its exact stabilizer field and descended group. -/
def orbitWeilInclusion (i : D.Index) :
    AffineWeil.groupScheme k (D.factorStabilizerField i) (D.factorStabilizerDescent i).1 ⟶ G :=
  Descent.GaloisHom.hom (D.geometricOrbitWeilInclusion i)
    (D.geometricOrbitWeilInclusion_descent i)

/-- Scalar extension recovers the original geometric orbit inclusion exactly. -/
theorem orbitWeilInclusion_baseChange (i : D.Index) :
    (GroupScheme.baseChange (algebraBaseMap k L)).map (D.orbitWeilInclusion i) =
      (D.stabilizerEmbeddingProductIso i).hom ≫ D.embeddingConjugateOrbitInclusion i :=
  Descent.GaloisHom.baseChange_hom _ _

end SimplyConnectedAlmostSimpleProduct
end Langlands.GroupScheme
