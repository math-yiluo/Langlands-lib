import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorStabilizer
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorTransitivity
import Mathlib.FieldTheory.Normal.Basic

/-! # Embeddings of the stabilizer field index the actual factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

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
    [IsGalois k L]
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom]

/-- Restrict an actual upper-field automorphism to the factor stabilizer field. -/
def factorStabilizerEmbedding (i : D.Index) (σ : L ≃ₐ[k] L) :
    D.factorStabilizerField i →ₐ[k] L :=
  σ.toAlgHom.comp (D.factorStabilizerField i).val

/-- Two automorphisms give the same factor exactly when they give the same
embedding of its stabilizer field. -/
theorem galoisFactorIndex_eq_iff_embeddings_eq (i : D.Index) (σ τ : L ≃ₐ[k] L) :
    D.galoisFactorIndex σ i = D.galoisFactorIndex τ i ↔
      D.factorStabilizerEmbedding i σ = D.factorStabilizerEmbedding i τ := by
  have hact : D.galoisFactorIndex (τ⁻¹ * σ) i = i ↔
      D.galoisFactorIndex σ i = D.galoisFactorIndex τ i := by
    let : MulAction (L ≃ₐ[k] L) D.Index := D.galoisFactorAction
    change (τ⁻¹ * σ) • i = i ↔ σ • i = τ • i
    rw [mul_smul, inv_smul_eq_iff]
  rw [← hact, ← D.fixes_factorStabilizerField_iff]
  constructor
  · intro h
    apply AlgHom.ext
    intro x
    have hx := h x.val x.property
    change τ.symm (σ x.val) = x.val at hx
    exact τ.symm_apply_eq.mp hx
  · intro h x hx
    have hh := DFunLike.congr_fun h (⟨x, hx⟩ : D.factorStabilizerField i)
    change σ x = τ x at hh
    change τ.symm (σ x) = x
    rw [hh, AlgEquiv.symm_apply_apply]

/-- Extend an embedding of the stabilizer field to an automorphism of the
normal upper field. -/
def factorEmbeddingExtension (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) : L ≃ₐ[k] L :=
  AlgEquiv.ofBijective (τ.liftNormal L) (AlgHom.normal_bijective k L L _)

omit [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
  [LocallyOfFinitePresentation G.X.hom] in
@[simp] theorem factorEmbeddingExtension_apply (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) (x : D.factorStabilizerField i) :
    D.factorEmbeddingExtension i τ x.val = τ x := by
  change τ.liftNormal L (algebraMap (D.factorStabilizerField i) L x) = τ x
  simpa only [Algebra.algebraMap_self, RingHom.id_apply] using τ.liftNormal_commutes L x

omit [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
  [LocallyOfFinitePresentation G.X.hom] in
@[simp] theorem factorStabilizerEmbedding_extension (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    D.factorStabilizerEmbedding i (D.factorEmbeddingExtension i τ) = τ := by
  ext x
  exact D.factorEmbeddingExtension_apply i τ x

/-- The actual factor associated to an embedding of the stabilizer field. -/
def factorIndexOfEmbedding (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) : D.Index :=
  D.galoisFactorIndex (D.factorEmbeddingExtension i τ) i

/-- Any extension of the embedding gives exactly this same actual factor. -/
theorem factorIndexOfEmbedding_eq_of_extension (i : D.Index)
    (τ : D.factorStabilizerField i →ₐ[k] L) (σ : L ≃ₐ[k] L)
    (hσ : D.factorStabilizerEmbedding i σ = τ) :
    D.factorIndexOfEmbedding i τ = D.galoisFactorIndex σ i := by
  apply (D.galoisFactorIndex_eq_iff_embeddings_eq i _ σ).mpr
  rw [D.factorStabilizerEmbedding_extension, hσ]

@[simp] theorem factorIndexOfEmbedding_restrict (i : D.Index) (σ : L ≃ₐ[k] L) :
    D.factorIndexOfEmbedding i (D.factorStabilizerEmbedding i σ) =
      D.galoisFactorIndex σ i :=
  D.factorIndexOfEmbedding_eq_of_extension i _ σ rfl

/-- Different stabilizer-field embeddings select different actual factors. -/
theorem factorIndexOfEmbedding_injective (i : D.Index) :
    Function.Injective (D.factorIndexOfEmbedding i) := by
  intro τ υ h
  have he := (D.galoisFactorIndex_eq_iff_embeddings_eq i
    (D.factorEmbeddingExtension i τ) (D.factorEmbeddingExtension i υ)).mp h
  simpa only [D.factorStabilizerEmbedding_extension] using he

/-- Almost-simplicity of the original group makes every factor arise from
one embedding of the selected factor's stabilizer field. -/
theorem factorIndexOfEmbedding_surjective [IsAffineHom G.X.hom]
    (hG : IsAlmostSimple G) (i : D.Index) :
    Function.Surjective (D.factorIndexOfEmbedding i) := by
  intro j
  obtain ⟨σ, hσ⟩ := D.exists_galoisFactorIndex_eq hG i j
  exact ⟨D.factorStabilizerEmbedding i σ, (D.factorIndexOfEmbedding_restrict i σ).trans hσ⟩

/-- Embeddings of the exact stabilizer field index all actual factors. -/
def factorEmbeddingEquiv [IsAffineHom G.X.hom] (hG : IsAlmostSimple G) (i : D.Index) :
    (D.factorStabilizerField i →ₐ[k] L) ≃ D.Index :=
  Equiv.ofBijective (D.factorIndexOfEmbedding i)
    ⟨D.factorIndexOfEmbedding_injective i, D.factorIndexOfEmbedding_surjective hG i⟩

/-- The index correspondence sends an actual restricted automorphism to its
canonical transport of the selected factor. -/
@[simp] theorem factorEmbeddingEquiv_restrict [IsAffineHom G.X.hom]
    (hG : IsAlmostSimple G) (i : D.Index) (σ : L ≃ₐ[k] L) :
    D.factorEmbeddingEquiv hG i (D.factorStabilizerEmbedding i σ) =
      D.galoisFactorIndex σ i :=
  D.factorIndexOfEmbedding_restrict i σ

/-- The original inclusion of the stabilizer field selects the original factor. -/
@[simp] theorem factorIndexOfEmbedding_val (i : D.Index) :
    D.factorIndexOfEmbedding i (D.factorStabilizerField i).val = i := by
  have h := D.factorIndexOfEmbedding_restrict i 1
  change D.factorIndexOfEmbedding i (D.factorStabilizerField i).val =
    D.galoisFactorIndex 1 i at h
  simpa only [D.galoisFactorIndex_one] using h

/-- Composition of embeddings with an upper-field automorphism agrees with
the actual Galois action on factors. -/
theorem factorIndexOfEmbedding_comp (i : D.Index) (σ : L ≃ₐ[k] L)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    D.factorIndexOfEmbedding i (σ.toAlgHom.comp τ) =
      D.galoisFactorIndex σ (D.factorIndexOfEmbedding i τ) := by
  change D.factorIndexOfEmbedding i (σ.toAlgHom.comp τ) =
    D.galoisFactorIndex σ (D.galoisFactorIndex (D.factorEmbeddingExtension i τ) i)
  rw [← D.galoisFactorIndex_mul]
  apply D.factorIndexOfEmbedding_eq_of_extension i _ (σ * D.factorEmbeddingExtension i τ)
  ext x
  change σ (D.factorEmbeddingExtension i τ x.val) = σ (τ x)
  rw [D.factorEmbeddingExtension_apply]

/-- The full embedding-index equivalence respects the canonical Galois action. -/
theorem factorEmbeddingEquiv_comp [IsAffineHom G.X.hom]
    (hG : IsAlmostSimple G) (i : D.Index) (σ : L ≃ₐ[k] L)
    (τ : D.factorStabilizerField i →ₐ[k] L) :
    D.factorEmbeddingEquiv hG i (σ.toAlgHom.comp τ) =
      D.galoisFactorIndex σ (D.factorEmbeddingEquiv hG i τ) :=
  D.factorIndexOfEmbedding_comp i σ τ

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
