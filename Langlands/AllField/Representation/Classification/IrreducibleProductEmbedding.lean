import Langlands.Representation.Classification.IrreducibleProductEmbedding
import Langlands.AllField.Representation.Classification.IrreducibleProductEmbeddingStatement
import Langlands.AllField.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
import Langlands.AllField.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.AllField.Representation.CuspidalSupport.CuspidalTensorStatement
import Langlands.AllField.Representation.CuspidalSupport.CuspidalityComparisonProof
import Langlands.AllField.Representation.CuspidalSupport.LeviTensorFactorizationProof
import Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatementSupplement
import Langlands.AllField.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.AllField.Representation.Induction.Equivalences
import Langlands.AllField.Representation.Parabolic.NormalizedInductionStatementSupplement
import Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement
/-! Blockwise cuspidal embeddings and injectivity of normalized products. -/

noncomputable section

namespace Langlands.AllField.FiniteTensor
open Langlands.FiniteTensor
open Langlands.AllField.FiniteTensor

universe uI uG uV uW


end Langlands.AllField.FiniteTensor

namespace Langlands.AllField.Classification
open Langlands.Classification hiding IrreducibleProductEmbeddingTheorem irreducibleProductEmbedding irreducibleProduct_embedding irreducible_supercuspidalProduct_embedding normalizedProduct_embedding_of_factor_embeddings
open Langlands.AllField.Classification

open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllField.Geometric

universe uF uV uW

variable (F : Type uF) [Field F]
  (T : LocalFieldData F)

/-- An irreducible smooth GL representation in an arbitrary carrier universe
embeds in an actual normalized product of small supercuspidal factors. -/
theorem irreducible_supercuspidalProduct_embedding (n : ℕ) (hn : 0 < n)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F))
    (hA : letI := T.topology; A.IsIrreducible) :
    letI := T.topology
    ∃ (B : BlockShape n)
      (C : ∀ i, SupercuspidalRep.{uF, uW} (F := F) (n := B.size i)),
      ∃ j : A.representation.IntertwiningMap
        (T.normalizedProductInduced B (fun i => (C i).obj.representation)),
        Function.Injective j := by
  letI := T.topology
  obtain ⟨_, B, σ, hσ, hcσ, j, hj⟩ :=
    Langlands.AllField.CuspidalSupport.cuspidalEmbedding F T n A hA
  obtain ⟨C, ⟨e⟩⟩ :=
    Langlands.AllField.CuspidalSupport.padicLeviCuspidalFactorization.{uF, uV, uW}
      F T n hn B σ hσ hcσ
  let eInd := T.normalizedParabolicInducedEquiv B e
  exact ⟨B, C, eInd.toIntertwiningMap.comp j, eInd.injective.comp hj⟩

/-- Tensor and then induce a family of actual blockwise injections. -/
theorem normalizedProduct_embedding_of_factor_embeddings
    {n : ℕ} (B : BlockShape n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F))
    (D : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F))
    (j : letI := T.topology
      ∀ i, (A i).representation.IntertwiningMap (D i).representation)
    (hj : ∀ i, Function.Injective (j i)) :
    letI := T.topology
    ∃ J : ((T.normalizedProductInductionFunctor B).obj A).representation.IntertwiningMap
      ((T.normalizedProductInductionFunctor B).obj D).representation,
      Function.Injective J := by
  letI := T.topology
  let jTensor := FiniteTensor.externalMap j
  exact ⟨T.normalizedParabolicInducedMap B jTensor,
    T.normalizedParabolicInducedMap_injective B jTensor
      (FiniteTensor.externalMap_injective j hj)⟩

/-- The original product embeds into the product of blockwise supercuspidal
inductions. This supplies the injection before regrouping and transitivity. -/
theorem irreducibleProduct_embedding
    {n : ℕ} (B : BlockShape n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F))
    (hA : letI := T.topology; ∀ i, (A i).IsIrreducible) :
    letI := T.topology
    ∃ (S : BlockRefinement B)
      (C : ∀ i, ∀ j, SupercuspidalRep.{uF, uV}
        (F := F) (n := (S i).size j)),
      ∃ J : ((T.normalizedProductInductionFunctor B).obj A).representation.IntertwiningMap
        ((T.normalizedProductInductionFunctor B).obj
          (fun i => (T.normalizedProductInductionFunctor (S i)).obj
            (fun j => (C i j).obj))).representation,
        Function.Injective J := by
  classical
  letI := T.topology
  choose S C j hj using fun i =>
    irreducible_supercuspidalProduct_embedding.{uF, uV, uV}
      F T (B.size i) (B.positive i) (A i) (hA i)
  exact ⟨S, C, normalizedProduct_embedding_of_factor_embeddings F T B A
    (fun i => (T.normalizedProductInductionFunctor (S i)).obj (fun k => (C i k).obj))
    j hj⟩

/-- The complete named blockwise embedding proposition. -/
theorem irreducibleProductEmbedding :
    IrreducibleProductEmbeddingTheorem.{uF, uV} F T := by
  intro n B A hA
  exact irreducibleProduct_embedding F T B A hA

end Langlands.AllField.Classification
