import Langlands.AllFieldBZ.Representation.Classification.IrreducibleProductEmbeddingStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.LeviTensorFactorizationProof
import Langlands.Representation.Classification.IrreducibleProductEmbedding

/-!
# All-field port of `Langlands.Representation.Classification.IrreducibleProductEmbedding`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.IrreducibleProductEmbedding` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.FiniteTensor
open Langlands.FiniteTensor
universe uI uG uV uW

variable {ι : Type uI} {H : ι → Type uG} [∀ i, Group (H i)]
  {V : ι → Type uV} {W : ι → Type uW}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

end Langlands.AllFieldBZ.FiniteTensor
namespace Langlands.AllFieldBZ.Classification
open Langlands.Classification hiding IrreducibleProductEmbeddingTheorem irreducibleProductEmbedding irreducibleProduct_embedding irreducible_supercuspidalProduct_embedding normalizedProduct_embedding_of_factor_embeddings
open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllFieldBZ.Geometric
universe uF uV uW

variable (F : LocalFieldPackage.{uF})
  (T : F.TopologicalData)

/-- An irreducible smooth GL representation in an arbitrary carrier universe
embeds in an actual normalized product of small supercuspidal factors. -/
theorem irreducible_supercuspidalProduct_embedding (n : ℕ) (hn : 0 < n)
    (A : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (hA : letI := T.topology; A.IsIrreducible) :
    letI := T.topology
    ∃ (B : BlockShape n)
      (C : ∀ i, SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := B.size i)),
      ∃ j : A.representation.IntertwiningMap
        (T.normalizedProductInduced B (fun i => (C i).obj.representation)),
        Function.Injective j := by
  letI := T.topology
  obtain ⟨_, B, σ, hσ, hcσ, j, hj⟩ :=
    CuspidalSupport.cuspidalEmbedding F T n A hA
  obtain ⟨C, ⟨e⟩⟩ :=
    CuspidalSupport.padicLeviCuspidalFactorization.{uF, uV, uW}
      F T n hn B σ hσ hcσ
  let eInd := T.normalizedParabolicInducedEquiv B e
  exact ⟨B, C, eInd.toIntertwiningMap.comp j, eInd.injective.comp hj⟩

/-- Tensor and then induce a family of actual blockwise injections. -/
theorem normalizedProduct_embedding_of_factor_embeddings
    {n : ℕ} (B : BlockShape n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (D : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F.Carrier))
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
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hA : letI := T.topology; ∀ i, (A i).IsIrreducible) :
    letI := T.topology
    ∃ (S : BlockRefinement B)
      (C : ∀ i, ∀ j, SupercuspidalRep.{uF, uV}
        (F := F.Carrier) (n := (S i).size j)),
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

end Langlands.AllFieldBZ.Classification
