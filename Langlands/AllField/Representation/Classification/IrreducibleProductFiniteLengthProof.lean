import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.AllField.Representation.Classification.IrreducibleProductEmbedding
import Langlands.AllField.Representation.Classification.NormalizedProductFiniteLengthStatement
import Langlands.AllField.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof
import Langlands.AllField.Representation.Parabolic.OrderedProductRegroupingProof
/-! Finite length of normalized products of arbitrary irreducible GL factors. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AllField.Classification
open Langlands.Classification hiding AdmissibleFiniteLengthProductPreservation IrreducibleProductEmbeddingTheorem IrreducibleProductFiniteLength irreducibleProductEmbedding irreducibleProductFiniteLength irreducibleProduct_embedding irreducible_supercuspidalProduct_embedding normalizedProduct_embedding_of_factor_embeddings
open Langlands.AllField.Classification

open _root_.CategoryTheory
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicOrbitJacquetComparison PadicParabolicSupportGradedTheorem PadicParabolicSupportJacquetComparison PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar geometricLemma_of_orderedCosets geometricLemma_of_supportGraded geometricPieceFunctor intersectionLeviHalfModulusBalance_sourceLevi intersectionLeviModulusBalance intersectionLeviModulusBalance_sourceLevi jacquetInductionFunctor leviModulus_of_diagonal padicGeometricLemma padicParabolicBruhat padicParabolicOrbitJacquetComparison padicParabolicSupportGradedTheorem padicParabolicSupportJacquetComparison padicStandardIntersectionsTheorem parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor parabolicSupportGradedCompactSmoothIso refinedLeviModulus_of_diagonal supportCoinvariantsImageHom_injective supportCoinvariantsImageIso supportImageNatIso supportImageQuotientHom supportImageQuotientHom_bijective supportImageQuotientIso supportImageToQuotient supportImageToQuotient_ker supportImageToQuotient_on_support supportImageToQuotient_surjective
open Langlands.AllField.Geometric

universe uF uV

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- Flattened supercuspidal factors use the inverse consecutive block numbering. -/
private def flattenSupercuspidalFactors {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (C : letI := T.topology
      ∀ i j, SupercuspidalRep.{uF,uV} (F := F) (n := (S i).size j)) :
    letI := T.topology
    ∀ k, SupercuspidalRep.{uF,uV} (F := F) (n := (B.flatten S).size k) :=
  fun k => C ((B.flattenBlockEquiv S).symm k).1 ((B.flattenBlockEquiv S).symm k).2

/-- Rank transport after flattening returns the original factor. -/
private theorem flattenSupercuspidalFactors_obj {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B)
    (C : letI := T.topology
      ∀ i j, SupercuspidalRep.{uF,uV} (F := F) (n := (S i).size j))
    (q : (i : Fin B.length) × Fin (S i).length) :
    letI := T.topology
    (B.flatten_size_flattenBlockEquiv S q) ▸
      (flattenSupercuspidalFactors F T B S C (B.flattenBlockEquiv S q)).obj =
        (C q.1 q.2).obj := by
  let := T.topology
  have key (a b : (i : Fin B.length) × Fin (S i).length) (h : a = b) :
      (congrArg (fun q => (S q.1).size q.2) h) ▸ (C a.1 a.2).obj =
        (C b.1 b.2).obj := by
    cases h
    rfl
  exact key _ _ ((B.flattenBlockEquiv S).symm_apply_apply q)

/-- Actual normalized product induction of arbitrary irreducible smooth GL
factors has finite group-algebra length. -/
theorem irreducibleProductFiniteLength :
    IrreducibleProductFiniteLength.{uF,uV} F T := by
  let := T.topology
  intro n hn B A hA
  obtain ⟨S, C, J, hJ⟩ := irreducibleProductEmbedding F T n B A hA
  let Cflat := flattenSupercuspidalFactors F T B S C
  let σ := fun k => (Cflat k).obj
  obtain ⟨hirr, hcuspidal⟩ := Langlands.AllField.CuspidalSupport.glCuspidalTensor F T n hn (B.flatten S) Cflat
  have hfinite := (Langlands.AllField.CuspidalSupport.cuspidalInductionLength.{uF,uV} F T n (B.flatten S)
    (FiniteTensor.externalSmoothObject σ) hirr hcuspidal).1
  obtain ⟨ereg⟩ := Langlands.AllField.Parabolic.orderedProductRegrouping.{uF,uV} F T
    n (B.flatten S) B S (B.flattenBlockEquiv S)
    (fun q => (B.flatten_size_flattenBlockEquiv S q).symm)
    (fun i j x => B.index_index_eq_flatten S ⟨i,j⟩ x) σ
  have ereg' : (T.normalizedProductInductionFunctor (B.flatten S)).obj σ ≅
      (T.normalizedProductInductionFunctor B).obj (fun i =>
        (T.normalizedProductInductionFunctor (S i)).obj (fun j => (C i j).obj)) := by
    simpa only [σ, Cflat, flattenSupercuspidalFactors_obj] using ereg
  let E := SmoothRep.equivOfIso ereg'
  let K := E.symm.toIntertwiningMap.comp J
  exact hfinite.of_injective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ K)
    (E.symm.injective.comp hJ)

end Langlands.AllField.Classification
