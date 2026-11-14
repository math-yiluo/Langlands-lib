import Langlands.AllFieldBZ.Group.GL.AdjacentMergeShape
import Langlands.AllFieldBZ.Representation.CuspidalSupport.AdjacentSwapStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.LeviTensorFactorizationProof
import Langlands.Representation.CuspidalSupport.AdjacentTensorReduction

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.AdjacentTensorReduction`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.AdjacentTensorReduction` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AdjacentBlockSwapCuspidalInductionFactorsTheorem AssociatedCuspidalInductionFactorsTheorem AssociatedCuspidalInductionHomTheorem AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem CanonicalAdjacentSupercuspidalProductMatchingStatement CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem PadicLeviAdmissibleFactorizationStatement PadicLeviCuspidalFactorizationStatement PadicLeviTensorSupercuspidalReflectionStatement TotalConjugatingCountTheorem TwoBlockAssociatedCuspidalInductionFactorsTheorem adjacentBlockSwap_of_canonicalProducts associatedCuspidalInductionFactors_of_adjacent associatedCuspidalInductionFactors_of_length_lt_two associatedGeometricPieceEquivalence canonicalCuspidalTensorData cuspidalDatum_eq_of_equiv factors_of_blockMap factors_step fullRefinedInductionEquiv fullRefinedJacquetEquiv glCuspidalTensorAssociation isIrreducible_normalizedParabolicInduced_singleBlock padicLeviAdmissibleFactorization padicLeviCuspidalFactorization padicLeviTensorSupercuspidalReflection refinedHalfModulus_eq_one_of_full refinedInverseHalfModulus_eq_one_of_full refinedModulus_eq_one_of_full totalConjugatingCount
open Langlands.GeneralLinear
universe uF uV uW uA

/-- Factor the source cuspidal data and identify the target with the tensor in
the prescribed canonical order, in an independently prescribed universe. -/
def canonicalCuspidalTensorData
    (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (e : Equiv.Perm (Fin B.length))
    (hw : ConjugatesLevi (F := F.Carrier) B (B.permute e) (B.blockPermutation e)) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0,uF,uW} ℂ ((B.permute e).Levi F.Carrier)),
      σ.IsIrreducible → IsLeviCuspidal B σ.representation →
      (transport B (B.permute e) (B.blockPermutation e) hw σ.representation).Equiv
        τ.representation →
      Σ A : ∀ i : Fin B.length,
        SupercuspidalRep.{uF,uA} (F := F.Carrier) (n := B.size i),
        (σ.representation.Equiv (B.blockTensor (fun i => (A i).obj.representation))) ×
        (τ.representation.Equiv
          ((B.permute e).blockTensor (fun i => (A (e i)).obj.representation))) := by
  let := T.topology
  intro σ τ hσ hcσ E
  let h := padicLeviCuspidalFactorization.{uF,uV,uA} F T n hn B σ hσ hcσ
  let A := h.choose
  let Eσ := h.choose_spec.some
  exact ⟨A, Eσ,
    (E.symm.trans (transportEquiv (B := B) (C := B.permute e)
      (B.blockPermutation e) hw Eσ)).trans
      (blockPermutationTensorEquiv B e hw (fun i => (A i).obj.representation))⟩

/-- The remaining canonical product-matching input. This proposition asserts
no proof and imposes no finite-length hypothesis. -/
def CanonicalAdjacentSupercuspidalProductMatchingStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ), 0 < n →
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (B : BlockShape n) (j : ℕ) (hj : j + 1 < B.length)
      (A : ∀ i : Fin B.length,
        SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)),
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedProductInduced B (fun i => (A i).obj.representation)))
        (Rep.of (T.normalizedProductInduced (B.permute (B.adjacentSwap j hj))
          (fun i => (A (B.adjacentSwap j hj i)).obj.representation)))

/-- Canonical matching of supercuspidal products suffices for the full
published adjacent-swap target, retaining independent inducing universes. -/
theorem adjacentBlockSwap_of_canonicalProducts
    (h : CanonicalAdjacentSupercuspidalProductMatchingStatement.{uF,uV}) :
    AdjacentBlockSwapCuspidalInductionFactorsTheorem.{uF,uV,uW} := by
  classical
  intro F T n hn
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro B C w hw j hj hblocks hmin σ τ hσ hcσ _ _ ⟨E⟩
  have hcanon := eq_blockPermutation_of_blockIndex B (B.adjacentSwap j hj)
    w hw hmin (fun a => by
      rw [hblocks a, adjacentSwap_symm_val_eq_swap])
  obtain ⟨rfl, rfl⟩ := hcanon
  let D := canonicalCuspidalTensorData.{uF,uV,uW,uV}
    F T hn B (B.adjacentSwap j hj) hw σ τ hσ hcσ E
  exact haveSameJordanHolderFactors_transport (h F T n hn B j hj D.1)
    (T.normalizedParabolicInducedEquiv B D.2.1).symm
    (T.normalizedParabolicInducedEquiv (B.permute (B.adjacentSwap j hj)) D.2.2).symm

end Langlands.AllFieldBZ.CuspidalSupport
