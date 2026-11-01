import Langlands.Representation.Geometric.OuterReversal
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Induction.SmoothGroupTransport
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-! Actual normalized refined induction and flattened coordinates under outer reversal. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CuspidalSupport OppositeCuspidalJacquetFiltration

universe uF
variable {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (F : Type uF) [Field F]

/-- Outer reversal in the two actual flattened product Levis. -/
def outerReverseFlattenedLeviEquiv :
    (B.flatten S).Levi F ≃* (B.reverse.flatten (outerReverseRefinement B S)).Levi F :=
  (flattenedLeviEquiv F B S).trans
    ((outerReverseRefinedLeviEquiv B F S).trans
      (flattenedLeviEquiv F B.reverse (outerReverseRefinement B S)).symm)

/-- The same coarse reversal permutation conjugates the reversed flattened Levi
onto the original flattened Levi. -/
theorem reverseMatrix_conj_outerReverseFlattenedLeviEquiv (m : (B.flatten S).Levi F) :
    B.reverseMatrix F *
        (B.reverse.flatten (outerReverseRefinement B S)).leviEmbedding F
          (outerReverseFlattenedLeviEquiv B S F m) * (B.reverseMatrix F)⁻¹ =
      (B.flatten S).leviEmbedding F m := by
  rw [← flattenedLeviEquiv_embedding F B.reverse (outerReverseRefinement B S)]
  simp only [outerReverseFlattenedLeviEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, outerReverseRefinedLeviEquiv_val]
  rw [reverseMatrix_mul_leviEmbedding, flattenedLeviEquiv_embedding]

/-- Concrete conjugacy for the surviving outer-reversed flattened source. -/
theorem conjugatesLevi_outerReverseFlattened :
    ConjugatesLevi (F := F) (B.reverse.flatten (outerReverseRefinement B S))
      (B.flatten S) B.reversePermutation := by
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨_, ⟨m', rfl⟩, rfl⟩
    refine ⟨(outerReverseFlattenedLeviEquiv B S F).symm m', ?_⟩
    rw [← reverseMatrix_conj_outerReverseFlattenedLeviEquiv,
      MulEquiv.apply_symm_apply]
    rfl
  · rintro ⟨m, rfl⟩
    refine ⟨(B.reverse.flatten (outerReverseRefinement B S)).leviEmbedding F
      (outerReverseFlattenedLeviEquiv B S F m), ⟨_, rfl⟩, ?_⟩
    exact reverseMatrix_conj_outerReverseFlattenedLeviEquiv B S F m

/-- Actual inverse flattened conjugation is the constructed outer relabelling. -/
theorem leviConjugation_outerReverseFlattened_symm
    (h : ConjugatesLevi (F := F) (B.reverse.flatten (outerReverseRefinement B S))
      (B.flatten S) B.reversePermutation) (m : (B.flatten S).Levi F) :
    (leviConjugation _ _ B.reversePermutation h).symm m =
      outerReverseFlattenedLeviEquiv B S F m := by
  apply (B.reverse.flatten (outerReverseRefinement B S)).leviEmbedding_injective F
  rw [leviConjugation_symm_embedding]
  have h' := reverseMatrix_conj_outerReverseFlattenedLeviEquiv B S F m
  rw [← h']
  change (B.reverseMatrix F)⁻¹ *
    (B.reverseMatrix F * _ * (B.reverseMatrix F)⁻¹) * B.reverseMatrix F = _
  group

/-- Actual inverse coarse conjugation is literal reversal of the outer labels. -/
theorem leviConjugation_outerReverse_symm
    (h : ConjugatesLevi (F := F) B.reverse B B.reversePermutation) (m : B.Levi F) :
    (leviConjugation _ _ B.reversePermutation h).symm m =
      leviReverseEquiv (R := F) B m := by
  apply B.reverse.leviEmbedding_injective F
  rw [leviConjugation_symm_embedding]
  have h' := reverseMatrix_mul_leviEmbedding (R := F) B m
  rw [← h']
  change (B.reverseMatrix F)⁻¹ *
    (B.reverseMatrix F * _ * (B.reverseMatrix F)⁻¹) * B.reverseMatrix F = _
  group

variable [TopologicalSpace F] [IsTopologicalRing F]

/-- Flattened outer relabelling with the actual product topologies. -/
def outerReverseFlattenedLeviEquivContinuous :
    (B.flatten S).Levi F ≃ₜ*
      (B.reverse.flatten (outerReverseRefinement B S)).Levi F :=
  (flattenedLeviEquivContinuous F B S).trans
    ((outerReverseRefinedLeviEquivContinuous B F S).trans
      (flattenedLeviEquivContinuous F B.reverse (outerReverseRefinement B S)).symm)

/-- The continuous inverse coarse conjugation equals the product reindexing. -/
theorem leviConjugationContinuous_outerReverse_symm
    (h : ConjugatesLevi (F := F) B.reverse B B.reversePermutation) :
    (leviConjugationContinuous B.reversePermutation h).symm =
      outerReverseLeviEquivContinuous B F := by
  apply ContinuousMulEquiv.ext
  intro m
  exact leviConjugation_outerReverse_symm B F h m

end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open Geometric GeneralLinear

universe uF uV
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Both actual positively normalized inducing actions agree after outer reindexing. -/
theorem refinedInducing_outerReverse
    (σ : Representation ℂ
      (refinedLevi F.Carrier B.reverse (outerReverseRefinement B S)) V)
    (q : refinedParabolic F.Carrier B S) :
    twist (T.refinedParabolicHalfModulus B.reverse (outerReverseRefinement B S))
        (σ.comp (refinedLeviProjection F.Carrier B.reverse (outerReverseRefinement B S)))
        (outerReverseRefinedParabolicEquiv B F.Carrier S q) =
      twist (T.refinedParabolicHalfModulus B S)
        ((σ.comp (outerReverseRefinedLeviEquiv B F.Carrier S).toMonoidHom).comp
          (refinedLeviProjection F.Carrier B S)) q := by
  ext v
  change (T.refinedParabolicHalfModulus B.reverse (outerReverseRefinement B S)
      (outerReverseRefinedParabolicEquiv B F.Carrier S q) : ℂ) •
      σ (refinedLeviProjection F.Carrier B.reverse (outerReverseRefinement B S)
        (outerReverseRefinedParabolicEquiv B F.Carrier S q)) v =
    (T.refinedParabolicHalfModulus B S q : ℂ) •
      σ (outerReverseRefinedLeviEquiv B F.Carrier S
        (refinedLeviProjection F.Carrier B S q)) v
  rw [T.refinedParabolicHalfModulus_outerReverse, refinedLeviProjection_outerReverse]

/-- Precomposition on actual induced functions compares reversed and original
refined induction, pulling back both the ambient and inducing actions. -/
def normalizedRefinedInduced_outerReverseEquiv
    (σ : Representation ℂ
      (refinedLevi F.Carrier B.reverse (outerReverseRefinement B S)) V) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    letI := T.leviTopologicalGroup B.reverse
    Representation.Equiv
      ((T.normalizedRefinedInduced B.reverse (outerReverseRefinement B S) σ).comp
        (OppositeCuspidalJacquetFiltration.leviReverseEquiv (R := F.Carrier) B).toMonoidHom)
      (T.normalizedRefinedInduced B S
        (σ.comp (outerReverseRefinedLeviEquiv B F.Carrier S).toMonoidHom)) := by
  letI := T.topology
  letI := T.leviTopologicalGroup B
  letI := T.leviTopologicalGroup B.reverse
  exact Induction.precomposeSmoothInducedGroupEquiv
    (outerReverseLeviEquivContinuous B F.Carrier)
    (outerReverseRefinedParabolicEquiv B F.Carrier S) (fun _ => rfl)
    (T.refinedInducing_outerReverse B S σ)

end Langlands.PadicField.TopologicalData
