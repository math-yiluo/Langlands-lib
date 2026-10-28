import Langlands.Representation.Classification.RelativeJacquetEmbeddingStatement
import Langlands.Representation.Parabolic.IrreducibleOppositeJacquetUnitProof
import Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof
import Langlands.Representation.Parabolic.OppositeRefinementExactnessProof
import Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof
import Langlands.Representation.Filtration.MultiplicityAdditivityProof

/-! Relative opposite-Jacquet embeddings and their actual finite-series bounds. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW

/-- Refined opposite Jacquet exactness sends the irreducible unit embedding
to the relative embedding, and actual short-exact decomposition bounds counts. -/
theorem glRelativeJacquetEmbedding :
    GLRelativeJacquetEmbeddingStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B S μ hμi hμa
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  let I := CuspidalJacquetMultiplicity.induced T B μ
  let O := CuspidalJacquetMultiplicity.oppositeJacquet T B I
  obtain ⟨i, hi⟩ :=
    (Parabolic.irreducibleOppositeJacquetUnit.{uF, uW}).1 p F T n hn B μ hμi hμa
  have hIa : IsAdmissible I.ρ :=
    Parabolic.normalizedInductionAdmissibility F T B μ μ.ρ hμa
  have hOa : IsAdmissible O.ρ :=
    Parabolic.isAdmissible_standardOppositeJacquet F T B I I.ρ hIa
  have hiq : Function.Injective (T.normalizedRefinedOppositeJacquetMap B S i) :=
    T.normalizedRefinedOppositeJacquetMap_injective B S i hOa.1 hi
  obtain ⟨E, _⟩ :=
    Parabolic.normalizedOppositeRefinementTransitivity p F T n B S I
  let j : (innerJacquet T B S μ).ρ.IntertwiningMap (ambientJacquet T B S μ).ρ :=
    E.toIntertwiningMap.comp (T.normalizedRefinedOppositeJacquetMap B S i)
  have hj : Function.Injective j :=
    E.toLinearEquiv.injective.comp hiq
  refine ⟨⟨j, hj⟩, ?_⟩
  intro τ M hM
  let A := ambientJacquet T B S μ
  let C : Rep.{max uF uW} ℂ (refinedLevi F.Carrier B S) :=
    Rep.of (A.ρ.quotient j.range.toSubmodule
      (fun g _ hx => j.range.apply_mem_toSubmodule g hx))
  let q : A.ρ.IntertwiningMap C.ρ :=
    { toLinearMap := j.range.toSubmodule.mkQ
      isIntertwining' _ := rfl }
  have hex : LinearMap.range j.toLinearMap = LinearMap.ker q.toLinearMap := by
    change j.range.toSubmodule = LinearMap.ker j.range.toSubmodule.mkQ
    exact (Submodule.ker_mkQ _).symm
  obtain ⟨m, c, hm, _, hsum⟩ :=
    jordanHolderShortExactDecomposition ℂ (refinedLevi F.Carrier B S)
      (innerJacquet T B S μ) A C τ j q hj (Submodule.mkQ_surjective _) hex M hM
  exact ⟨m, hm, by omega⟩

end Langlands
