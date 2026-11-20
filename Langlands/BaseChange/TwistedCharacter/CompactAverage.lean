import Langlands.BaseChange.TwistedCharacter.Basic
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Spherical

/-! # Algebraic averaging of operators over compact spaces -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis MeasureTheory

universe uX uV

section CompactOperatorAverage

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ν : Measure X) [IsFiniteMeasure ν]
  (B : X → Module.End ℂ V) (hB : ∀ v, IsLocallyConstant (fun x => B x v))

private def operatorIntegrand (v : V) : SimpleFunc X V :=
  compactlySupportedSimpleFunc (fun x => B x v) (hB v) (HasCompactSupport.of_compactSpace _)

private theorem operatorIntegrand_finMeasSupp (v : V) :
    (operatorIntegrand B hB v).FinMeasSupp ν :=
  compactlySupportedSimpleFunc_finMeasSupp ν _ _ _

/-- The average of a pointwise locally constant family of operators on a compact space,
computed by a finite sum on each vector. -/
def compactOperatorAverage : Module.End ℂ V where
  toFun v := AlgebraicIntegral.integral ν (operatorIntegrand B hB v)
  map_add' v w := by
    have h : operatorIntegrand B hB (v + w) =
        operatorIntegrand B hB v + operatorIntegrand B hB w := by
      ext x
      exact map_add (B x) v w
    rw [h, AlgebraicIntegral.integral_add _ _
      (operatorIntegrand_finMeasSupp ν B hB v) (operatorIntegrand_finMeasSupp ν B hB w)]
  map_smul' c v := by
    have h : operatorIntegrand B hB (c • v) = c • operatorIntegrand B hB v := by
      ext x
      exact map_smul (B x) c v
    rw [h, AlgebraicIntegral.integral_smul c _ (operatorIntegrand_finMeasSupp ν B hB v)]
    rfl

/-- An algebraic linear functional evaluates the compact operator average by scalar integration. -/
theorem compactOperatorAverage_dual (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    ℓ (compactOperatorAverage ν B hB v) = ∫ x, ℓ (B x v) ∂ν := by
  change ℓ (AlgebraicIntegral.integral ν (operatorIntegrand B hB v)) = _
  rw [← AlgebraicIntegral.integral_linearMap _ (operatorIntegrand_finMeasSupp ν B hB v) ℓ,
    AlgebraicIntegral.integral_eq_bochner _
      ((operatorIntegrand_finMeasSupp ν B hB v).map ℓ.map_zero)]
  rfl

/-- If every image lies in a subspace, so does the image of the average. -/
theorem compactOperatorAverage_range_le (S : Submodule ℂ V)
    (hS : ∀ x, (B x).range ≤ S) : (compactOperatorAverage ν B hB).range ≤ S := by
  rintro _ ⟨v, rfl⟩
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp
  intro ℓ hℓ
  rw [compactOperatorAverage_dual]
  have hzero (x : X) : ℓ (B x v) = 0 :=
    ((Submodule.mem_dualAnnihilator ℓ).mp hℓ) _ (hS x (LinearMap.mem_range_self _ _))
  simp [hzero]

omit [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] in
include hB in
private theorem onSubspace_locallyConstant (S : Submodule ℂ V)
    (hS : ∀ x, (B x).range ≤ S) (v : S) :
    IsLocallyConstant (fun x => FiniteRankEnd.onSubspace (B x) S (hS x) v) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨U, hU, hx, heq⟩ := (hB (v : V)).exists_open x
  exact ⟨U, hU, hx, fun y hy => Subtype.ext (heq y hy)⟩

private theorem onSubspace_average (S : Submodule ℂ V)
    (hS : ∀ x, (B x).range ≤ S) :
    FiniteRankEnd.onSubspace (compactOperatorAverage ν B hB) S
        (compactOperatorAverage_range_le ν B hB S hS) =
      compactOperatorAverage ν (fun x => FiniteRankEnd.onSubspace (B x) S (hS x))
        (onSubspace_locallyConstant B hB S hS) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  let integrand := operatorIntegrand (fun x => FiniteRankEnd.onSubspace (B x) S (hS x))
    (onSubspace_locallyConstant B hB S hS) v
  have hfin : integrand.FinMeasSupp ν :=
    operatorIntegrand_finMeasSupp ν _ _ _
  change AlgebraicIntegral.integral ν (operatorIntegrand B hB v) =
    S.subtype (AlgebraicIntegral.integral ν integrand)
  rw [← AlgebraicIntegral.integral_linearMap _ hfin S.subtype]
  apply congrArg (AlgebraicIntegral.integral ν)
  exact SimpleFunc.ext fun _ => rfl

/-- The ordinary trace commutes with compact averaging on a finite-dimensional space. -/
theorem trace_compactOperatorAverage [FiniteDimensional ℂ V] :
    LinearMap.trace ℂ V (compactOperatorAverage ν B hB) =
      ∫ x, LinearMap.trace ℂ V (B x) ∂ν := by
  classical
  let b := Module.finBasis ℂ V
  simp only [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace, Matrix.diag_apply,
    LinearMap.toMatrix_apply, ← Module.Basis.coord_apply]
  simp_rw [compactOperatorAverage_dual]
  rw [integral_finsetSum]
  intro i _
  exact ((hB (b i)).comp (b.coord i)).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- When all the images lie in a common finite-dimensional space, finite-rank trace
commutes with compact averaging. -/
theorem finiteRank_trace_compactOperatorAverage (S : Submodule ℂ V)
    [FiniteDimensional ℂ S] (hS : ∀ x, (B x).range ≤ S)
    (hfin : (compactOperatorAverage ν B hB) ∈ finiteRankEnd V) :
    FiniteRankEnd.trace ⟨compactOperatorAverage ν B hB, hfin⟩ =
      ∫ x, FiniteRankEnd.trace ⟨B x, (mem_finiteRankEnd_iff _).mpr
        (Submodule.finiteDimensional_of_le (hS x))⟩ ∂ν := by
  rw [FiniteRankEnd.trace_eq_subspace _ S (compactOperatorAverage_range_le ν B hB S hS),
    onSubspace_average ν B hB S hS, trace_compactOperatorAverage]
  congr 1
  funext x
  rw [FiniteRankEnd.trace_eq_subspace _ S (hS x)]

end CompactOperatorAverage

end Langlands.BaseChange
