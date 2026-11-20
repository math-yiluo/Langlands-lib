import Langlands.BaseChange.TwistedCharacter.CompactAverage
import Langlands.Representation.Smooth.CompactCompletionFixed
import Mathlib.MeasureTheory.Group.Integral

/-! # Conjugation averages for smooth representations -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis HarishChandraSchwartz MeasureTheory

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
  (K : Subgroup G) [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

private def conjugates (B : Module.End ℂ V) (k : K) : Module.End ℂ V :=
  ρ (k : G) ∘ₗ B ∘ₗ ρ (k : G)⁻¹

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
include hρ in
private theorem conjugates_locallyConstant (B : Module.End ℂ V) (v : V) :
    IsLocallyConstant (fun k => conjugates ρ K B k v) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro k
  have hin := (Hecke.orbitMap_locallyConstant ρ (hρ v)).comp_continuous
    (continuous_subtype_val.inv : Continuous fun j : K => (j : G)⁻¹)
  have hout := (Hecke.orbitMap_locallyConstant ρ (hρ (B (ρ (k : G)⁻¹ v)))).comp_continuous
    (continuous_subtype_val : Continuous fun j : K => (j : G))
  filter_upwards [hin.eventually_eq k, hout.eventually_eq k] with j hj hj'
  change ρ (j : G)⁻¹ v = ρ (k : G)⁻¹ v at hj
  change ρ (j : G) (B (ρ (j : G)⁻¹ v)) = ρ (k : G) (B (ρ (k : G)⁻¹ v))
  rw [hj]
  exact hj'

/-- Average the conjugates of an endomorphism under the probability Haar measure of `K`. -/
def conjugationAverage (B : Module.End ℂ V) : Module.End ℂ V :=
  compactOperatorAverage (normalizedHaar K) (conjugates ρ K B)
    (conjugates_locallyConstant ρ hρ K B)

/-- Scalarization of the algebraic conjugation average. -/
theorem conjugationAverage_dual (B : Module.End ℂ V) (v : V) (ℓ : V →ₗ[ℂ] ℂ) :
    ℓ (conjugationAverage ρ hρ K B v) =
      ∫ k : K, ℓ (ρ (k : G) (B (ρ (k : G)⁻¹ v))) ∂(normalizedHaar K) :=
  compactOperatorAverage_dual _ _ _ _ _

/-- The average commutes with the action of the averaging subgroup. -/
theorem conjugationAverage_equivariant (B : Module.End ℂ V) (a : K) (v : V) :
    conjugationAverage ρ hρ K B (ρ (a : G) v) =
      ρ (a : G) (conjugationAverage ρ hρ K B v) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  rw [map_sub, sub_eq_zero, conjugationAverage_dual]
  change _ = (ℓ.comp (ρ (a : G))) (conjugationAverage ρ hρ K B v)
  rw [conjugationAverage_dual]
  calc
    _ = ∫ k : K, ℓ (ρ ((a * k : K) : G)
          (B (ρ ((a * k : K) : G)⁻¹ (ρ (a : G) v)))) ∂(normalizedHaar K) :=
      (integral_mul_left_eq_self _ a).symm
    _ = _ := by
      congr 1 with k
      have hinv : ((a * k : K) : G)⁻¹ * (a : G) = (k : G)⁻¹ := by
        simp [mul_inv_rev, mul_assoc]
      have h : ρ (((a * k : K) : G)⁻¹) (ρ (a : G) v) = ρ (k : G)⁻¹ v := by
        rw [← Module.End.mul_apply, ← map_mul, hinv]
      rw [h]
      simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, LinearMap.comp_apply]

section Trace

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- After integrating a test function, the conjugation average has finite rank and
preserves the twisted distribution trace. -/
theorem conjugationAverage_integratedAction_trace (μ : Measure G) [μ.IsHaarMeasure]
    (hρa : IsAdmissible ρ) (A : Module.End ℂ V) (f : SchwartzBruhat G) :
    ∃ hfin : conjugationAverage ρ hρa.1 K (Hecke.integratedAction μ ρ hρa.1 f ∘ₗ A) ∈
        finiteRankEnd V,
      FiniteRankEnd.trace
          ⟨conjugationAverage ρ hρa.1 K (Hecke.integratedAction μ ρ hρa.1 f ∘ₗ A), hfin⟩ =
        twistedDistribution μ ρ hρa A f := by
  classical
  obtain ⟨J, _, hJ, hbi⟩ :=
    Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  obtain ⟨N, hNJ, hN⟩ := CompactOpenSubgroup.exists_le_normalizedBy_compact
    ⟨J, hJ⟩ K (isCompact_iff_compactSpace.mpr inferInstance)
  let S := fixedVectors ρ N.toSubgroup
  let : Module.Finite ℂ S := hρa.2 N.1
  let T : finiteRankEnd V :=
    ⟨Hecke.integratedAction μ ρ hρa.1 f ∘ₗ A,
      (Character.finiteRankIntegratedAction μ ρ hρa f).property.comp_right A⟩
  have hT : T.val.range ≤ S := by
    rintro _ ⟨v, rfl⟩ k
    have hJrange := Hecke.integratedAction_range_le_fixedVectors μ ρ hρa.1
      (hbi f (Finset.mem_singleton_self f))
    exact hJrange (LinearMap.mem_range_self _ (A v)) ⟨(k : G), hNJ k.property⟩
  have hS (k : K) : (conjugates ρ K T.val k).range ≤ S := by
    rintro _ ⟨v, rfl⟩ a
    change ρ (a : G) (ρ (k : G) (T.val (ρ (k : G)⁻¹ v))) =
      ρ (k : G) (T.val (ρ (k : G)⁻¹ v))
    have ha : (k : G)⁻¹ * (a : G) * (k : G) ∈ N.1 := by
      apply (N.mem_conj (k : G) (a : G)).mp
      rw [hN (k : G) k.property]
      exact a.property
    have hfix : ρ ((k : G)⁻¹ * (a : G) * (k : G)) (T.val (ρ (k : G)⁻¹ v)) =
        T.val (ρ (k : G)⁻¹ v) :=
      hT (LinearMap.mem_range_self T.val (ρ (k : G)⁻¹ v)) (⟨_, ha⟩ : N.toSubgroup)
    have he : (a : G) * (k : G) = (k : G) * ((k : G)⁻¹ * (a : G) * (k : G)) := by
      group
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply, hfix]
  have hfin : conjugationAverage ρ hρa.1 K T.val ∈ finiteRankEnd V :=
    (mem_finiteRankEnd_iff _).mpr (Submodule.finiteDimensional_of_le
      (compactOperatorAverage_range_le _ _ _ S hS))
  refine ⟨hfin, ?_⟩
  change FiniteRankEnd.trace
      ⟨compactOperatorAverage (normalizedHaar K) (conjugates ρ K T.val)
        (conjugates_locallyConstant ρ hρa.1 K T.val), hfin⟩ = FiniteRankEnd.trace T
  refine (finiteRank_trace_compactOperatorAverage (normalizedHaar K) (conjugates ρ K T.val)
    (conjugates_locallyConstant ρ hρa.1 K T.val) S hS hfin).trans ?_
  have htrace (k : K) :
      FiniteRankEnd.trace
          ⟨conjugates ρ K T.val k, (mem_finiteRankEnd_iff _).mpr
            (Submodule.finiteDimensional_of_le (hS k))⟩ =
        FiniteRankEnd.trace T := by
    rw [← FiniteRankEnd.trace_conjugate
      (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom (k : G))) T]
    congr 1
  simp [htrace]

end Trace

end Langlands.BaseChange
