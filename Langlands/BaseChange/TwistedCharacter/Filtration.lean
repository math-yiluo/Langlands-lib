import Langlands.BaseChange.SigmaLiftTransport
import Langlands.BaseChange.TwistedCharacter.Exactness
import Langlands.Representation.Filtration.SubsingletonProof
import Langlands.Representation.Smooth.Admissibility.ExactProof
import Langlands.Topology.LocallyProfiniteProof

/-! # Twisted distributions on finite invariant filtrations -/

noncomputable section

namespace Langlands

open CategoryTheory MeasureTheory HarmonicAnalysis

universe uG uV

namespace ObjectRepFiltration

variable {G : Type uG} [Group G] {R : Rep.{uV} ℂ G} {n : ℕ}
  (s : ObjectRepFiltration R n) (A : Module.End ℂ R)
  (hA : ∀ (i : Fin (n + 1)) (v : R), v ∈ s.subrepresentation i →
    A v ∈ s.subrepresentation i)

/-- Restrict a filtration-preserving operator to one step. -/
def stepEndomorphism (i : Fin (n + 1)) :
    Module.End ℂ (s.subrepresentation i).toSubmodule :=
  A.restrict (hA i)

/-- The operator on the actual successive quotient. -/
def gradedEndomorphism (i : Fin n) :
    Module.End ℂ (s.gradedRepresentation i) :=
  let S := (s.step i.castSucc).lowerInUpper (s.step i.succ) (Discrete.mk PUnit.unit)
  S.toSubmodule.mapQ S.toSubmodule (s.stepEndomorphism A hA i.succ) (by
    intro v hv
    let w : (s.subrepresentation i.succ).toSubmodule := v
    change A (w : R) ∈ s.subrepresentation i.castSucc
    exact hA i.castSucc w hv)

@[simp]
theorem gradedEndomorphism_projection (i : Fin n) (v : (s.subrepresentation i.succ).toSubmodule) :
    s.gradedEndomorphism A hA i ((s.gradedProjection i).hom v) =
      (s.gradedProjection i).hom (s.stepEndomorphism A hA i.succ v) := rfl

private def stepInclusion (i : Fin n) :
    (s.subrepresentation i.castSucc).toRepresentation.IntertwiningMap
      (s.subrepresentation i.succ).toRepresentation :=
  { toLinearMap := Submodule.inclusion (s.monotone_subrepresentation (Fin.castSucc_le_succ i))
    isIntertwining' := fun _ => rfl }

private theorem stepInclusion_range (i : Fin n) :
    LinearMap.range (s.stepInclusion i).toLinearMap =
      LinearMap.ker (s.gradedProjection i).hom.toLinearMap := by
  ext v
  change (∃ w, s.stepInclusion i w = v) ↔ (s.gradedProjection i).hom v = 0
  rw [s.gradedProjection_eq_zero_iff i v]
  exact ⟨fun ⟨w, hw⟩ => (congrArg Subtype.val hw) ▸ w.property,
    fun hv => ⟨⟨v, hv⟩, Subtype.ext rfl⟩⟩

end ObjectRepFiltration

namespace BaseChange

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] (μ : Measure G)
  [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
  {R : Rep.{uV} ℂ G} {n : ℕ}

/-- The twisted distribution for a filtration-preserving endomorphism is the
sum of the distributions of the induced endomorphisms on the graded pieces. -/
def TwistedDistributionFiltrationAdditivity
    (s : ObjectRepFiltration R n) (hR : IsAdmissible R.ρ) (A : Module.End ℂ R)
    (hA : ∀ (i : Fin (n + 1)) (v : R), v ∈ s.subrepresentation i →
      A v ∈ s.subrepresentation i) : Prop :=
  ∃ hGraded : ∀ i, IsAdmissible (s.gradedRepresentation i).ρ,
    twistedDistribution μ R.ρ hR A =
      ∑ i, twistedDistribution μ _ (hGraded i) (s.gradedEndomorphism A hA i)

theorem twistedDistributionFiltrationAdditivity (s : ObjectRepFiltration R n)
    (hR : IsAdmissible R.ρ) (A : Module.End ℂ R)
    (hA : ∀ (i : Fin (n + 1)) (v : R), v ∈ s.subrepresentation i →
      A v ∈ s.subrepresentation i) :
    TwistedDistributionFiltrationAdditivity μ s hR A hA := by
  have hCofinal (U : OpenSubgroup G) :
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ U := by
    obtain ⟨K, hK, hKU⟩ := ((Topology.LocallyProfiniteProof.vanDantzig G).mp
      Topology.isLocallyProfinite_of_mathlib).2 (U : Set G) U.mem_nhds_one
    exact ⟨K, hK, hKU⟩
  have hStep (i : Fin (n + 1)) : IsAdmissible (s.subrepresentation i).toRepresentation :=
    isAdmissible_of_injective ((s.step i).inclusion.app (Discrete.mk PUnit.unit)).hom
      ((s.step i).inclusion_injective _) hR
  have hInj (i : Fin n) : Function.Injective (s.stepInclusion i) :=
    Submodule.inclusion_injective (s.monotone_subrepresentation (Fin.castSucc_le_succ i))
  have hGraded (i : Fin n) : IsAdmissible (s.gradedRepresentation i).ρ :=
    ((isAdmissible_iff_of_shortExact hCofinal (s.stepInclusion i) (s.gradedProjection i).hom
      (hInj i) (s.gradedProjection_surjective i) (s.stepInclusion_range i)
      (hStep i.succ).1).mp (hStep i.succ)).2
  let stepTrace (i : Fin (n + 1)) :=
    twistedDistribution μ _ (hStep i) (s.stepEndomorphism A hA i)
  let gradedTrace (i : Fin n) :=
    twistedDistribution μ _ (hGraded i) (s.gradedEndomorphism A hA i)
  have hAdd (i : Fin n) : stepTrace i.succ = stepTrace i.castSucc + gradedTrace i :=
    twistedDistribution_shortExact μ (hStep i.castSucc) (hStep i.succ) (hGraded i)
      (s.stepInclusion i) (s.gradedProjection i).hom (hInj i) (s.gradedProjection_surjective i)
      (s.stepInclusion_range i) _ _ _ (LinearMap.ext fun _ => rfl)
      (LinearMap.ext fun v => (s.gradedEndomorphism_projection A hA i v).symm)
  have hZero : stepTrace 0 = 0 := by
    have hOp : s.stepEndomorphism A hA 0 = 0 := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      have hBot : s.subrepresentation 0 ≤ ⊥ := le_of_eq s.subrepresentation_zero
      have hv : (v : R) = 0 := (Submodule.mem_bot ℂ).mp (hBot v.property)
      change A (v : R) = 0
      rw [hv, map_zero]
    change twistedDistribution μ _ (hStep 0) (s.stepEndomorphism A hA 0) = 0
    rw [hOp]
    simpa using twistedDistribution_smul μ _ (hStep 0) 0 (s.stepEndomorphism A hA 0)
  have hTop : stepTrace (Fin.last n) = twistedDistribution μ R.ρ hR A := by
    let e : (s.subrepresentation (Fin.last n)).toRepresentation.Equiv R.ρ :=
      Representation.Equiv.mk
        { toFun := Subtype.val
          invFun := fun v => ⟨v, by rw [s.subrepresentation_last]; trivial⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
        (fun _ => rfl)
    exact (twistedDistribution_eq_of_equivalent μ (hStep (Fin.last n)) hR e
      (s.stepEndomorphism A hA (Fin.last n))).symm
  have hSum (j : ℕ) (hj : j ≤ n) :
      stepTrace ⟨j, Nat.lt_succ_of_le hj⟩ =
        ∑ i : Fin j, gradedTrace ⟨i, lt_of_lt_of_le i.isLt hj⟩ := by
    induction j with
    | zero =>
      have hIndex : (⟨0, Nat.lt_succ_of_le hj⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
      rw [hIndex, Finset.univ_eq_empty, Finset.sum_empty]
      exact hZero
    | succ j ih =>
      have hjn : j < n := hj
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [← ih hjn.le]
      exact hAdd ⟨j, hjn⟩
  exact ⟨hGraded, hTop.symm.trans (hSum n le_rfl)⟩

end BaseChange

end Langlands
