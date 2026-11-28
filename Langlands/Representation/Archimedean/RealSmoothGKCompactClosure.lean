import Langlands.Representation.Archimedean.AdmissibleCompactFiniteClosure
import Langlands.Representation.Archimedean.GKModuleQuotient
import Langlands.Representation.Archimedean.RealPrincipalSeriesCompactAverages
import Langlands.Representation.Archimedean.SmoothHilbertTransposePairingReduction

/-! # Compact-finite vectors in the closure of an admissible smooth image -/

noncomputable section

open MeasureTheory Set
open scoped Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV uE

local notation:max "G" n:max => Langlands.GeneralLinear n ℝ
local notation:max "O" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation:max "K" n:max => unitaryCompact ℝ n
local notation:max "L" n:max => ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ
local notation:max "I" n:max => matrixModel ℝ n
local notation:max "D" n:max R:max => DerivativeSmoothVectors (I n) R
local notation:max "ε" n:max R:max => derivativeCLM (I n) R []

private theorem finiteVector_compact_restrict {H K₀ V : Type*} [Monoid H] [Monoid K₀]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V) (c : K₀ →* H)
    {v : V} (hv : FiniteVectors.IsFiniteVector ρ v) :
    FiniteVectors.IsFiniteVector (ρ.comp c) v := by
  let _ : FiniteDimensional ℂ (FiniteVectors.orbitSpan ρ v) := hv
  apply Submodule.finiteDimensional_of_le (S₂ := FiniteVectors.orbitSpan ρ v)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact FiniteVectors.action_mem_orbitSpan ρ (c k) v

/-- The norm closure of an admissible algebraic image has precisely that image
when tested on the values of genuine compact-finite smooth vectors. -/
def RealSmoothGKCompactClosureStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (O n) V) (π : (L n) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : G n →* (E →L[ℂ] E)) (e : V →ₗ[ℂ] D n R),
    IsRealGKModule n ρ π → IsAdmissibleGKModule ρ → IsContinuousRepresentation R →
    IsSmoothGKIntertwiner ℝ n R ρ π e →
    e.range = smoothKFinite ℝ n R ⊓
      (((ε n R).toLinearMap.comp e).range.topologicalClosure).comap (ε n R).toLinearMap

theorem realSmoothGKCompactClosure : RealSmoothGKCompactClosureStatement.{uV,uE} := by
  intro n V _ _ ρ π E _ _ _ R e hGK hadm hR he
  let κ : Representation ℂ (O n) (D n R) := (representation (I n) R).comp Unitary.toUnits
  let P := (ε n R).toLinearMap.comp e
  let c := RealPrincipalSeriesHilbert.orthogonalCompactEquiv n
  let σ := ρ.comp c.symm.toMonoidHom
  let S := normCompactRepresentation (K n) R
  have hc (k : K n) : Unitary.toUnits (c.symm k) = (k : G n) :=
    congrArg Subtype.val (c.apply_symm_apply k)
  have hP (k : K n) (v : V) : P (σ k v) = S k (P v) := by
    change ε n R (e (ρ (c.symm k) v)) = R (k : G n) (ε n R (e v))
    rw [he.1, hc]
    rfl
  let W : Subrepresentation S :=
    { toSubmodule := P.range
      apply_mem_toSubmodule := by
        rintro k _ ⟨v, rfl⟩
        exact ⟨σ k v, hP k v⟩ }
  have hfin (v : V) : FiniteVectors.IsFiniteVector σ v :=
    finiteVector_compact_restrict ρ c.symm.toMonoidHom (hGK.1 v)
  have hcont (v : V) (ℓ : V →ₗ[ℂ] ℂ) : Continuous (fun k : K n => ℓ (σ k v)) :=
    (hGK.2.1 v ℓ).comp RealPrincipalSeriesHilbert.continuous_orthogonalCompactEquiv_symm
  have hadmσ : IsAdmissibleGKModule σ := by
    intro d η hη
    let η' := η.comp c.toMonoidHom
    have hEq : gkIntertwiners σ d η = gkIntertwiners ρ d η' := by
      ext T
      constructor
      · intro hT k x
        have h := hT (c k) x
        change T (η (c k) *ᵥ x) = ρ (c.symm (c k)) (T x) at h
        rwa [c.symm_apply_apply] at h
      · intro hT k x
        have h := hT (c.symm k) x
        change T (η (c (c.symm k)) *ᵥ x) = ρ (c.symm k) (T x) at h
        rwa [c.apply_symm_apply] at h
    rw [hEq]
    exact hadm _ _ (hη.comp RealPrincipalSeriesHilbert.continuous_orthogonalCompactEquiv)
  let T := P.intertwiningMap_of_isIntertwiningMap σ S hP
  let A := (P.codRestrict W.toSubmodule (fun x => ⟨x, rfl⟩)).intertwiningMap_of_isIntertwiningMap
    σ W.toRepresentation (fun k x => Subtype.ext (hP k x))
  have hA : Function.Surjective A := by
    intro y
    obtain ⟨x, hx⟩ := y.prop
    exact ⟨x, Subtype.ext hx⟩
  have hW : ∀ v ∈ W.toSubmodule, FiniteVectors.IsFiniteVector S v := by
    rintro _ ⟨x, rfl⟩
    exact (hfin x).map T
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    let eK := e.intertwiningMap_of_isIntertwiningMap ρ κ he.1
    exact ⟨(hGK.1 v).map eK, Submodule.le_topologicalClosure _ ⟨v, rfl⟩⟩
  · intro v hv
    let Q := (ε n R).toLinearMap.intertwiningMap_of_isIntertwiningMap
      (κ.comp c.symm.toMonoidHom) S (fun k x => by
        change ε n R (representation (I n) R (Unitary.toUnits (c.symm k)) x) =
          R (k : G n) (ε n R x)
        rw [hc]
        rfl)
    have hvK : FiniteVectors.IsFiniteVector S (ε n R v) :=
      (finiteVector_compact_restrict κ c.symm.toMonoidHom hv.1).map Q
    let _ : MeasurableSpace (K n) := borel (K n)
    let _ : BorelSpace (K n) := ⟨rfl⟩
    let μ : Measure (K n) := Measure.haarMeasure ⟨⟨univ, isCompact_univ⟩, by simp⟩
    let _ : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
    have h := admissibleCompactFiniteClosure (K n) μ R W hR
      (hadmσ.of_surjective hfin hcont A hA) hW hv.2 hvK
    obtain ⟨w, hw⟩ := h
    exact ⟨w, derivativeCLM_nil_injective ℝ n R hw⟩

end Langlands.Archimedean
