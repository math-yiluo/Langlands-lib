import Langlands.TraceFormula.RationalLocalGeneralLinear
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.MeasureTheory.Measure.Count

/-! # An auxiliary finite-place cutoff for periodization on the actual norm-one group -/

noncomputable section

namespace Langlands.TraceFormula

open CategoryTheory _root_.AlgebraicGeometry NumberField MeasureTheory
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.QuotientIntegration
open scoped CategoryTheory.MonObj

universe u

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)
local notation "A₁" => normOneSubgroup K GLG
local notation "Γ" => rationalNormOneSubgroup K GLG

local instance globalizationAuxiliaryIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance globalizationAuxiliarySmooth : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

/-- Localization at one place is injective on the actual principal norm-one subgroup. -/
theorem atPlace_rationalNormOneSubgroup_injective (v : Langlands.Global.FinitePlace K) :
    Function.Injective (fun γ : Γ => atPlace K GLG (.inr v) (γ.val : AdelicGroupPoints K GLG)) := by
  intro γ γ' h
  obtain ⟨q, hq⟩ := γ.property
  obtain ⟨q', hq'⟩ := γ'.property
  have h₁ : (γ.val : AdelicGroupPoints K GLG) = rational K GLG q :=
    (congrArg Subtype.val hq).symm
  have h₂ : (γ'.val : AdelicGroupPoints K GLG) = rational K GLG q' :=
    (congrArg Subtype.val hq').symm
  have heq : q = q' := by
    apply (GeneralLinearGroupPoints.rationalEquiv K n).injective
    have hv := congrArg (localGLEquiv K n (.inr v)) h
    change localGLEquiv K n (.inr v) (atPlace K GLG (.inr v) (γ.val : AdelicGroupPoints K GLG)) =
      localGLEquiv K n (.inr v) (atPlace K GLG (.inr v) (γ'.val : AdelicGroupPoints K GLG)) at hv
    rw [h₁, h₂, localGLEquiv_atPlace_rational, localGLEquiv_atPlace_rational] at hv
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply (algebraMap K (v.adicCompletion K)).injective
    exact congrArg (fun g => g.val i j) hv
  apply Subtype.ext
  exact hq.symm.trans (heq ▸ hq')

/-- For any compact support set, a neighborhood of the identity at the supplied finite
place removes every principal norm-one point in that set other than the identity. -/
theorem exists_auxiliaryIdentityNeighborhood (v : Langlands.Global.FinitePlace K)
    {C : Set A₁} (hC : IsCompact C) :
    ∃ U : Set (PlaceGroupPoints K GLG (.inr v)), IsOpen U ∧ 1 ∈ U ∧
      ∀ γ : Γ, γ.val ∈ C → atPlace K GLG (.inr v) γ.val.val ∈ U → γ = 1 := by
  let p := fun γ : Γ => atPlace K GLG (.inr v) γ.val.val
  let bad : Set Γ := {γ | γ.val ∈ C ∧ γ ≠ 1}
  have hemb := (rationalNormOneSubgroup_isClosed K GLG).isClosedEmbedding_subtypeVal
  let : DiscreteTopology Γ := rationalNormOneSubgroup_discreteTopology K GLG
  have hpre : IsCompact (Subtype.val ⁻¹' C : Set Γ) := hemb.isCompact_preimage hC
  have hfin : bad.Finite := hpre.finite_of_discrete.subset (fun _ h => h.1)
  have hp : Function.Injective p := atPlace_rationalNormOneSubgroup_injective K n v
  have hp1 : p 1 = 1 := map_one (atPlace K GLG (.inr v))
  refine ⟨(p '' bad)ᶜ, (hfin.image p).isClosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨γ, hγ, h⟩
    exact hγ.2 (hp (h.trans hp1.symm))
  · intro γ hγ hU
    by_contra h
    exact hU ⟨γ, ⟨hγ, h⟩, rfl⟩

/-- For test functions supported in the compact set and the auxiliary neighborhood, the
periodization at the identity equals the original function value for counting measure. -/
theorem exists_auxiliaryPeriodizationCutoff (v : Langlands.Global.FinitePlace K)
    {C : Set A₁} (hC : IsCompact C) :
    ∃ U : Set (PlaceGroupPoints K GLG (.inr v)), IsOpen U ∧ 1 ∈ U ∧
      ∀ f : A₁ → ℂ, (∀ a, f a ≠ 0 → a ∈ C ∧ atPlace K GLG (.inr v) a.val ∈ U) →
        quotientAverage Γ Measure.count f (Quotient.mk _ 1) = f 1 := by
  classical
  obtain ⟨U, hUopen, hU1, hU⟩ := exists_auxiliaryIdentityNeighborhood K n v hC
  refine ⟨U, hUopen, hU1, fun f hf => ?_⟩
  rw [quotientAverage_mk]
  simp only [mul_one]
  have heq : (fun γ : Γ => f γ.val) = ({1} : Set Γ).indicator (fun _ => f 1) := by
    funext γ
    by_cases hγ : γ = 1
    · subst γ
      simp
    · have hzero : f γ.val = 0 := by
        by_contra h
        exact hγ (hU γ (hf γ h).1 (hf γ h).2)
      simp [hγ, hzero]
  rw [heq, integral_indicator_const _ (measurableSet_singleton (1 : Γ))]
  simp [measureReal_def]

end Langlands.TraceFormula
