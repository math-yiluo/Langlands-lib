import Langlands.Representation.Archimedean.RealInductionStagesFiltration
import Langlands.Representation.Archimedean.RealUnlinkedSwapReduction

/-!
# Induction in stages of injective real standard intertwiners

The induced map of `RealInductionStagesInduce` preserves exact Lie equivariance and
injectivity. Consequently, an injective intertwiner between two equal-rank middle lists
extends through arbitrary surrounding lists.
-/

noncomputable section

open scoped Matrix TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

namespace InductionStages

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

/-- Exact standard intertwiners commute with `kRep` and `lie`. -/
theorem isRealStandardIntertwiner_iff {n : ℕ} {ds es : List RealBlock}
    {T : KFin n ds →ₗ[ℂ] KFin n es} :
    IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T ↔
      (∀ k f, T (kRep n ds k f) = kRep n es k (T f)) ∧
        ∀ X f, T (lie n ds X f) = lie n es X (T f) := by
  constructor
  · rintro ⟨hk, hl⟩
    refine ⟨fun k f => ?_, fun X f => ?_⟩
    · obtain ⟨hf, hT⟩ := hk k f
      have e : (⟨_, hf⟩ : KFin n ds) = kRep n ds k f :=
        Subtype.ext (coe_kRep k f).symm
      rw [e] at hT
      exact hT
    · obtain ⟨hf, hT⟩ := hl X f
      have e : (⟨_, hf⟩ : KFin n ds) = lie n ds X f :=
        Subtype.ext (lie_apply_coe n ds X f).symm
      rw [e] at hT
      exact hT
  · rintro ⟨hk, hl⟩
    refine ⟨fun k f => ?_, fun X f => ?_⟩
    · have hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
          (k : Langlands.GeneralLinear n ℝ) (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
            KFin n ds := by
        rw [← coe_kRep]
        exact (kRep n ds k f).2
      refine ⟨hf, ?_⟩
      have e : (⟨_, hf⟩ : KFin n ds) = kRep n ds k f :=
        Subtype.ext (coe_kRep k f).symm
      rw [e]
      exact hk k f
    · have hf : rightDerivative (matrixModel ℝ n) X (f : Langlands.GeneralLinear n ℝ → ℂ) ∈
          KFin n ds := by
        rw [← lie_apply_coe]
        exact (lie n ds X f).2
      refine ⟨hf, ?_⟩
      have e : (⟨_, hf⟩ : KFin n ds) = lie n ds X f :=
        Subtype.ext (lie_apply_coe n ds X f).symm
      rw [e]
      exact hl X f

section Stages

variable {n a r : ℕ} {pre ds es post : List RealBlock}
  (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank es = r)
  (hr' : realRank ds = r) (hn : realRank (pre ++ es ++ post) = n)
  {T : KFin r ds →ₗ[ℂ] KFin r es}
  (hT : ∀ k f, T (kRep r ds k f) = kRep r es k (T f))

/-- Exact Lie equivariance is preserved by the induced map. -/
theorem ind_lie
    (hL : ∀ X f, T (lie r ds X f) = lie r es X (T f))
    (X : Matrix (Fin n) (Fin n) ℝ) (F : KFin n (pre ++ ds ++ post)) :
    ind h ha hr hr' hn T hT (lie n (pre ++ ds ++ post) X F) =
      lie n (pre ++ es ++ post) X (ind h ha hr hr' hn T hT F) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_sliceK h ha hr
  intro κ
  have hzero := sliceK_ind_lie_sub_mem h ha hr hr' hn hT ⊥
    (fun Z f => by rw [hL, sub_self]; exact Submodule.zero_mem _) X F κ
  simpa only [Submodule.mem_bot] using hzero

/-- The induced map of an exact standard intertwiner is an exact standard intertwiner. -/
theorem ind_isRealStandardIntertwiner
    (hL : ∀ X f, T (lie r ds X f) = lie r es X (T f)) :
    IsRealStandardIntertwiner n (realStandardRep n (pre ++ es ++ post))
      (realStandardLie n (pre ++ es ++ post)) (pre ++ ds ++ post)
      (ind h ha hr hr' hn T hT) :=
  isRealStandardIntertwiner_iff.mpr
    ⟨ind_kRep h ha hr hr' hn hT, ind_lie h ha hr hr' hn hT hL⟩

/-- The slice identity detects the kernel of the induced map. -/
theorem injective_ind (hi : Function.Injective T) :
    Function.Injective (ind h ha hr hr' hn T hT) := by
  intro F G hFG
  apply sub_eq_zero.mp
  apply eq_zero_of_sliceK h ha hr'
  intro κ
  apply hi
  simp only [map_zero, map_sub]
  rw [← sliceK_ind h ha hr hr' hn hT,
    ← sliceK_ind h ha hr hr' hn hT, hFG, sub_self]

/-- Induction of an exact standard intertwiner through surrounding blocks. -/
def standardInd
    (hI : IsRealStandardIntertwiner r (realStandardRep r es) (realStandardLie r es) ds T) :
    KFin n (pre ++ ds ++ post) →ₗ[ℂ] KFin n (pre ++ es ++ post) :=
  ind h ha hr hr' hn T (isRealStandardIntertwiner_iff.mp hI).1

theorem standardInd_intertwiner
    (hI : IsRealStandardIntertwiner r (realStandardRep r es) (realStandardLie r es) ds T) :
    IsRealStandardIntertwiner n (realStandardRep n (pre ++ es ++ post))
      (realStandardLie n (pre ++ es ++ post)) (pre ++ ds ++ post)
      (standardInd h ha hr hr' hn hI) :=
  ind_isRealStandardIntertwiner h ha hr hr' hn
    (isRealStandardIntertwiner_iff.mp hI).1 (isRealStandardIntertwiner_iff.mp hI).2

theorem standardInd_injective
    (hI : IsRealStandardIntertwiner r (realStandardRep r es) (realStandardLie r es) ds T)
    (hi : Function.Injective T) :
    Function.Injective (standardInd h ha hr hr' hn hI) :=
  injective_ind h ha hr hr' hn (isRealStandardIntertwiner_iff.mp hI).1 hi

end Stages

end InductionStages

open InductionStages Langlands.LocalFactor.Archimedean

/-- An injective standard intertwiner between equal-rank lists extends through arbitrary
surrounding lists. -/
theorem RealInjectiveIntertwinerExists.in_stages {n r : ℕ} {ds es : List RealBlock}
    (hT : RealInjectiveIntertwinerExists r ds es)
    (pre post : List RealBlock) (hr : realRank ds = r) (he : realRank es = r)
    (hn : realRank (pre ++ ds ++ post) = n) :
    RealInjectiveIntertwinerExists n (pre ++ ds ++ post) (pre ++ es ++ post) := by
  obtain ⟨T, hi, hT⟩ := hT
  have hne : realRank (pre ++ es ++ post) = n := realRank_of_realRank_eq hr hn he
  have h : realRank pre + r ≤ n := by
    simp only [realRank_append'] at hn
    omega
  exact ⟨standardInd h rfl he hr hne hT, standardInd_injective h rfl he hr hne hT hi,
    standardInd_intertwiner h rfl he hr hne hT⟩

end Langlands.Archimedean
