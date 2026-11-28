import Langlands.BaseChange.TwistedCharacter.CyclicDescendedFourierVanishing
import Langlands.HarmonicAnalysis.UnitConjugation.InvariantExponentialDomain

/-! # Invariant exponential cutoff of the descended slice distribution -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis UnitConjugation MeasureTheory Set Metric Function _root_.Topology
open Hecke.TestFunction (pullback pullback_apply)

section Transport

variable {A : Type*} [NormedRing A] {C : Set A} (hC : IsClosed C)

local notation "q" => (fun x : C => NormedSpace.exp (x : A) - 1)

/-- Pull an additive-coordinate distribution back by `exp − 1` and extend it by zero
from its clopen domain. -/
def exponentialCutoffDistribution (he : IsOpenEmbedding q) (T : Distribution A) : Distribution A :=
  T.comp ((openEmbeddingTestExtension he).comp (SchwartzBruhat.restrictClosed hC))

private theorem exponentialCutoff_chart {K : Type*} [TopologicalSpace K]
    (he : IsOpenEmbedding q) (T : Distribution A) {i j : K → A}
    (hi : IsOpenEmbedding i) (hj : IsOpenEmbedding j) (hC₀ : ∀ k, i k ∈ C)
    (hEval : ∀ k, q ⟨i k, hC₀ k⟩ = j k) (g : SchwartzBruhat K) :
    exponentialCutoffDistribution hC he T (openEmbeddingTestExtension hi g) =
      T (openEmbeddingTestExtension hj g) := by
  apply congrArg T
  apply Hecke.TestFunction.ext
  intro y
  change openEmbeddingTestExtension he (SchwartzBruhat.restrictClosed hC (openEmbeddingTestExtension hi g)) y = _
  by_cases hy : y ∈ range q
  · obtain ⟨x, rfl⟩ := hy
    rw [openEmbeddingTestExtension_apply, SchwartzBruhat.restrictClosed_apply]
    by_cases hx : x.val ∈ range i
    · obtain ⟨k, hk⟩ := hx
      have h : q x = j k := (congrArg q (Subtype.ext hk)).symm.trans (hEval k)
      rw [← hk, openEmbeddingTestExtension_apply, h, openEmbeddingTestExtension_apply]
    · have hy' : q x ∉ range j := by
        rintro ⟨k, hk⟩
        exact hx ⟨k, congrArg Subtype.val (he.injective ((hEval k).trans hk))⟩
      rw [openEmbeddingTestExtension_apply_of_not_mem _ _ hx,
        openEmbeddingTestExtension_apply_of_not_mem _ _ hy']
  · have hy' : y ∉ range j := by
      rintro ⟨k, rfl⟩
      exact hy ⟨⟨i k, hC₀ k⟩, hEval k⟩
    rw [openEmbeddingTestExtension_apply_of_not_mem _ _ hy,
      openEmbeddingTestExtension_apply_of_not_mem _ _ hy']

variable {F : Type*} [NontriviallyNormedField F] [hComp : CompleteSpace F] [hChar : CharZero F]
  [hAlg : NormedAlgebra F A] [hFin : FiniteDimensional F A]

include hComp hChar hAlg hFin in
private theorem exp_sub_one_conjugation (u : Aˣ) (x : A) :
    NormedSpace.exp (conjugationHomeomorph u x) - 1 = conjugationHomeomorph u (NormedSpace.exp x - 1) := by
  let e : A ≃ₐ[F] A :=
    { conjugationLinearEquiv F u with
      map_mul' := fun _ _ => by simp [mul_assoc]
      commutes' := fun a => by
        change (u : A) * algebraMap F A a * ((u⁻¹ : Aˣ) : A) = algebraMap F A a
        rw [← Algebra.commutes a (u : A), mul_assoc, Units.mul_inv, mul_one] }
  exact (map_exp_sub_one e x).symm

include hComp hChar hAlg hFin in
private theorem exponentialCutoff_invariant (he : IsOpenEmbedding q) (T : Distribution A)
    (hT : IsConjugationInvariant T) (hCInv : ∀ (u : Aˣ) x, conjugationHomeomorph u x ∈ C ↔ x ∈ C) :
    IsConjugationInvariant (exponentialCutoffDistribution hC he T) := by
  apply (isConjugationInvariant_iff _).mpr
  intro u f
  let e := conjugationHomeomorph u
  let eC : C ≃ₜ C := e.subtype (fun x => (hCInv u x).symm)
  have hEq (x : C) : q (eC x) = e (q x) := exp_sub_one_conjugation (F := F) u x.val
  let Ext := openEmbeddingTestExtension he
  let Res := SchwartzBruhat.restrictClosed hC
  have hTest : Ext (Res (pullback e f)) = pullback e (Ext (Res f)) := by
    apply Hecke.TestFunction.ext
    intro y
    by_cases hy : y ∈ range q
    · obtain ⟨x, rfl⟩ := hy
      rw [show Ext (Res (pullback e f)) (q x) = Res (pullback e f) x from openEmbeddingTestExtension_apply he _ x,
        SchwartzBruhat.restrictClosed_apply, pullback_apply, pullback_apply, ← hEq,
        show Ext (Res f) (q (eC x)) = Res f (eC x) from openEmbeddingTestExtension_apply he _ (eC x),
        SchwartzBruhat.restrictClosed_apply]
      rfl
    · have hy' : e y ∉ range q := by
        rintro ⟨x, hx⟩
        exact hy ⟨eC.symm x, e.injective (by rw [← hEq, eC.apply_symm_apply, hx])⟩
      rw [pullback_apply]
      exact (openEmbeddingTestExtension_apply_of_not_mem he _ hy).trans
        (openEmbeddingTestExtension_apply_of_not_mem he _ hy').symm
  change T (Ext (Res (pullback e f))) = T (Ext (Res f))
  rw [hTest]
  exact (isConjugationInvariant_iff T).mp hT u _

end Transport

section Slice

variable {F A : Type*} [NontriviallyNormedField F] [ProperSpace F] [CharZero F]
  [NormedRing A] [NormedAlgebra F A] [CompleteSpace A] [FiniteDimensional F A] [IsUltrametricDist A]
  (α : A ≃ₐ[F] A)

local notation "S" => adjointFixedAlgebra α
local notation "U" => adjointConjugationDomain α

/-- The invariant cutoff of the descended distribution gives an invariant additive
distribution in exponential coordinates with both small-chart evaluation identities. -/
def AdjointExponentialCutoffStatement (C : Set S) (T₀ : Distribution S) (T : Distribution U) : Prop :=
  IsClopen C → (0 : S) ∈ C → C ⊆ U → IsConjugationInvariant T₀ →
  (∀ f : SchwartzBruhat U, support (f : U → ℂ) ⊆ Subtype.val ⁻¹' C →
    T₀ (SchwartzBruhat.extendZero (isOpen_adjointConjugationDomain α) f) = T f) →
  InvariantExponentialDomainStatement S →
  ∃ D : Distribution S, IsConjugationInvariant D ∧ AdjointExponentialTestAgreement α D T ∧
    letI : IsUltrametricDist S := IsUltrametricDist.subtype (fun x : A => x ∈ S)
    ∃ δ > (0 : ℝ), ∀ (t : ℝ) (ht : 0 < t) (ht₁ : t < 1), t ≤ δ →
      ∀ htU : closedBall (0 : S) t ⊆ U,
        ∀ E : closedBall (0 : S) t ≃ₜ normUnitCongruence (R := S) ht.le ht₁,
          (∀ x, ((E x).val : S) = NormedSpace.exp (x : S)) →
          ExponentialTraceChartAgreement (IsUltrametricDist.isOpen_closedBall (0 : S) ht.ne') E
            ((isOpen_adjointConjugationDomain α).isOpenEmbedding_subtypeVal.comp
              (isOpenEmbedding_adjointNormSlice α ht ht₁ htU)) D T₀

set_option maxHeartbeats 1600000 in
theorem adjointExponentialCutoff (C : Set S) (T₀ : Distribution S) (T : Distribution U) :
    AdjointExponentialCutoffStatement α C T₀ T := by
  intro hC h₀ hCU hInv hAgree hDomain
  obtain ⟨Ω, hΩ, hΩ₀, hΩinv, he⟩ := hDomain
  let D := exponentialCutoffDistribution hΩ.1 he T₀
  let : IsUltrametricDist S := IsUltrametricDist.subtype (fun x : A => x ∈ S)
  let hU := isOpen_adjointConjugationDomain α
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.mp ((hC.2.inter hΩ.2).mem_nhds ⟨h₀, hΩ₀⟩)
  have hδ (t : ℝ) (ht : t ≤ r / 2) : closedBall (0 : S) t ⊆ C ∩ Ω :=
    (closedBall_subset_ball (ht.trans_lt (half_lt_self hr))).trans hrB
  have hBoth (t : ℝ) (ht : 0 < t) (ht₁ : t < 1) (htδ : t ≤ r / 2)
      (htU : closedBall (0 : S) t ⊆ U)
      (E : closedBall (0 : S) t ≃ₜ normUnitCongruence (R := S) ht.le ht₁)
      (hE : ∀ x, ((E x).val : S) = NormedSpace.exp (x : S)) :
      ExponentialTraceChartAgreement (IsUltrametricDist.isOpen_closedBall (0 : S) ht.ne') E
        (isOpenEmbedding_adjointNormSlice α ht ht₁ htU) D T ∧
      ExponentialTraceChartAgreement (IsUltrametricDist.isOpen_closedBall (0 : S) ht.ne') E
        (hU.isOpenEmbedding_subtypeVal.comp (isOpenEmbedding_adjointNormSlice α ht ht₁ htU)) D T₀ := by
    let M := normUnitCongruence (R := S) ht.le ht₁
    let b := adjointNormSlice α ht ht₁ htU
    let hb := isOpenEmbedding_adjointNormSlice α ht ht₁ htU
    have hJ : IsOpenEmbedding ((Subtype.val : U → S) ∘ b) := hU.isOpenEmbedding_subtypeVal.comp hb
    have hI : IsOpenEmbedding ((Subtype.val : closedBall (0 : S) t → S) ∘ E.symm) :=
      (IsUltrametricDist.isOpen_closedBall (0 : S) ht.ne').isOpenEmbedding_subtypeVal.comp E.symm.isOpenEmbedding
    have hΩMem (k : M) : (E.symm k).val ∈ Ω := (hδ t htδ (E.symm k).property).2
    have hChart (k : M) : NormedSpace.exp ((E.symm k).val : S) - 1 = (b k).val := by
      have h := hE (E.symm k)
      rw [E.apply_symm_apply] at h
      exact congrArg (fun y : S => y - 1) h.symm
    have hValue (g : SchwartzBruhat M) : D (openEmbeddingTestExtension hI g) =
        T₀ (openEmbeddingTestExtension hJ g) :=
      exponentialCutoff_chart hΩ.1 he T₀ hI hJ hΩMem hChart g
    refine ⟨fun g => (hValue g).trans ?_, hValue⟩
    have hSupport : support (openEmbeddingTestExtension hb g : U → ℂ) ⊆ Subtype.val ⁻¹' C := by
      intro y hy
      have hR : y ∈ range b := by
        by_contra hn
        exact hy (openEmbeddingTestExtension_apply_of_not_mem hb g hn)
      obtain ⟨k, rfl⟩ := hR
      have hk : (b k).val ∈ closedBall (0 : S) t := by
        rw [mem_closedBall, dist_zero_right]
        exact k.property
      exact (hδ t htδ hk).1
    have hTest : openEmbeddingTestExtension hJ g = SchwartzBruhat.extendZero hU (openEmbeddingTestExtension hb g) := by
      apply Hecke.TestFunction.ext
      intro y
      by_cases hy : y ∈ range ((Subtype.val : U → S) ∘ b)
      · obtain ⟨k, rfl⟩ := hy
        exact (openEmbeddingTestExtension_apply hJ g k).trans (by
          rw [show ((Subtype.val : U → S) ∘ b) k = (b k).val from rfl,
            SchwartzBruhat.extendZero_apply_subtype, openEmbeddingTestExtension_apply])
      · rw [openEmbeddingTestExtension_apply_of_not_mem hJ g hy]
        by_cases hyU : y ∈ U
        · rw [SchwartzBruhat.extendZero_apply_of_mem hU _ hyU]
          symm
          exact openEmbeddingTestExtension_apply_of_not_mem hb g fun ⟨k, hk⟩ =>
            hy ⟨k, congrArg Subtype.val hk⟩
        · exact (SchwartzBruhat.extendZero_apply_of_not_mem hU _ hyU).symm
    rw [hTest, hAgree _ hSupport]
  refine ⟨D, exponentialCutoff_invariant (F := F) hΩ.1 he T₀ hInv hΩinv,
    ⟨r / 2, half_pos hr, fun t ht ht₁ htδ htU E hE => (hBoth t ht ht₁ htδ htU E hE).1⟩,
    r / 2, half_pos hr, fun t ht ht₁ htδ htU E hE => (hBoth t ht ht₁ htδ htU E hE).2⟩

end Slice

end Langlands.BaseChange
