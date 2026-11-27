import Langlands.TraceFormula.GeneralLinearSupercuspidalGlobalizationRankZero
import Langlands.TraceFormula.IsotypicTrace.CuspidalOccurrenceReduction
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Twist.SubquotientProof

/-! # Reduction of `GL_n` supercuspidal globalization to local occurrence -/

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis

namespace Langlands.TraceFormula

local instance globalizationReductionIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance globalizationReductionSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The `GL_n` group scheme over `K`, for the bound variables `K` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

section CharacterTransport

variable {H J : Type*} [Group H] [Group J] [TopologicalSpace H] [TopologicalSpace J]
  [IsTopologicalGroup H] [IsTopologicalGroup J] [MeasurableSpace H] [MeasurableSpace J]
  [BorelSpace H] [BorelSpace J] [T2Space H] [T2Space J] [LocallyCompactSpace H]
  [LocallyCompactSpace J] [TotallyDisconnectedSpace H] [TotallyDisconnectedSpace J]
  {V : Type w} [AddCommGroup V] [Module ℂ V]

/-- Pullback of the distribution character along a Haar-preserving group homeomorphism. -/
private theorem distribution_pullback (E : H ≃ₜ* J) (μH : Measure H) (μJ : Measure J)
    [μH.IsHaarMeasure] [μJ.IsHaarMeasure] (hE : MeasurePreserving E μH μJ)
    (ρ : Representation ℂ J V) (hρ : IsAdmissible ρ)
    (hρH : IsAdmissible (ρ.comp E.toMonoidHom)) (f : SchwartzBruhat J) :
    Character.distribution μH (ρ.comp E.toMonoidHom) hρH
        (Hecke.TestFunction.pullback E.toHomeomorph f) =
      Character.distribution μJ ρ hρ f := by
  apply congrArg FiniteRankEnd.trace
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  change (Hecke.integratedAction μH (ρ.comp E.toMonoidHom) hρH.1
    (Hecke.TestFunction.pullback E.toHomeomorph f)) x = Hecke.integratedAction μJ ρ hρ.1 f x
  rw [Hecke.integratedAction_apply, Hecke.integratedAction_apply]
  have heq : ((Hecke.actionIntegrand ρ hρ.1 f x).comp E hE.measurable) =
      Hecke.actionIntegrand (ρ.comp E.toMonoidHom) hρH.1
        (Hecke.TestFunction.pullback E.toHomeomorph f) x := by
    ext g
    rfl
  rw [← heq]
  exact AlgebraicIntegral.integral_comp_measurePreserving _ _ hE

end CharacterTransport

/-- An unramified determinant twist has open kernel at a finite completion. -/
private theorem isOpen_unramifiedDeterminant_ker (K : Type u) [Field K] [NumberField K]
    (n : ℕ) (v : Langlands.Global.FinitePlace K) (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (hχ : ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 → χ t = 1) :
    IsOpen ((χ.comp (GeneralLinear.determinant (R := v.adicCompletion K) (n := n))).ker :
      Set (GeneralLinear n (v.adicCompletion K))) := by
  let d : GeneralLinear n (v.adicCompletion K) → v.adicCompletion K := fun g =>
    (GeneralLinear.determinant g : v.adicCompletion K)
  have hd : Continuous d := Units.continuous_val.matrix_det
  have hd1 : d 1 = 1 := by simp [d]
  have hN : {x : v.adicCompletion K | Valued.v x = 1} ∈ nhds (1 : v.adicCompletion K) := by
    simpa only [map_one] using (Valued.locally_const (x := (1 : v.adicCompletion K)) (by simp))
  rw [← hd1] at hN
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  apply Filter.mem_of_superset (hd.continuousAt.preimage_mem_nhds hN)
  intro g hg
  exact hχ (GeneralLinear.determinant g) hg

/-- Simultaneous occurrence in positive rank, with a common vector at the prescribed level. -/
def GeneralLinearSupercuspidalPositiveRankOccurrenceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ), 0 < n →
    ∀ (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive GLₙ)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ GLₙ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup K GLₙ)).IsMulRightInvariant]
    [∀ v : Langlands.Global.FinitePlace K,
      MeasurableSpace (GeneralLinear n (v.adicCompletion K))]
    [∀ v : Langlands.Global.FinitePlace K, BorelSpace (GeneralLinear n (v.adicCompletion K))]
    [∀ v : Langlands.Global.FinitePlace K,
      LocallyCompactSpace (GeneralLinear n (v.adicCompletion K))]
    [∀ v : Langlands.Global.FinitePlace K,
      TotallyDisconnectedSpace (GeneralLinear n (v.adicCompletion K))]
    (Sc : Finset (Langlands.Global.FinitePlace K)), Sc.Nonempty →
    ∀ (vaux : Langlands.Global.FinitePlace K), vaux ∉ Sc →
    ∀ (V : Langlands.Global.FinitePlace K → Type w) [∀ v, AddCommGroup (V v)]
      [∀ v, Module ℂ (V v)]
      (π : ∀ v : Langlands.Global.FinitePlace K,
        Representation ℂ (GeneralLinear n (v.adicCompletion K)) (V v)),
      (∀ v ∈ Sc, (π v).IsIrreducible ∧ GeneralLinear.IsSupercuspidal (π v)) →
    let S := fullAEL2CuspidalSubmodule K GLₙ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction K GLₙ hPD hG T i hi I e hc
    let eᵥ : ∀ v : Langlands.Global.FinitePlace K,
        PlaceGroupPoints K GLₙ (.inr v) ≃ₜ* GeneralLinear n (v.adicCompletion K) := fun v =>
      GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
        (placeCompletion K (.inr v))
    let incl : ∀ v : Langlands.Global.FinitePlace K,
        GeneralLinear n (v.adicCompletion K) →* AdelicGroupPoints K GLₙ := fun v =>
      (ofPlace K GLₙ (.inr v)).comp (eᵥ v).symm.toMulEquiv.toMonoidHom
    ∃ (P : Submodule ℂ S) (_ : CompleteSpace P), P ≠ ⊥ ∧
      (∀ (a : AdelicGroupPoints K GLₙ), ∀ x ∈ P, πc a x ∈ P) ∧
      (∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ (a : AdelicGroupPoints K GLₙ), ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) ∧
      (∃ x ∈ P, x ≠ 0 ∧ ∀ w : Langlands.Global.FinitePlace K, w ∉ Sc → w ≠ vaux →
        ∀ k ∈ FiniteAdelicGL.localIntegral K n w, πc (incl w k) x = x) ∧
      ∀ v ∈ Sc, ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
        (∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 → χ t = 1) ∧
        let ρ := Langlands.twist (χ.comp GeneralLinear.determinant) (π v)
        ∃ Tv : V v →ₗ[ℂ] P, Tv ≠ 0 ∧ ∀ g y, (Tv (ρ g y) : S) = πc (incl v g) (Tv y)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3500000 in
/-- Simultaneous occurrence gives globalization with every trace identity in the statement. -/
theorem generalLinearSupercuspidalGlobalization_of_positiveRankOccurrence
    (hOccurrence : GeneralLinearSupercuspidalPositiveRankOccurrenceStatement.{u, w}) :
    GeneralLinearSupercuspidalGlobalizationStatement.{u, w} := by
  intro K _ _ n
  cases n with
  | zero => exact generalLinearSupercuspidalGlobalization_rankZero K
  | succ n =>
    intro hPD hG T i hi _ I _ e hc _ _ _ _ _ Sc hSc vaux hvaux V _ _ π hπ
    obtain ⟨P, hPcomplete, hP0, hPinv, hPirr, hx, hTv⟩ :=
      hOccurrence K (n + 1) n.succ_pos hPD hG T i hi I e hc Sc hSc vaux hvaux V π hπ
    let := hPcomplete
    refine ⟨P, hPcomplete, hP0, hPinv, hPirr, hx, ?_⟩
    intro v hv
    obtain ⟨χ, hχ, Tv, hTv0, hTveq⟩ := hTv v hv
    refine ⟨χ, hχ, ⟨Tv, hTv0, hTveq⟩, ?_⟩
    intro μv _ ν _
    let G := GroupScheme.GeneralLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)
    let S := fullAEL2CuspidalSubmodule K G hPD hG T i hi I e hc
    let eᵥ : PlaceGroupPoints K G (.inr v) ≃ₜ* GeneralLinear (n + 1) (v.adicCompletion K) :=
      GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin (n + 1)) (CommRingCat.of K)
        (placeCompletion K (.inr v))
    let L := χ.comp (GeneralLinear.determinant (n := n + 1))
    let ρ := Langlands.twist L (π v)
    have hρ : IsAdmissible ρ := (isAdmissible_twist_iff L (π v)
      (isOpen_unramifiedDeterminant_ker K (n + 1) v χ hχ)).mpr (hπ v hv).2.1
    have hρirr : ρ.IsIrreducible := (isIrreducible_twist_iff L (π v)).mpr (hπ v hv).1
    let : TotallyDisconnectedSpace (PlaceGroupPoints K G (.inr v)) :=
      eᵥ.symm.toHomeomorph.totallyDisconnectedSpace
    let μGv : Measure (PlaceGroupPoints K G (.inr v)) := Measure.map eᵥ.symm μv
    let : μGv.IsHaarMeasure := eᵥ.symm.isHaarMeasure_map μv
    have heᵥ : MeasurePreserving eᵥ μGv μv :=
      ⟨eᵥ.continuous.measurable, MeasurableEquiv.map_map_symm eᵥ.toHomeomorph.toMeasurableEquiv⟩
    let ρGv : Representation ℂ (PlaceGroupPoints K G (.inr v)) (V v) :=
      ρ.comp eᵥ.toMonoidHom
    have hρGv : IsAdmissible ρGv := isAdmissible_comp_continuousMulEquiv ρ eᵥ hρ
    have hρGvirr : ρGv.IsIrreducible :=
      (CuspidalSupport.isIrreducible_comp_mulEquiv_iff ρ eᵥ.toMulEquiv).mpr hρirr
    let j : V v →ₗ[ℂ] S := P.subtype.comp Tv
    have hj0 : j ≠ 0 := by
      intro h
      apply hTv0
      exact LinearMap.ext fun y => Subtype.ext (LinearMap.congr_fun h y)
    have hjP : LinearMap.range j ≤ P := by
      rintro _ ⟨y, rfl⟩
      exact (Tv y).property
    have hjeq (y : PlaceGroupPoints K G (.inr v)) (x : V v) :
        j (ρGv y x) = fullAEL2CuspidalBoundedRightAction K G hPD hG T i hi I e hc
          (ofPlace K G (.inr v) y) (j x) := by
      have hy := hTveq (eᵥ y) x
      change j (ρGv y x) = fullAEL2CuspidalBoundedRightAction K G hPD hG T i hi I e hc
        (ofPlace K G (.inr v) (eᵥ.symm (eᵥ y))) (j x) at hy
      simpa only [eᵥ.symm_apply_apply] using hy
    obtain ⟨_, ⟨C, hC⟩, _⟩ := IsotypicTrace.cuspidalIsotypicTraceFactorization_of_occurrence K G v
      hPD hG T i hi I e hc μGv ν P hPinv hPirr ρGv hρGv hρGvirr j hj0 hjP hjeq
    refine ⟨hρ, C, ?_⟩
    intro fv fw hfw hf RPf htc
    let fGv := Hecke.TestFunction.pullback eᵥ.toHomeomorph fv
    have htrace := hC fGv fw hfw hf htc
    have hcval := distribution_pullback eᵥ μGv μv heᵥ ρ hρ hρGv fv
    exact htrace.trans (congrArg (fun z => z * C fw) hcval)

end Langlands.TraceFormula
