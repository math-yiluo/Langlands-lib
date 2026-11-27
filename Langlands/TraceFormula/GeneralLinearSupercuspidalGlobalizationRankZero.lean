import Langlands.TraceFormula.GeneralLinearSupercuspidalGlobalizationStatement
import Langlands.Automorphic.GeneralLinearParabolicCuspidalComparisonProof
import Langlands.Analysis.OperatorTraceFiniteCompression
import Langlands.TraceFormula.IsotypicTrace.OccurrenceReduction

/-! # Rank zero in supercuspidal globalization for `GL_n` -/

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

local instance globalizationRankZeroIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance globalizationRankZeroSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
/-- The `GL_n` group scheme over `K`, for the bound variables `K` and `n`. -/
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Cusp" => fullAEL2CuspidalSubmodule K GLₙ hPD hG T i hi I e hc

private theorem project_const_integral {A H : Type*} [MeasurableSpace A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ν : Measure A)
    (P : Submodule ℂ H) [CompleteSpace P] (c : ℂ) (z : P) :
    P.orthogonalProjectionOnto (∫ _ : A, c • (z : H) ∂ν) =
      (((ν Set.univ).toReal : ℂ) * c) • z := by
  rw [integral_const, ← Complex.coe_smul, smul_smul, map_smul,
    P.orthogonalProjectionOnto_mem_subspace_eq_self]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in
/-- The full globalization conclusion for the trivial group scheme `GL_0`. -/
theorem generalLinearSupercuspidalGlobalization_rankZero :
  ∀ (K : Type u) [Field K] [NumberField K],
    let n : ℕ := 0
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
        (∃ Tv : V v →ₗ[ℂ] P, Tv ≠ 0 ∧ ∀ g y, (Tv (ρ g y) : S) = πc (incl v g) (Tv y)) ∧
        ∀ (μv : Measure (GeneralLinear n (v.adicCompletion K))) [μv.IsHaarMeasure]
          (ν : Measure (AdelicGroupPoints K GLₙ)) [ν.IsHaarMeasure],
          ∃ (hρ : IsAdmissible ρ) (C : (AdelicGroupPoints K GLₙ → ℂ) → ℂ),
            ∀ (fv : SchwartzBruhat (GeneralLinear n (v.adicCompletion K)))
              (fw : AdelicGroupPoints K GLₙ → ℂ),
              (∀ g x, fw (g * ofPlace K GLₙ (.inr v) x) = fw g) →
              ∀ hf : Integrable (fun g => fv (eᵥ v (atPlace K GLₙ (.inr v) g)) * fw g) ν,
                let RPf : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                  fullAEL2CuspidalIntegratedAction K GLₙ hPD hG T i hi I e hc ν _ hf ∘L
                    P.subtypeL
                IsTraceClass (E := (P : Submodule ℂ S)) RPf →
                  operatorTrace (E := (P : Submodule ℂ S)) RPf =
                    Character.distribution μv ρ hρ fv * C fw := by
  classical
  intro K _ _ n hPD hG T i hi _ I _ e hc _ _ _ _ _ Sc _ vaux _ V _ _ π hπ
  dsimp only
  let A := AdelicGroupPoints K GLₙ
  let Q := PositiveRationalQuotient K GLₙ T i
  let μQ := positiveRationalQuotientHaarMeasure K GLₙ T i
  let πc := fullAEL2CuspidalBoundedRightAction K GLₙ hPD hG T i hi I e hc
  have matrix_subsingleton (R : Type u) [CommRing R] : Subsingleton (GeneralLinear n R) :=
    ⟨fun a b => Units.ext (Matrix.ext fun j _ => Fin.elim0 j)⟩
  let : Subsingleton A :=
    ⟨fun a b => (GeneralLinearGroupPoints.adelicHomeomorph K n).injective
      ((matrix_subsingleton _).elim _ _)⟩
  have h_action (a : A) (x : Cusp) : πc a x = x := by
    rw [Subsingleton.elim a 1, map_one]
    rfl
  let : Subsingleton Q :=
    ⟨fun a b => Quotient.inductionOn₂ a b fun x y => congrArg _ (Subsingleton.elim x y)⟩
  let : Finite Q := Finite.of_subsingleton
  let : CompactSpace Q := Finite.compactSpace
  let : IsLocallyFiniteMeasure μQ :=
    positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure K GLₙ T i hi I e hc
  let : IsFiniteMeasure μQ := ⟨isCompact_univ.measure_lt_top⟩
  have hμ : μQ ≠ 0 := positiveRationalQuotientHaarMeasure_ne_zero K GLₙ T i hi I e hc
  let hconst : MemLp (fun _ : Q => (1 : ℂ)) 2 μQ := memLp_const _
  let φ := hconst.toLp (fun _ : Q => (1 : ℂ))
  have hφ : φ ≠ 0 := by
    intro heq
    have h := hconst.coeFn_toLp
    change (φ : Q → ℂ) =ᵐ[μQ] (fun _ => 1) at h
    rw [heq] at h
    have hzero := (Lp.coeFn_zero ℂ 2 μQ).symm.trans h
    have hf : ∀ᵐ _ : Q ∂μQ, False := hzero.mono fun _ h' => zero_ne_one h'
    let : (ae μQ).NeBot := ae_neBot.mpr hμ
    exact (Filter.Eventually.exists hf).elim fun _ h => h
  have hφc : φ ∈ Cusp := by
    rw [mem_fullAEL2CuspidalSubmodule]
    intro p
    obtain ⟨_, _, ⟨j, _⟩, _⟩ := exists_properRationalParabolicRadicals_eq_comap hPD hG p
    exact Fin.elim0 j
  let x : Cusp := ⟨φ, hφc⟩
  have hx : x ≠ 0 := fun h => hφ (congrArg Subtype.val h)
  let : NormedAddCommGroup Cusp := Submodule.normedAddCommGroup Cusp
  let : InnerProductSpace ℂ Cusp := Submodule.innerProductSpace Cusp
  let P : Submodule ℂ Cusp := ℂ ∙ x
  let : NormedAddCommGroup P := Submodule.normedAddCommGroup P
  let : InnerProductSpace ℂ P := Submodule.innerProductSpace P
  have hxP : x ∈ P := Submodule.mem_span_singleton_self x
  let : FiniteDimensional ℂ P := FiniteDimensional.span_singleton ℂ x
  let : CompleteSpace P := P.closed_of_finiteDimensional.completeSpace_coe
  have hP : P ≠ ⊥ := Submodule.span_singleton_eq_bot.not.mpr hx
  refine ⟨P, inferInstance, hP, fun a z hz => (h_action a z).symm ▸ hz, ?_,
    ⟨x, hxP, hx, fun _ _ _ _ _ => h_action _ _⟩, ?_⟩
  · intro W hWP _ _
    by_cases hW : W = ⊥
    · exact Or.inl hW
    · suffices x ∈ W by exact Or.inr (hWP.antisymm ((Submodule.span_singleton_le_iff_mem x W).mpr this))
      obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hWP hz)
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hz0 (by simpa using hc.symm)
      have hcz : c • x ∈ W := hc.symm ▸ hz
      have h := W.smul_mem c⁻¹ hcz
      rw [← mul_smul, inv_mul_cancel₀ hc0, one_smul] at h
      exact h
  · intro v hv
    let := matrix_subsingleton (v.adicCompletion K)
    have hπirr := (hπ v hv).1
    have hπadm := (hπ v hv).2.1
    refine ⟨1, fun _ _ => rfl, ?_⟩
    let ρ := Langlands.twist ((1 : (v.adicCompletion K)ˣ →* ℂˣ).comp
      GeneralLinear.determinant) (π v)
    have hρ_id (g : GeneralLinear n (v.adicCompletion K)) (y : V v) : ρ g y = y := by
      rw [Subsingleton.elim g 1, map_one]
      rfl
    have hρeq : ρ = π v := by
      ext g y
      rw [hρ_id, Subsingleton.elim g 1, map_one]
      rfl
    obtain ⟨y, hy⟩ := IsotypicTrace.exists_ne_zero_of_isIrreducible (π v) hπirr
    have hspan : (ℂ ∙ y : Submodule ℂ (V v)) = ⊤ := by
      let W : Subrepresentation (π v) :=
        { toSubmodule := ℂ ∙ y
          apply_mem_toSubmodule := fun g z hz => by
            rw [Subsingleton.elim g 1, map_one]
            exact hz }
      rcases hπirr.eq_bot_or_eq_top W with hW | hW
      · exact (hy (Submodule.span_singleton_eq_bot.mp
          (congrArg Subrepresentation.toSubmodule hW))).elim
      · exact congrArg Subrepresentation.toSubmodule hW
    let : FiniteDimensional ℂ (V v) := by
      let : FiniteDimensional ℂ (ℂ ∙ y : Submodule ℂ (V v)) := FiniteDimensional.span_singleton ℂ y
      exact FiniteDimensional.of_surjective (ℂ ∙ y : Submodule ℂ (V v)).subtype
        (fun z => ⟨⟨z, hspan.symm ▸ Submodule.mem_top⟩, rfl⟩)
    have hd : Module.finrank ℂ (V v) = 1 := by
      rw [← finrank_top, ← hspan, finrank_span_singleton hy]
    let : Module.Free ℂ P := Module.Free.of_divisionRing ℂ P
    let E : V v ≃ₗ[ℂ] P := LinearEquiv.ofFinrankEq _ _
      (hd.trans (finrank_span_singleton hx).symm)
    have hρadm : IsAdmissible ρ := hρeq.symm ▸ hπadm
    refine ⟨⟨E.toLinearMap, ?_, fun g z => by rw [hρ_id, h_action]⟩, ?_⟩
    · intro h
      have hEy : E y = 0 := by
        simpa only [LinearEquiv.coe_coe, LinearMap.zero_apply] using LinearMap.congr_fun h y
      exact hy (E.injective (hEy.trans (map_zero E).symm))
    intro μv _ ν _
    let m : ℂ := (μv Set.univ).toReal
    let M : ℂ := (ν Set.univ).toReal
    let : Finite (GeneralLinear n (v.adicCompletion K)) := Finite.of_subsingleton
    let : CompactSpace (GeneralLinear n (v.adicCompletion K)) := Finite.compactSpace
    have hm : m ≠ 0 := Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
      ⟨(isOpen_univ.measure_pos μv Set.univ_nonempty).ne', isCompact_univ.measure_lt_top.ne⟩)
    let idP : P →L[ℂ] P := ContinuousLinearMap.id ℂ P
    refine ⟨hρadm, fun fw => M * fw 1 * operatorTrace (E := P) idP / m, ?_⟩
    intro fv fw _ hf _
    have hlocal : Hecke.integratedAction μv ρ hρadm.1 fv =
        (m * fv 1) • (LinearMap.id : Module.End ℂ (V v)) := by
      ext1 z
      rw [Hecke.integratedAction_eq_sum_of_presentation μv ρ hρadm.1 fv z
        ({()} : Finset Unit) (fun _ => Set.univ) (fun _ => fv 1 • z)
        (fun _ _ => MeasurableSet.univ) (fun _ _ _ => isCompact_univ.measure_lt_top)]
      · simp [m, smul_smul]
      · intro g
        simp [Subsingleton.elim g 1]
    have hchar : Character.distribution μv ρ hρadm fv = m * fv 1 := by
      rw [Character.distribution_eq_subspace μv ρ hρadm fv ⊤ le_top]
      have htop : FiniteRankEnd.onSubspace (Hecke.integratedAction μv ρ hρadm.1 fv)
          (⊤ : Submodule ℂ (V v)) le_top = (m * fv 1) • LinearMap.id := by
        ext1 z
        apply Subtype.ext
        change Hecke.integratedAction μv ρ hρadm.1 fv z = (m * fv 1) • (z : V v)
        simp [hlocal]
      rw [htop, map_smul, LinearMap.trace_id, finrank_top, hd]
      simp
    have hglobal : P.orthogonalProjectionOnto ∘L
        fullAEL2CuspidalIntegratedAction K GLₙ hPD hG T i hi I e hc ν _ hf ∘L P.subtypeL =
          (M * (fv 1 * fw 1)) • idP := by
      ext1 z
      change P.orthogonalProjectionOnto
        (fullAEL2CuspidalIntegratedAction K GLₙ hPD hG T i hi I e hc ν _ hf (z : Cusp)) = _
      rw [fullAEL2CuspidalIntegratedAction_apply]
      have heq (a : A) :
          (fv ((GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
            (placeCompletion K (.inr v))) (atPlace K GLₙ (.inr v) a)) * fw a) •
            fullAEL2CuspidalRightAction K GLₙ hPD hG T i hi I e hc a (z : Cusp) =
          (fv 1 * fw 1) • (z : Cusp) := by
        have hpr : (GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
            (placeCompletion K (.inr v))) (atPlace K GLₙ (.inr v) a) = 1 :=
          Subsingleton.elim _ _
        have hact : fullAEL2CuspidalRightAction K GLₙ hPD hG T i hi I e hc a (z : Cusp) =
            (z : Cusp) := h_action a z
        rw [hpr, congrArg fw (Subsingleton.elim a 1), hact]
      trans P.orthogonalProjectionOnto (∫ _ : A, (fv 1 * fw 1) • (z : Cusp) ∂ν)
      · exact congrArg P.orthogonalProjectionOnto
          (integral_congr_ae («μ» := ν) (Filter.Eventually.of_forall heq))
      · exact project_const_integral ν P (fv 1 * fw 1) z
    calc
      operatorTrace _ = (M * (fv 1 * fw 1)) * operatorTrace idP :=
        (congrArg (operatorTrace (E := P)) hglobal).trans
          (operatorTrace_smul _ _ (isTraceClass_of_finiteDimensional idP))
      _ = _ := by
        change _ = Character.distribution μv ρ hρadm fv * (M * fw 1 * operatorTrace idP / m)
        rw [hchar]
        field_simp [hm]

end Langlands.TraceFormula
