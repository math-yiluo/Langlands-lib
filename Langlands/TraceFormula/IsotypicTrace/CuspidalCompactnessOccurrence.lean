import Langlands.TraceFormula.IsotypicTrace.CompactFixedSpaceOccurrence
import Langlands.TraceFormula.IsotypicTrace.CuspidalOccurrenceReduction
import Langlands.Representation.Unitary.CompactIsometricAverage
import Langlands.Representation.Unitary.RightHaarHermitianApproximationProof
import Langlands.Analysis.Local.HaarInversionDensityProof
import Langlands.Analysis.Local.ModularCharacterContinuity
import Langlands.Representation.Hecke.NormalizedIndicator

/-! # Local occurrence from compact adelic convolution -/

noncomputable section

universe u uE

open AlgebraicGeometry CategoryTheory MeasureTheory NumberField Filter
open scoped CategoryTheory.MonObj CompactlySupported Topology NNReal ENNReal
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.HarmonicAnalysis
open Langlands.Analysis

namespace Langlands.TraceFormula.IsotypicTrace

section Local

variable {J : Type u} [Group J] [TopologicalSpace J] [IsTopologicalGroup J] [T2Space J]
  [LocallyCompactSpace J] [TotallyDisconnectedSpace J] [SecondCountableTopology J]
  [MeasurableSpace J] [BorelSpace J]
  {H : Type uE} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (σ : J →* (H →L[ℂ] H))
  (hnorm : ∀ g x, ‖σ g x‖ = ‖x‖) (hcont : ∀ x, Continuous fun g => σ g x)

include hnorm hcont in
private theorem exists_nonzero_fixed (x : H) (hx : x ≠ 0) :
    ∃ (K : OpenSubgroup J), IsCompact (K : Set J) ∧
      ∃ z : fixedVectors (toRepresentation σ) K.toSubgroup, (z : H) ≠ 0 := by
  let U := {g : J | ‖σ g x - x‖ < ‖x‖ / 2}
  have hUo : IsOpen U := isOpen_lt ((hcont x).sub continuous_const).norm continuous_const
  have hU : U ∈ 𝓝 (1 : J) := hUo.mem_nhds (by
    change ‖σ 1 x - x‖ < ‖x‖ / 2
    simpa only [map_one, one_apply_eq_self, sub_self, norm_zero] using half_pos (norm_pos_iff.mpr hx))
  obtain ⟨K, hKc, hKU⟩ := ((Topology.LocallyProfiniteProof.vanDantzig J).mp
    Topology.isLocallyProfinite_of_mathlib).2 U hU
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let : SecondCountableTopology K := inferInstanceAs (SecondCountableTopology ↥(K : Set J))
  let τ := σ.comp K.toSubgroup.subtype
  have hτn (k : K) (y : H) : ‖τ k y‖ = ‖y‖ := hnorm k y
  have hτc (y : H) : Continuous fun k : K => τ k y := (hcont y).comp continuous_subtype_val
  let z := compactIsometricAverage K τ hτn hτc x
  have hzfix : z ∈ fixedVectors (toRepresentation σ) K.toSubgroup := fun k =>
    compactIsometricAverage_fixed K τ hτn hτc k x
  refine ⟨K, hKc, ⟨z, hzfix⟩, ?_⟩
  have hbound : ‖z - x‖ ≤ ‖x‖ / 2 := by
    let νK := compactProbabilityHaar K
    have hconst : (∫ _ : K, x ∂νK) = x := by
      rw [integral_const, probReal_univ, one_smul]
    have hdiff : z - x = ∫ k : K, (τ k x - x) ∂νK := by
      calc
        z - x = (∫ k : K, τ k x ∂νK) - ∫ _ : K, x ∂νK := by
          rw [hconst]
          exact congrArg (fun y : H => y - x) (compactIsometricAverage_apply K τ hτn hτc x)
        _ = _ := (integral_sub (compactIsometricOrbit_integrable K τ hτn hτc x)
          (integrable_const x)).symm
    rw [hdiff]
    have hnormIntegral : ‖∫ k : K, (τ k x - x) ∂νK‖ ≤ (‖x‖ / 2) * νK.real Set.univ :=
      (norm_integral_le_of_norm_le_const (C := ‖x‖ / 2)
        (f := fun k : K => τ k x - x) (.of_forall fun k => le_of_lt (hKU k.property)))
    simpa only [probReal_univ, mul_one] using hnormIntegral
  intro hz
  change z = 0 at hz
  rw [hz, zero_sub, norm_neg] at hbound
  exact (not_le_of_gt (half_lt_self (norm_pos_iff.mpr hx))) hbound

end Local

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (v : Langlands.Global.FinitePlace F)
  [MeasurableSpace (PlaceGroupPoints F G (Sum.inr v))]
  [BorelSpace (PlaceGroupPoints F G (Sum.inr v))]
  [LocallyCompactSpace (PlaceGroupPoints F G (Sum.inr v))]
  [TotallyDisconnectedSpace (PlaceGroupPoints F G (Sum.inr v))]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local notation "Gv" => PlaceGroupPoints F G (Sum.inr v)
local notation "H" => awaySubgroup F G v
local notation "A" => AdelicGroupPoints F G

/-- Compact integrated operators for the adelic action give an irreducible admissible local
representation in each nonzero complete invariant subspace. -/
theorem exists_localOccurrence_of_compactIntegrated
    (π : A →* (E →L[ℂ] E)) (hπn : ∀ a x, ‖π a x‖ = ‖x‖)
    (hπc : ∀ x, Continuous fun a => π a x)
    (hcompact : ∀ (f : C_c(A, ℂ)) (hf : Integrable f Measure.haar),
      IsCompactOperator (integratedIsometricAction Measure.haar π hπn
        (fun x => (hπc x).aestronglyMeasurable) f hf))
    (P : Submodule ℂ E) [CompleteSpace P] (hPn : P ≠ ⊥)
    (hP : ∀ a, ∀ x ∈ P, π a x ∈ P) :
    ∃ (V : Type uE) (_ : AddCommGroup V) (_ : Module ℂ V)
      (ρ : Representation ℂ Gv V) (_ : IsAdmissible ρ),
      ρ.IsIrreducible ∧ ∃ j₀ : V →ₗ[ℂ] E, j₀ ≠ 0 ∧ LinearMap.range j₀ ≤ P ∧
        ∀ y x, j₀ (ρ y x) = π (ofPlace F G (Sum.inr v) y) (j₀ x) := by
  classical
  let D := placeSplitting F G v
  let πP := restrictAction π P hP
  let σ := πP.comp (ofPlace F G (Sum.inr v))
  let τ := πP.comp (awaySubgroup F G v).subtype
  have hσn (y : Gv) (x : P) : ‖σ y x‖ = ‖x‖ := hπn _ x
  have hσc (x : P) : Continuous fun y : Gv => σ y x :=
    (restrict_continuous F G π hπc P hP x).comp (continuous_ofPlace F G _)
  have hτi (h : H) (x y : P) : inner ℂ (τ h x) (τ h y) = inner ℂ x y :=
    (LinearMap.norm_map_iff_inner_map_map (τ h)).mp (fun z => hπn _ z) x y
  have hτc (x : P) : Continuous fun h : H => τ h x :=
    (restrict_continuous F G π hπc P hP x).comp continuous_subtype_val
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPn
  obtain ⟨K₀, hK₀, z, hz⟩ := exists_nonzero_fixed σ hσn hσc ⟨x, hxP⟩
    (fun h => hx0 (congrArg Subtype.val h))
  let μv : Measure Gv := Measure.haar
  let ν : Measure A := Measure.haar
  obtain ⟨μH, hμH, hsplit⟩ := exists_awayHaar F G v μv ν
  obtain ⟨f, hf, hfprop, -, hsymm, htend, -⟩ := rightHaarHermitianApproximation μH τ hτi hτc
  let Tn (n : ℕ) : P →L[ℂ] P := integratedIsometricAction μH.inv τ (fun h x => hπn h x)
    (fun x => (hτc x).stronglyMeasurable.aestronglyMeasurable)
    (fun h => (f n h : ℂ)) (hf n).ofReal
  have hn : ∃ n, Tn n z ≠ 0 := by
    by_contra! hall
    have hlim : Tendsto (fun _ : ℕ => (0 : P)) atTop (𝓝 (z : P)) := by
      have ht : Tendsto (fun n => Tn n z) atTop (𝓝 (z : P)) := htend z
      simpa only [hall] using ht
    exact hz (tendsto_nhds_unique hlim tendsto_const_nhds)
  obtain ⟨n, hn⟩ := hn
  let B := Tn n
  let b : C_c(H, ℂ) :=
    { toFun := fun h => (((Measure.modularCharacter h : ℝ≥0) : ℝ) : ℂ) * (f n h : ℂ)
      continuous_toFun :=
        (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
          Langlands.Haar.continuous_modularCharacter_of_locallyCompact)).mul
          (Complex.continuous_ofReal.comp (hfprop n).1)
      hasCompactSupport' := ((hfprop n).2.1.comp_left Complex.ofReal_zero).mul_left }
  let bw : A → ℂ := b ∘ Prod.snd ∘ D.symm
  have hbwH (h : H) : bw h = b h := by
    have he : D (1, h) = (h : A) := by simp [D]
    change b (D.symm (h : A)).2 = b h
    rw [← he, D.symm_apply_apply]
  have hbint : Integrable b μH := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  have hbwint : Integrable (fun h : H => bw h) μH := hbint.congr (.of_forall fun h => (hbwH h).symm)
  have hB (x : P) : B x = awayAction F G v π hπn hπc P hP μH bw x := by
    rw [awayAction_apply F G v π hπn hπc P hP μH bw hbwint]
    change (∫ h, (f n h : ℂ) • πP h x ∂μH.inv) = _
    rw [(Langlands.Haar.haarInversionDensity H μH).1, integral_withDensity_eq_integral_smul
      Langlands.Haar.continuous_modularCharacter_of_locallyCompact.measurable]
    apply integral_congr_ae
    filter_upwards [] with h
    rw [hbwH h]
    change ((Measure.modularCharacter h : ℝ≥0) : ℝ) • ((f n h : ℂ) • πP h x) =
      ((((Measure.modularCharacter h : ℝ≥0) : ℝ) : ℂ) * (f n h : ℂ)) • πP h x
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    rfl
  have hcomm (y : Gv) (x : P) : B (σ y x) = σ y (B x) := by
    rw [hB, hB]
    exact awayAction_commute F G v π hπn hπc P hP μH bw y x
  have hBw (a : A) (y : Gv) : bw (a * ofPlace F G (Sum.inr v) y) = bw a := by
    have hy : D (y, 1) = ofPlace F G (Sum.inr v) y := by simp [D]
    change b (D.symm (a * ofPlace F G (Sum.inr v) y)).2 = b (D.symm a).2
    rw [← hy, map_mul, D.symm_apply_apply]
    simp
  have hBcompact (K : OpenSubgroup Gv) (hK : IsCompact (K : Set Gv)) :
      IsCompactOperator (B.comp (fixedVectors (toRepresentation σ) K.toSubgroup).subtypeL) := by
    let fv := Hecke.TestFunction.subgroupIndicator K hK
    have hf0 : fv ≠ 0 := by
      intro h
      have := congrArg (fun f : SchwartzBruhat Gv => f 1) h
      simp [fv] at this
    let bp (p : Gv × H) := fv p.1 * b p.2
    have hbpc : Continuous bp := (fv.locallyConstant.continuous.comp continuous_fst).mul
      (b.continuous.comp continuous_snd)
    have hbps : HasCompactSupport bp := by
      refine (fv.hasCompactSupport.prod b.hasCompactSupport).of_isClosed_subset isClosed_closure ?_
      refine closure_minimal ?_ (isClosed_closure.prod isClosed_closure)
      intro p hp
      have hp' : fv p.1 * b p.2 ≠ 0 := hp
      exact ⟨subset_closure fun h => hp' (by rw [show fv p.1 = 0 from h, zero_mul]),
        subset_closure fun h => hp' (by rw [show b p.2 = 0 from h, mul_zero])⟩
    let w : C_c(A, ℂ) :=
      ⟨⟨bp ∘ D.symm, hbpc.comp D.symm.continuous⟩,
        hbps.comp_homeomorph D.symm.toHomeomorph⟩
    have hwint : Integrable w ν := w.continuous.integrable_of_hasCompactSupport w.hasCompactSupport
    let R := integratedIsometricAction ν π hπn (fun x => (hπc x).aestronglyMeasurable) w hwint
    have hR (x : E) : R x = ∫ a, (fv (atPlace F G (Sum.inr v) a) * bw a) • π a x ∂ν := rfl
    obtain ⟨L, hL, hRL⟩ := compression_split_eq F G v π hπn hπc P hP μv μH ν hsplit
      fv bw hBw hwint hf0 R hR
    have hcomp : IsCompactOperator (L.comp B) := by
      have hr : IsCompactOperator R := hcompact w hwint
      have hproj := (hr.comp_clm P.subtypeL).clm_comp P.orthogonalProjectionOnto
      have hBA : B = awayAction F G v π hπn hπc P hP μH bw := by
        exact ContinuousLinearMap.ext hB
      rw [hBA]
      exact hRL ▸ hproj
    let WK := fixedVectors (toRepresentation σ) K.toSubgroup
    have hrestrict : (L.comp B).comp WK.subtypeL = μv.real (K : Set Gv) • (B.comp WK.subtypeL) := by
      ext1 q
      change L (B (q : P)) = μv.real (K : Set Gv) • B (q : P)
      rw [hL]
      have heq (y : Gv) : fv y • σ y (B (q : P)) = (K : Set Gv).indicator (fun _ => B (q : P)) y := by
        by_cases hy : y ∈ K
        · have hq : σ y (q : P) = q := q.property ⟨y, hy⟩
          simp only [fv, Hecke.TestFunction.subgroupIndicator_apply, Set.indicator_of_mem hy,
            one_smul, ← hcomm, hq]
        · simp [fv, hy]
      change (∫ y, fv y • σ y (B (q : P)) ∂μv) = _
      simp_rw [heq, integral_indicator K.isOpen.measurableSet, setIntegral_const]
    have hcc : IsCompactOperator ((L.comp B).comp WK.subtypeL) :=
      hcomp.comp_clm WK.subtypeL
    rw [hrestrict] at hcc
    exact (IsCompactOperator.smul_iff₀ (Hecke.HeckeAlgebra.compactOpen_mass_pos μv K hK).ne').mp hcc
  have hσi (y : Gv) (x z : P) : inner ℂ (σ y x) (σ y z) = inner ℂ x z :=
    (LinearMap.norm_map_iff_inner_map_map (σ y)).mp (hσn y) x z
  obtain ⟨V, _, _, ρ, hρ, hirr, j, hj⟩ := exists_irreducible_of_compactOnFixedSpaces
    σ hσi B (hsymm n).1 hcomm hBcompact K₀ hK₀ z hn
  let j₀ := P.subtype.comp j.toLinearMap
  refine ⟨V, inferInstance, inferInstance, ρ, hρ, hirr, j₀, ?_, ?_, ?_⟩
  · intro h0
    obtain ⟨w, hw⟩ := FiniteIndexRestriction.exists_ne_zero ρ hirr
    have hw0 : (j w : E) = 0 := congrArg (fun f : V →ₗ[ℂ] E => f w) h0
    apply hw
    apply hj
    rw [map_zero]
    exact Subtype.ext hw0
  · rintro _ ⟨w, rfl⟩
    exact (j w).property
  · intro y x
    exact congrArg (fun p : P => (p : E)) (Representation.IntertwiningMap.isIntertwining ρ (toRepresentation σ) j y x)

end Langlands.TraceFormula.IsotypicTrace
