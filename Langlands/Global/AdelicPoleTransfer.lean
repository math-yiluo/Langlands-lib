import Langlands.Global.AdelicTaylorPoleDetection
import Langlands.Analysis.SeveralComplex.HolomorphicSliceDivision
import Langlands.Analysis.Meromorphic.ScalarIdentity
import Langlands.Global.AdelicLeviConstantTermPairing
import Langlands.Global.AdelicCuspidalPairingDetection

/-! # Local uniform pole transfer from tests on automorphic forms -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry Filter Metric Set
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global Langlands.GroupScheme Langlands.Analysis Langlands.Analysis.Meromorphic

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : IsClosedSubgroup rho)
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "𝔉" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "value" => UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hN hrho R L

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Present a growth-valued family on the agreement domain by a common scalar
denominator and a weakly holomorphic numerator. -/
def HasHolomorphicNumerator (U D : Set E) (f num : E → 𝔉) (den : E → ℂ) : Prop :=
  DifferentiableOn ℂ den U ∧ (∃ s ∈ U, den s ≠ 0) ∧
    (∀ test : 𝔉 →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => test (num s)) U) ∧
    ∀ s ∈ U ∩ D, den s • f s = num s

/-- Suppose a weakly holomorphic family on an open agreement set takes automorphic
values and has a weakly holomorphic numerator with one scalar denominator. If its
tests separating automorphic vectors extend holomorphically, then all continuous
scalar evaluations extend holomorphically on one common neighborhood. -/
theorem exists_uniform_holomorphic_evaluations_of_automorphic_tests
    (K : Subgroup (InfiniteAdelicGroupPoints F G)) (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    {U D : Set E} (hU : IsOpen U) (hUc : IsPreconnected U) (hD : IsOpen D) {s₀ : E} (hs₀ : s₀ ∈ U)
    {f num : E → 𝔉} {den : E → ℂ}
    (hnum : HasHolomorphicNumerator F G rho hsmooth hcalc hN hrho R L U D f num den)
    (hf : ∀ test : 𝔉 →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => test (f s)) (U ∩ D))
    (hauto : ∀ s ∈ U ∩ D, IsAutomorphicFunctionOn F G hsmooth hcalc
      (AdelicGroupPoints.rationalSubgroup F G) K rho (value (num s)))
    {κ : Type*} (obs : κ → 𝔉 →L[ℂ] ℂ)
    (hdetect : ∀ v : 𝔉, IsAutomorphicFunctionOn F G hsmooth hcalc
      (AdelicGroupPoints.rationalSubgroup F G) K rho (value v) → (∀ i, obs i v = 0) → v = 0)
    (hobs : ∀ i, ∃ b : E → ℂ, DifferentiableOn ℂ b U ∧
      EqOn b (fun s => obs i (f s)) (U ∩ D)) :
    ∃ V ⊆ U, IsOpen V ∧ s₀ ∈ V ∧ ∀ test : 𝔉 →L[ℂ] ℂ,
      ∃ b : E → ℂ, DifferentiableOn ℂ b V ∧ EqOn b (fun s => test (f s)) (V ∩ D) := by
  obtain ⟨hd, ⟨y, hy, hyne⟩, hn, heq⟩ := hnum
  have hnonzero (s : E) (hs : s ∈ U) : ¬ den =ᶠ[𝓝 s] 0 := by
    intro hz
    have hm : U ∩ {t | den t = 0} ∈ 𝓝 s := inter_mem (hU.mem_nhds hs) hz
    obtain ⟨A, hA, hAo, hsA⟩ := _root_.mem_nhds_iff.mp hm
    exact hyne (differentiableOn_eqOn_zero_of_isPreconnected hd hU hUc hAo
      (hA.trans inter_subset_left) ⟨s, hsA⟩ (fun x hx => (hA hx).2) hy)
  obtain ⟨u, r, V, hVo, hsV, hVU, hr, hr2, hline, hcircle⟩ :=
    exists_open_division_circle hU hs₀ hd (hnonzero s₀ hs₀)
  have h0 : (0 : ℂ) ∈ ball 0 2 := mem_ball_self (by norm_num)
  have hsr : (r : ℂ) ∈ sphere 0 r := by simp [hr.le]
  have hbr : (r : ℂ) ∈ ball 0 2 := mem_ball.mpr ((mem_sphere.mp hsr).trans_lt hr2)
  have hdiv (s : E) (hs : s ∈ V ∩ D) (test : 𝔉 →L[ℂ] ℂ) (z : ℂ) (hz : z ∈ ball 0 2) :
      AnalyticallyDividesAt (fun t : ℂ => den (s + t • u))
        (fun t : ℂ => test (num (s + t • u))) z := by
    let line (t : ℂ) := s + t • u
    have hlined : Differentiable ℂ line := by fun_prop
    let B := ball (0 : ℂ) 2
    let A := B ∩ line ⁻¹' D
    have hAo : IsOpen A := isOpen_ball.inter (hD.preimage hlined.continuous)
    have hAB : A ⊆ B := inter_subset_left
    have h0A : (0 : ℂ) ∈ A := ⟨h0, by simpa [line] using hs.2⟩
    have hmap : MapsTo line B U := hline s hs.1
    have hmapA : MapsTo line A (U ∩ D) := fun _ ht => ⟨hmap ht.1, ht.2⟩
    have hnd (ξ : 𝔉 →L[ℂ] ℂ) : DifferentiableOn ℂ (fun t => ξ (num (line t))) B :=
      (hn ξ).comp hlined.differentiableOn hmap
    have hdd : DifferentiableOn ℂ (den ∘ line) B := hd.comp hlined.differentiableOn hmap
    have hda : AnalyticOnNhd ℂ (den ∘ line) B := hdd.analyticOnNhd isOpen_ball
    have hdn : analyticOrderAt (den ∘ line) z ≠ ⊤ :=
      hda.analyticOrderAt_ne_top_of_isPreconnected (convex_ball (0 : ℂ) 2).isPreconnected hbr hz
        ((hda r hbr).analyticOrderAt_eq_zero.mpr (hcircle s hs.1 r hsr) ▸ ENat.zero_ne_top)
    apply analyticallyDividesAt_of_automorphic_tests F G rho hsmooth hcalc hN hrho R L K hL
      (convex_ball (0 : ℂ) 2).isPreconnected isOpen_ball hAo hAB ⟨0, h0A⟩
      (num ∘ line) hnd (fun t ht => hauto (line t) (hmapA ht)) obs hdetect ⟨z, hz⟩
      (den ∘ line) (hda z hz) hdn _ test
    intro i
    obtain ⟨b, hb, hbeq⟩ := hobs i
    have hbd : DifferentiableOn ℂ (b ∘ line) B := hb.comp hlined.differentiableOn hmap
    let q (t : ℂ) := obs i (num (line t)) - den (line t) * b (line t)
    have hqd : DifferentiableOn ℂ q B := (hnd (obs i)).sub (hdd.mul hbd)
    have hqA : EqOn q 0 A := by
      intro t ht
      change obs i (num (line t)) - den (line t) * b (line t) = 0
      have hb' : b (line t) = obs i (f (line t)) := hbeq (hmapA ht)
      rw [hb', ← heq (line t) (hmapA ht), map_smul, smul_eq_mul, sub_self]
    have hqB := differentiableOn_eqOn_zero_of_isPreconnected hqd isOpen_ball
      (convex_ball (0 : ℂ) 2).isPreconnected hAo hAB ⟨0, h0A⟩ hqA
    refine ⟨b ∘ line, hbd.analyticOnNhd isOpen_ball z hz, ?_⟩
    filter_upwards [isOpen_ball.mem_nhds hz] with t ht
    exact sub_eq_zero.mp (hqB ht)
  refine ⟨V, hVU, hVo, hsV, fun test => ?_⟩
  let b := circleDivision den (fun s => test (num s)) u r
  have hb : DifferentiableOn ℂ b V := differentiableOn_circleDivision hU hd (hn test) u hr
    (fun s hs z hz => ⟨hline s hs (mem_ball.mpr ((mem_sphere.mp hz).trans_lt hr2)),
      hcircle s hs z hz⟩)
  have hmul (s : E) (hs : s ∈ V ∩ D) : den s * b s = den s * test (f s) := by
    change den s * circleDivision den (fun t => test (num t)) u r s = den s * test (f s)
    calc
      _ = test (num s) := mul_circleDivision_eq (num := fun t => test (num t))
        hd u s hr hr2 (hline s hs.1)
        (hcircle s hs.1) (fun z hz => hdiv s hs test z hz)
      _ = _ := by rw [← heq s ⟨hVU hs.1, hs.2⟩, map_smul, smul_eq_mul]
  refine ⟨b, hb, fun s hs => ?_⟩
  have hbAt := (hb.differentiableAt (hVo.mem_nhds hs.1)).continuousAt
  have hfAt := ((hf test).differentiableAt ((hU.inter hD).mem_nhds ⟨hVU hs.1, hs.2⟩)).continuousAt
  by_contra hne
  apply hnonzero s (hVU hs.1)
  have hne' := (hbAt.ne_iff_eventually_ne hfAt).mp hne
  filter_upwards [(hVo.inter hD).mem_nhds hs, hne'] with t ht htne
  exact by_contradiction fun hdt => htne (mul_left_cancel₀ hdt (hmul t ht))

section CuspidalTests

open AdelicGroupPoints StandardParabolicFamily

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G))

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Kinf" => Subgroup.comap (ContinuousMonoidHom.toMonoidHom (ofInfinite F G)) K

/-- Transfer holomorphy of the actual norm-one cuspidal pairings to every adelic
evaluation, on one neighborhood. Leading cuspidal injectivity and the weighted
test majorants are the hypotheses used for separation. -/
theorem exists_uniform_holomorphic_evaluations_of_cuspidal_pairings
    (hinj : LeadingCuspidalInjectivityStatement.{u})
    (hK : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J : Idx, IsMaximalCompactSubgroup F (𝓕.M J)
      (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom))
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    {U D : Set E} (hU : IsOpen U) (hUc : IsPreconnected U) (hD : IsOpen D) {s₀ : E} (hs₀ : s₀ ∈ U)
    {f num : E → 𝔉} {den : E → ℂ}
    (hnum : HasHolomorphicNumerator F G rho hsmooth hcalc hN hrho R L U D f num den)
    (hf : ∀ test : 𝔉 →L[ℂ] ℂ, DifferentiableOn ℂ (fun s => test (f s)) (U ∩ D))
    (hauto : ∀ s ∈ U ∩ D, IsAutomorphicFunctionOn F G hsmooth hcalc
      (rationalSubgroup F G) Kinf rho (value (num s)))
    (hweight : ∀ (J : Idx) ψ, 𝓕.IsLeviCuspForm Kinf rho J ψ → ∀ g,
      𝓕.HasLeviPairingMajorant J ψ g rho R)
    (hpair : ∀ (J : Idx) ψ, 𝓕.IsLeviCuspForm Kinf rho J ψ → ∀ g,
      ∃ b : E → ℂ, DifferentiableOn ℂ b U ∧
        EqOn b (fun s => 𝓕.leviPairing J (𝓕.constantTerm J (value (f s))) g ψ) (U ∩ D)) :
    ∃ V ⊆ U, IsOpen V ∧ s₀ ∈ V ∧ ∀ g : AdelicGroupPoints F G,
      ∃ b : E → ℂ, DifferentiableOn ℂ b V ∧ EqOn b (fun s => value (f s) g) (V ∩ D) := by
  let I := Σ J : Idx, {ψ : AdelicGroupPoints F (𝓕.M J) → ℂ // 𝓕.IsLeviCuspForm Kinf rho J ψ} ×
    AdelicGroupPoints F G
  let obs : I → 𝔉 →L[ℂ] ℂ := fun ⟨J, ⟨ψ, hψ⟩, g⟩ =>
    𝓕.constantTermLeviPairingCLM J ψ hψ.1.1 g rho hN hrho hsmooth hcalc R L hψ.1.2.1.1
      (hweight J ψ hψ g)
  have hdet (v : 𝔉) (hv : IsAutomorphicFunctionOn F G hsmooth hcalc
      (rationalSubgroup F G) Kinf rho (value v)) (hz : ∀ i, obs i v = 0) : v = 0 := by
    have hzero : 𝓕.HasVanishingCuspidalPairings Kinf rho (value v) := by
      intro J ψ hψ g
      obtain ⟨C, hC⟩ := 𝓕.exists_leviPairing_constantTerm_bound J ψ hψ.1.1 g rho hN hrho
        hsmooth hcalc R L hψ.1.2.1.1 (hweight J ψ hψ g)
      refine ⟨(hC v).1, ?_⟩
      simpa only [obs, constantTermLeviPairingCLM_apply] using hz ⟨J, ⟨ψ, hψ⟩, g⟩
    exact toFun_injective F G rho hsmooth hcalc hN hrho R L
      (𝓕.eq_zero_of_hasVanishingCuspidalPairings hinj K hK hKmin hKlevi rho hsmooth hrho hv hzero)
  have hobs (i : I) : ∃ b : E → ℂ, DifferentiableOn ℂ b U ∧
      EqOn b (fun s => obs i (f s)) (U ∩ D) := by
    obtain ⟨J, ⟨ψ, hψ⟩, g⟩ := i
    simpa only [obs, constantTermLeviPairingCLM_apply] using hpair J ψ hψ g
  obtain ⟨V, hVU, hV, hsV, htests⟩ :=
    exists_uniform_holomorphic_evaluations_of_automorphic_tests F G rho hsmooth hcalc hN hrho R L
      Kinf hL hU hUc hD hs₀ hnum hf hauto obs hdet hobs
  refine ⟨V, hVU, hV, hsV, fun g => ?_⟩
  obtain ⟨b, hb, hbeq⟩ := htests (differentialEvaluation F G rho hsmooth hcalc hN hrho R L 1 g)
  refine ⟨b, hb, fun s hs => ?_⟩
  have he : b s = differentialEvaluation F G rho hsmooth hcalc hN hrho R L 1 g (f s) := hbeq hs
  rw [he, differentialEvaluation_apply, map_one, Module.End.one_apply]
  rfl

end CuspidalTests

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace
