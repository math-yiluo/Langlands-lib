import Langlands.HarmonicAnalysis.UnitConjugation.LatticeLevelOrbitExpansion
import Langlands.Representation.Category.Basic

/-! # Finite trace smoothing on small unit congruence subgroups -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory Metric Set

universe u v

local notation "L(" R "," h ")" => OpenAddSubgroup.toAddSubgroup
  (IsUltrametricDist.closedBall_openAddSubgroup R h)
local notation "K(" R "," h "," h' ")" => normUnitCongruence (R := R) (le_of_lt h) h'

/-- Exponential product straightening gives a finite compact orbit-character
expansion of every sufficiently small norm congruence indicator. -/
def NormUnitLevelTraceExpansionStatement (F : Type u) (R : Type v)
    [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F] [CharZero F]
    [NormedRing R] [NormedAlgebra F R] [IsUltrametricDist R] [ProperSpace R] [FiniteDimensional F R]
    [SecondCountableTopology R] [CompactOpenExhaustion R]
    [MeasurableSpace R] [BorelSpace R] [MeasurableSpace Rˣ] [BorelSpace Rˣ]
    {e : R → R → ℂ} (he : IsSelfDualBicharacter e) : Prop :=
  ExponentialProductStraighteningStatement F R →
  (∀ k : Rˣ, ∀ x z, e (conjugationHomeomorph k x) (conjugationHomeomorph k z) = e x z) →
  ∃ c : ℝ, ∃ hc : 1 ≤ c, ∃ ε > (0 : ℝ), max 1 ‖(1 : R)‖ * (c * ε) < 1 ∧
    ∀ (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) (hcr : c * r < 1), r ≤ ε →
    ∀ (s : ℝ) (hs : 0 < s) (hs₁ : s < 1),
      let L := L(R, hr)
      let N := L(R, hs)
      let K := K(R, hr, hr₁)
      let H := normUnitCongruence (R := R) (mul_nonneg (zero_le_one.trans hc) hr.le) hcr
      let M := unitCongruenceLevel (R := R) hr hr₁ hs hs₁
      ∃ (I : Type v) (S : Finset I) (z : I → R) (J : I → Finset (AddChar L ℂ))
        (τ : I → SmoothRep.{0, v, v} ℂ K) (n : ℕ), n ≠ 0 ∧
        (∀ i ∈ S, z i ∈ he.annihilator (N : Set R)) ∧
        (∀ i ∈ S, (J i : Set (AddChar L ℂ)) = latticeCharacterOrbit he L H (z i)) ∧
        (∀ i, FiniteDimensional ℂ (τ i)) ∧
        (∀ i ∈ S, ∀ (x : L) (k : K), (k.val : R) = NormedSpace.exp (x : R) →
          (τ i).representation.character k = ∑ χ ∈ J i, χ x) ∧
        ∀ k : K, (∑ i ∈ S, (τ i).representation.character k) =
          (M : Set K).indicator (fun _ => (n : ℂ)) k

variable {F : Type u} {R : Type v} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [CharZero F] [NormedRing R] [NormedAlgebra F R]
  [IsUltrametricDist R] [ProperSpace R] [FiniteDimensional F R]
  [SecondCountableTopology R] [CompactOpenExhaustion R]
  [MeasurableSpace R] [BorelSpace R] [MeasurableSpace Rˣ] [BorelSpace Rˣ]

theorem normUnitLevelTraceExpansion {e : R → R → ℂ} (he : IsSelfDualBicharacter e)
    (μ : Measure R) [μ.IsAddHaarMeasure] : NormUnitLevelTraceExpansionStatement F R he := by
  classical
  intro hStraighten hInv
  obtain ⟨c, hc, d₁, hd₁, hsmall, hOrbit⟩ := normUnitOrbitCharacter (F := F) he hStraighten hInv
  obtain ⟨d₂, hd₂, hChart⟩ := exponentialCongruenceHaar (F := F) (A := R)
  obtain ⟨d₃, hd₃, hIso⟩ := exponentialBallTransport (F := F) (A := R)
  let ε := min d₁ (min d₂ d₃)
  have hε₁ : ε ≤ d₁ := min_le_left _ _
  have hε₂ : ε ≤ d₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hε₃ : ε ≤ d₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hmono {a b : ℝ} (h : a ≤ b) :
      max 1 ‖(1 : R)‖ * (c * a) ≤ max 1 ‖(1 : R)‖ * (c * b) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (zero_le_one.trans hc))
      (zero_le_one.trans (le_max_left _ _))
  refine ⟨c, hc, ε, lt_min hd₁ (lt_min hd₂ hd₃), (hmono hε₁).trans_lt hsmall,
    fun r hr hr₁ hcr hrε s hs hs₁ => ?_⟩
  let L := L(R, hr)
  let N := L(R, hs)
  let K := K(R, hr, hr₁)
  let H := normUnitCongruence (R := R) (mul_nonneg (zero_le_one.trans hc) hr.le) hcr
  let M := unitCongruenceLevel (R := R) hr hr₁ hs hs₁
  have hrSmall : max 1 ‖(1 : R)‖ * (c * r) < 1 := (hmono (hrε.trans hε₁)).trans_lt hsmall
  have hstable {t : ℝ} (ht : 0 < t) (k : Rˣ) (hk : k ∈ H) (x : R)
      (hx : x ∈ L(R, ht)) : conjugationHomeomorph k x ∈ L(R, ht) := by
    change dist (conjugationHomeomorph k x) 0 ≤ t
    rw [dist_zero_right, norm_conjugation_eq_of_mem_normUnitCongruence _ hcr hrSmall hk]
    exact dist_zero_right x ▸ hx
  obtain ⟨I, S, z, J, n, hn, hz, hJ, hSum⟩ :=
    latticeLevelOrbitExpansion he L N H μ (isCompact_closedBall _ _)
      (IsUltrametricDist.isOpen_closedBall _ hs.ne') (isCompact_closedBall _ _)
      (hstable hr) (hstable hs) (fun k _ => hInv k)
  have hreps (i : I) : ∃ V : SmoothRep.{0, v, v} ℂ K, FiniteDimensional ℂ V ∧
      (i ∈ S → ∀ (x : L) (k : K), (k.val : R) = NormedSpace.exp (x : R) →
        V.representation.character k = ∑ χ ∈ J i, χ x) := by
    obtain ⟨S', hS', _, W, _, _, hW, ρ, hρ, hEval⟩ := hOrbit r hr hr₁ hcr (hrε.trans hε₁) (z i)
    refine ⟨SmoothRep.of ρ hρ, hW, fun hi x k hk => ?_⟩
    have hEq : S' = J i := Finset.coe_injective (hS'.trans (hJ i hi).symm)
    exact hEq ▸ hEval x k hk
  choose τ hτ using hreps
  refine ⟨I, S, z, J, τ, n, hn, hz, hJ, fun i => (hτ i).1,
    fun i hi => (hτ i).2 hi, ?_⟩
  obtain ⟨E, hE, _⟩ := hChart r hr hr₁ (hrε.trans hε₂)
  obtain ⟨Iso, hIso, _⟩ := hIso r hr (hrε.trans hε₃)
  let c₀ : closedBall (0 : R) r := ⟨0, mem_closedBall_self hr.le⟩
  have h0 : (Iso c₀ : R) = 0 := by rw [hIso, show (c₀ : R) = 0 from rfl, NormedSpace.exp_zero, sub_self]
  intro k
  obtain ⟨x, rfl⟩ := E.surjective k
  let xL : L := x
  have hMem : E x ∈ M ↔ x.val ∈ N := by
    have h := Iso.dist_eq x c₀
    change dist (Iso x : R) (Iso c₀ : R) = dist (x : R) 0 at h
    rw [hIso, h0, dist_zero_right] at h
    change ‖((E x).val : R) - 1‖ ≤ s ↔ dist (x : R) 0 ≤ s
    rw [hE, h]
  have hχ : (∑ i ∈ S, (τ i).representation.character (E x)) =
      ∑ i ∈ S, ∑ χ ∈ J i, χ xL :=
    Finset.sum_congr rfl fun i hi => (hτ i).2 hi xL (E x) (hE x)
  rw [hχ, hSum xL]
  by_cases hx : x.val ∈ N
  · rw [indicator_of_mem hx, indicator_of_mem (hMem.mpr hx)]
  · rw [indicator_of_notMem hx, indicator_of_notMem (mt hMem.mp hx)]

end Langlands.HarmonicAnalysis.UnitConjugation
