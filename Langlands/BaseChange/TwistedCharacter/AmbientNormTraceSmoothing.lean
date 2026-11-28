import Langlands.BaseChange.TwistedCharacter.CompactSemisimpleDescentPushforward
import Langlands.HarmonicAnalysis.UnitConjugation.NormUnitLevelTraceExpansion
import Langlands.Representation.Hecke.CommonInvarianceProof
import Langlands.Representation.Hecke.NormalizedIndicator

/-! # Smoothing ambient tests by compact norm-unit trace sums -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis UnitConjugation Set Function Filter
open _root_.Topology
open scoped _root_.Topology

universe u v w

variable {A : Type v} [NormedRing A] [IsUltrametricDist A]

/-- A positive norm congruence level as an open subgroup. -/
def normUnitOpenSubgroup {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) : OpenSubgroup Aˣ :=
  ⟨normUnitCongruence hr.le hr₁, isOpen_normUnitCongruence hr hr₁⟩

variable {H : Type w} [Group H] [TopologicalSpace H] (i : Aˣ →* H) (hi : IsOpenEmbedding i)

/-- The image of a positive norm congruence level is compact. -/
theorem isCompact_normUnitOpenSubgroupImage [ProperSpace A] {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    IsCompact (openSubgroupImage (normUnitOpenSubgroup hr hr₁) i hi : Set H) :=
  (isCompact_normUnitCongruence hr.le hr₁).image hi.continuous

section TraceSum

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

private theorem traceSum_smooths (ν : Measure G) [ν.IsHaarMeasure] (f : SchwartzBruhat G)
    (K J : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hJ : IsCompact (J : Set G)) (hJK : J ≤ K)
    (hf : ∀ j : J, ∀ g, f (g * j.val) = f g)
    {I : Type*} (S : Finset I) (τ : I → SmoothRep.{0, _, _} ℂ K)
    [∀ j, FiniteDimensional ℂ (τ j)] (n : ℕ) (hn : n ≠ 0)
    (hSum : ∀ k : K, ∑ j ∈ S, (τ j).representation.character k =
      (J : Set G).indicator (fun _ => (n : ℂ)) k.val) :
    let a : ℂ := (ν.real (J : Set G) : ℂ)⁻¹ / n
    Hecke.TestFunction.convolution ν f (∑ j ∈ S, a •
      Character.compactTraceCosetTest K hK (τ j).representation (τ j).isSmooth 1) = f := by
  classical
  intro a
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hTest : (∑ j ∈ S, a •
      Character.compactTraceCosetTest K hK (τ j).representation (τ j).isSmooth 1) =
      Hecke.HeckeAlgebra.normalizedIndicator ν J hJ := by
    apply Hecke.TestFunction.ext
    intro g
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Hecke.HeckeAlgebra.normalizedIndicator_apply, Character.compactTraceCosetTest,
      Hecke.TestFunction.leftTranslate_one]
    by_cases hg : g ∈ K
    · let k : K := ⟨g, hg⟩
      have he (j : I) : SchwartzBruhat.extendZero K.isOpen
          (Character.compactTraceTest (τ j).representation (τ j).isSmooth) g =
          (τ j).representation.character k := by
        rw [SchwartzBruhat.extendZero_apply_of_mem K.isOpen _ hg, Character.compactTraceTest_apply]
        rfl
      simp only [he, ← Finset.mul_sum, hSum]
      by_cases hj : g ∈ J
      · simp only [show k.val = g from rfl, indicator_of_mem hj, mul_one]
        exact div_mul_cancel₀ _ hn'
      · simp [show k.val = g from rfl, indicator_of_notMem hj]
    · have hnot : g ∉ J := fun hj => hg (hJK hj)
      simp [SchwartzBruhat.extendZero_apply_of_not_mem K.isOpen _ hg, indicator_of_notMem hnot]
  rw [hTest]
  exact Hecke.HeckeAlgebra.mul_normalizedIndicator_of_rightInvariant ν J hJ f hf

end TraceSum

variable {F : Type u} [NontriviallyNormedField F] [IsUltrametricDist F] [CharZero F]
  [NormedAlgebra F A] [ProperSpace A]
  [MeasurableSpace A] [MeasurableSpace Aˣ]
  [IsTopologicalGroup H] [T2Space H]
  [MeasurableSpace H]

local notation "L(" h ")" => OpenAddSubgroup.toAddSubgroup
  (IsUltrametricDist.closedBall_openAddSubgroup A h)

/-- Norm congruence character sums smooth every ambient test on the right,
with the same frequency orbits as on the norm-unit subgroup. -/
def AmbientNormTraceSmoothingStatement {e : A → A → ℂ} (he : IsSelfDualBicharacter e)
    (ν : Measure H) [ν.IsHaarMeasure] [CompleteSpace F] [FiniteDimensional F A]
    [SecondCountableTopology A] [CompactOpenExhaustion A] [BorelSpace A] [BorelSpace Aˣ]
    [LocallyCompactSpace H] [TotallyDisconnectedSpace H] [BorelSpace H] : Prop :=
  ExponentialProductStraighteningStatement F A →
  (∀ k : Aˣ, ∀ x z, e (conjugationHomeomorph k x) (conjugationHomeomorph k z) = e x z) →
  ∃ c : ℝ, ∃ hc : 1 ≤ c, ∃ ε > (0 : ℝ), max 1 ‖(1 : A)‖ * (c * ε) < 1 ∧
    ∀ (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) (hcr : c * r < 1), r ≤ ε →
      let K := normUnitOpenSubgroup (A := A) hr hr₁
      let K' := openSubgroupImage K i hi
      let hK' := isCompact_normUnitOpenSubgroupImage i hi hr hr₁
      let E := openSubgroupImageEquiv K i hi
      let B := normUnitCongruence (R := A) (mul_nonneg (zero_le_one.trans hc) hr.le) hcr
      ∀ f : SchwartzBruhat H,
        ∃ (s : ℝ) (hs : 0 < s), s < 1 ∧
        ∃ (I : Type v) (S : Finset I) (z : I → A) (J : I → Finset (AddChar L(hr) ℂ))
          (τ : I → SmoothRep.{0, w, v} ℂ K') (hFD : ∀ j, FiniteDimensional ℂ (τ j)) (a : ℂ),
          (∀ j ∈ S, z j ∈ he.annihilator (L(hs) : Set A)) ∧
          (∀ j ∈ S, (J j : Set (AddChar L(hr) ℂ)) = latticeCharacterOrbit he L(hr) B (z j)) ∧
          (∀ j ∈ S, ∀ (x : L(hr)) (k : K), (k.val : A) = NormedSpace.exp (x : A) →
            (τ j).representation.character (E k) = ∑ χ ∈ J j, χ x) ∧
          letI : ∀ j, FiniteDimensional ℂ (τ j) := hFD
          Hecke.TestFunction.convolution ν f (∑ j ∈ S, a •
            Character.compactTraceCosetTest K' hK' (τ j).representation (τ j).isSmooth 1) = f

theorem ambientNormTraceSmoothing {e : A → A → ℂ} (he : IsSelfDualBicharacter e)
    (μ : Measure A) [μ.IsAddHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    [CompleteSpace F] [FiniteDimensional F A] [SecondCountableTopology A] [CompactOpenExhaustion A]
    [BorelSpace A] [BorelSpace Aˣ] [LocallyCompactSpace H] [TotallyDisconnectedSpace H] [BorelSpace H] :
    AmbientNormTraceSmoothingStatement (F := F) i hi he ν := by
  classical
  intro hStraighten hInv
  obtain ⟨c, hc, ε, hε, hsmall, hExpansion⟩ := normUnitLevelTraceExpansion (F := F) he μ hStraighten hInv
  refine ⟨c, hc, ε, hε, hsmall, fun r hr hr₁ hcr hεr => ?_⟩
  let K := normUnitOpenSubgroup (A := A) hr hr₁
  let K' := openSubgroupImage K i hi
  let hK' := isCompact_normUnitOpenSubgroupImage i hi hr hr₁
  let E := openSubgroupImageEquiv K i hi
  change ∀ f : SchwartzBruhat H, _
  intro f
  obtain ⟨U, _, _, hU⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance H {f} K'
  have hfU := (hU f (Finset.mem_singleton_self f)).2
  have hIn : i ⁻¹' (U : Set H) ∈ 𝓝 (1 : Aˣ) := hi.continuous.continuousAt.preimage_mem_nhds
    (by simpa only [map_one] using U.mem_nhds_one)
  obtain ⟨s, hs, hs₁, hsU⟩ := exists_normUnitCongruence_subset hIn
  let N := normUnitOpenSubgroup (A := A) hs hs₁
  let J₀ := openSubgroupImage (K ⊓ N) i hi
  have hJ₀c : IsCompact (J₀ : Set H) := by
    change IsCompact (i '' ((K : Set Aˣ) ∩ (N : Set Aˣ)))
    exact ((isCompact_normUnitCongruence hr.le hr₁).inter_right N.isClosed).image hi.continuous
  have hJ₀K : J₀ ≤ K' := fun _ ⟨k, hk, hEq⟩ => ⟨k, hk.1, hEq⟩
  have hJ₀U : J₀ ≤ U := by
    rintro _ ⟨k, hk, rfl⟩
    exact hsU hk.2
  obtain ⟨I, S, z, J, τ, n, hn, hz, hOrbit, hFD, hEval, hSum⟩ := hExpansion r hr hr₁ hcr hεr s hs hs₁
  let τ' (j : I) : SmoothRep.{0, w, v} ℂ K' := SmoothRep.of
    ((τ j).representation.comp E.symm.toMonoidHom)
    (isSmooth_comp E.symm.toMonoidHom E.symm.continuous (τ j).isSmooth)
  let hFD' (j : I) : FiniteDimensional ℂ (τ' j) := hFD j
  let : ∀ j, FiniteDimensional ℂ (τ' j) := hFD'
  let a : ℂ := (ν.real (J₀ : Set H) : ℂ)⁻¹ / n
  have hChar (j : I) (k : K') : (τ' j).representation.character k =
      (τ j).representation.character (E.symm k) := rfl
  refine ⟨s, hs, hs₁, I, S, z, J, τ', hFD', a, hz, hOrbit, ?_, ?_⟩
  · intro j hj x k hk
    rw [hChar, E.symm_apply_apply]
    exact hEval j hj x k hk
  have hMem (k : K') : E.symm k ∈ unitCongruenceLevel hr hr₁ hs hs₁ ↔ k.val ∈ J₀ := by
    constructor
    · intro hk
      exact ⟨(E.symm k).val, ⟨(E.symm k).property, hk⟩,
        congrArg Subtype.val (E.apply_symm_apply k)⟩
    · rintro ⟨g, hg, heq⟩
      have he : E ⟨g, hg.1⟩ = k := Subtype.ext heq
      rw [← he, E.symm_apply_apply]
      exact hg.2
  have hSum' (k : K') : ∑ j ∈ S, (τ' j).representation.character k =
      (J₀ : Set H).indicator (fun _ => (n : ℂ)) k.val := by
    simp only [hChar]
    refine (hSum (E.symm k)).trans ?_
    by_cases hk : k.val ∈ J₀
    · rw [indicator_of_mem hk, indicator_of_mem ((hMem k).mpr hk)]
    · rw [indicator_of_notMem hk, indicator_of_notMem (mt (hMem k).mp hk)]
  exact traceSum_smooths ν f K' J₀ hK' hJ₀c hJ₀K
    (fun j g => hfU ⟨j.val, hJ₀U j.property⟩ g) S τ' n hn hSum'

end Langlands.BaseChange
