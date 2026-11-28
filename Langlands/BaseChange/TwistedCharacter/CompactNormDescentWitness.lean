import Langlands.BaseChange.TwistedCharacter.AmbientNormTraceSmoothing
import Langlands.Representation.Character.CompactTraceSelfIntertwining
import Langlands.Representation.Character.SeparationProof

/-! # Compact trace witnesses for a normalized semisimple descent -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis UnitConjugation Character
  Set Function Metric _root_.Topology
open scoped _root_.Topology

universe u v w uW

section Level

variable {A H W : Type*} [NormedRing A] [IsUltrametricDist A] [CompleteSpace A]
  [Group H] [TopologicalSpace H] [AddCommGroup W] [Module ℂ W]

/-- Arbitrarily small ambient norm levels have nonzero fixed vectors in a
smooth irreducible representation. -/
theorem exists_fixedVector_normUnitOpenSubgroupImage (i : Aˣ →* H) (hi : IsOpenEmbedding i)
    (π : Representation ℂ H W) (hπ : IsSmooth π) (hirr : π.IsIrreducible)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℝ) (hr : 0 < r) (hr₁ : r < 1), r ≤ ε ∧
      fixedVectors π (openSubgroupImage (normUnitOpenSubgroup hr hr₁) i hi).toSubgroup ≠ ⊥ := by
  let : Nontrivial W := CharacterSeparation.nontrivial_of_isIrreducible hirr
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨U, hU⟩ := hπ w
  have hV : i ⁻¹' (U : Set H) ∈ 𝓝 (1 : Aˣ) := hi.continuous.continuousAt.preimage_mem_nhds
    (by simpa only [map_one] using U.mem_nhds_one)
  obtain ⟨s, hs, hs₁, hsU⟩ := exists_normUnitCongruence_subset hV
  let r := min s ε
  have hr : 0 < r := lt_min hs hε
  have hr₁ : r < 1 := (min_le_left _ _).trans_lt hs₁
  refine ⟨r, hr, hr₁, min_le_right _ _, fun h => hw ?_⟩
  have hwJ : w ∈ fixedVectors π (openSubgroupImage (normUnitOpenSubgroup hr hr₁) i hi).toSubgroup := by
    rintro ⟨_, ⟨g, hg, rfl⟩⟩
    have hg' : ‖(g : A) - 1‖ ≤ r := hg
    exact hU ⟨i g, hsU (hg'.trans (min_le_left _ _))⟩
  rw [h] at hwJ
  simpa only [Submodule.mem_bot] using hwJ

end Level

section Descent

variable {F : Type u} {A : Type v} {H : Type w} {W : Type uW}
  [NontriviallyNormedField F] [ProperSpace F] [IsUltrametricDist F] [CharZero F]
  [NormedRing A] [NormedAlgebra F A] [CompleteSpace A] [ProperSpace A]
  [FiniteDimensional F A] [IsUltrametricDist A]
  [MeasurableSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [MeasurableSpace H] [BorelSpace H]
  [AddCommGroup W] [Module ℂ W]
  (α : A ≃ₐ[F] A) (i : Aˣ →* H) (hi : IsOpenEmbedding i) (s : H)

local notation "S" => adjointFixedAlgebra α
local notation "U" => adjointConjugationDomain α
local instance : IsUltrametricDist S := IsUltrametricDist.subtype (fun x : A => x ∈ S)
local instance : ProperSpace S := FiniteDimensional.proper F S

variable [MeasurableSpace (adjointFixedAlgebra α)] [MeasurableSpace (adjointFixedAlgebra α)ˣ]
  (ν : Measure H) [ν.IsHaarMeasure]
  (ρ : Measure (adjointFixedAlgebra α))
  (π : Representation ℂ H W) (hπ : IsAdmissible π)

local notation "L(" h ")" => OpenAddSubgroup.toAddSubgroup
  (IsUltrametricDist.closedBall_openAddSubgroup A h)
local notation "j" => translatedCosetEmbedding i s
local notation "hj" => isOpenEmbedding_translatedCoset i hi s
local notation "D" => Character.distribution ν π hπ

/-- A nonzero compact trace on the slice produces an ambient orbit type with
slice intertwining, self-intertwining, and a fixed vector at a conjugated level. -/
def CompactNormDescentWitnessStatement {e : A → A → ℂ} (he : IsSelfDualBicharacter e)
    (P : SchwartzBruhat (Aˣ × U) →ₗ[ℂ] SchwartzBruhat Aˣ) (T : Distribution U)
    [ν.IsMulRightInvariant] [ρ.IsAddHaarMeasure]
    [SecondCountableTopology A] [SecondCountableTopology Aˣ] [CompactOpenExhaustion A] [BorelSpace A]
    [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
    [BorelSpace (adjointFixedAlgebra α)] [BorelSpace (adjointFixedAlgebra α)ˣ] : Prop :=
  (∀ g : Aˣ, i (Units.map α.toMonoidHom g) = s * i g * s⁻¹) →
  ExponentialProductStraighteningStatement F A →
  (∀ k : Aˣ, ∀ x z, e (conjugationHomeomorph k x) (conjugationHomeomorph k z) = e x z) →
  π.IsIrreducible →
  let μ := ν.comap j
  letI : IsFiniteMeasureOnCompacts μ := IsFiniteMeasureOnCompacts.comap' ν (hj).continuous (hj).measurableEmbedding
  SchwartzBruhat.IsTestPushforward (μ.prod (ρ.comap (Subtype.val : U → S))) μ (adjointConjugationOnUnits α) P →
  (translatedCosetDistribution i hi s D).comp P = Distribution.tensor (Distribution.ofMeasure μ) T →
  ∃ (c : ℝ) (hc : 1 ≤ c), ∃ ε > (0 : ℝ), ∃ d > (0 : ℝ), max 1 ‖(1 : A)‖ * (c * ε) < 1 ∧
    ∀ (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) (hcr : c * r < 1), r ≤ ε →
    ∀ (t : ℝ) (ht : 0 < t) (ht₁ : t < 1), t ≤ d →
    ∀ htU : closedBall (0 : S) t ⊆ U,
      let K := normUnitOpenSubgroup (A := A) hr hr₁
      let K' := openSubgroupImage K i hi
      let hK' := isCompact_normUnitOpenSubgroupImage i hi hr hr₁
      let E := openSubgroupImageEquiv K i hi
      let B := normUnitCongruence (R := A) (mul_nonneg (zero_le_one.trans hc) hr.le) hcr
      let M := normUnitCongruence (R := S) ht.le ht₁
      let ι := adjointNormSliceHom α ht ht₁ i
      let hι := continuous_adjointNormSliceHom α ht ht₁ i hi.continuous
      let J := K'.comap ι hι
      letI : CompactSpace M := isCompact_iff_compactSpace.mp (isCompact_normUnitCongruence ht.le ht₁)
      let hb := isOpenEmbedding_adjointNormSlice α ht ht₁ htU
      ∀ (σ : SmoothRep.{0, v, v} ℂ M) [FiniteDimensional ℂ σ],
        T (openEmbeddingTestExtension hb (compactTraceTest σ.representation σ.isSmooth)) ≠ 0 →
        ∃ (z : A) (O : Finset (AddChar L(hr) ℂ)) (τ : SmoothRep.{0, w, v} ℂ K')
          (hFD : FiniteDimensional ℂ τ),
          (O : Set (AddChar L(hr) ℂ)) = latticeCharacterOrbit he L(hr) B z ∧
          (∀ (x : L(hr)) (k : K), (k.val : A) = NormedSpace.exp (x : A) →
            τ.representation.character (E k) = ∑ χ ∈ O, χ x) ∧
          (∃ A₁ : Representation.IntertwiningMap (τ.representation.comp (compactSliceRestriction K' ι hι))
            (σ.representation.comp J.toSubgroup.subtype), A₁ ≠ 0) ∧
          letI : FiniteDimensional ℂ τ := hFD
          ∃ m : M,
            let y := s * ι m
            let J' := conjugateIntersection K' K' y
            D (compactTraceCosetTest K' hK' τ.representation τ.isSmooth y) ≠ 0 ∧
            (∃ A₂ : Representation.IntertwiningMap (τ.representation.comp J'.toSubgroup.subtype)
              (τ.representation.comp (conjugateIntersectionTransport K' K' y)), A₂ ≠ 0) ∧
            ∀ K₀ : OpenSubgroup H, fixedVectors π K₀.toSubgroup ≠ ⊥ →
              ∃ g : H, fixedVectors τ.representation (conjugateIntersection K₀ K' g).toSubgroup ≠ ⊥

set_option maxHeartbeats 1600000 in
theorem compactNormDescentWitness {e : A → A → ℂ} (he : IsSelfDualBicharacter e)
    (P : SchwartzBruhat (Aˣ × U) →ₗ[ℂ] SchwartzBruhat Aˣ) (T : Distribution U)
    [ν.IsMulRightInvariant] [ρ.IsAddHaarMeasure]
    [SecondCountableTopology A] [SecondCountableTopology Aˣ] [CompactOpenExhaustion A] [BorelSpace A]
    [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
    [BorelSpace (adjointFixedAlgebra α)] [BorelSpace (adjointFixedAlgebra α)ˣ] :
    CompactNormDescentWitnessStatement α i hi s ν ρ π hπ he P T := by
  intro hα hStraighten hInv hirr μ hP hT
  obtain ⟨c, hc, ε, hε, hsmall, hSmooth⟩ :=
    ambientNormTraceSmoothing i hi (F := F) he (Measure.addHaar : Measure A) ν hStraighten hInv
  obtain ⟨d, hd, hHaar⟩ := exponentialCongruenceHaar (F := F) (A := S)
  refine ⟨c, hc, ε, hε, d, hd, hsmall, fun r hr hr₁ hcr hrε t ht ht₁ htd htU => ?_⟩
  let K := normUnitOpenSubgroup (A := A) hr hr₁
  let K' := openSubgroupImage K i hi
  let hK' := isCompact_normUnitOpenSubgroupImage i hi hr hr₁
  let M := normUnitCongruence (R := S) ht.le ht₁
  let ι := adjointNormSliceHom α ht ht₁ i
  have hι := continuous_adjointNormSliceHom α ht ht₁ i hi.continuous
  let hb := isOpenEmbedding_adjointNormSlice α ht ht₁ htU
  let : CompactSpace M := isCompact_iff_compactSpace.mp (isCompact_normUnitCongruence ht.le ht₁)
  let : SecondCountableTopology S := IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology U := IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology M := hb.isEmbedding.secondCountableTopology
  let ω := ρ.comap (normUnitCoordinate (A := S) ht.le ht₁)
  obtain ⟨_, _, hM⟩ := hHaar t ht ht₁ htd
  let : ω.IsHaarMeasure := (hM ρ).1
  obtain ⟨Q, hQ, hEval⟩ := compactSemisimpleDescentPushforward α K i hi s ht ht₁ htU ν ρ P D T hα hP hT
  let νK := ν.comap (Subtype.val : K' → H)
  let : νK.IsHaarMeasure := IsHaarMeasure.comap (mH := inferInstance) (f := K'.toSubgroup.subtype)
    ν K'.isOpen.isOpenEmbedding_subtypeVal
  let : CompactSpace K' := isCompact_iff_compactSpace.mp hK'
  let f₀ : SchwartzBruhat K' := ⟨fun _ => 1, IsLocallyConstant.const 1, HasCompactSupport.of_compactSpace _⟩
  have hvol : (νK.real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ENNReal.toReal_pos (ne_of_gt (isOpen_univ.measure_pos νK ⟨1, mem_univ _⟩))
      isCompact_univ.measure_ne_top).ne'
  have hconst : (∫ k : K', f₀ k ∂νK) = (νK.real univ : ℂ) := by
    change (∫ _ : K', (1 : ℂ) ∂νK) = _
    rw [integral_const, Complex.real_smul, mul_one]
  have hD : Distribution.IsConjugationInvariant D := distribution_isConjugationInvariant ν π hπ
  change ∀ (σ : SmoothRep.{0, v, v} ℂ M) [FiniteDimensional ℂ σ],
    T (openEmbeddingTestExtension hb (compactTraceTest σ.representation σ.isSmooth)) ≠ 0 → _
  intro σ hσ hNZ
  let g := compactTraceTest σ.representation σ.isSmooth
  let f := compactSliceTraceTest K' hK' σ.representation σ.isSmooth
  have hF : D (Q f) ≠ 0 := by
    change D (Q (SchwartzBruhat.tensor f₀ g)) ≠ 0
    have h := hEval f₀ g
    change D (Q (SchwartzBruhat.tensor f₀ g)) =
      (∫ k : K', f₀ k ∂νK) * T (openEmbeddingTestExtension hb g) at h
    rw [h, hconst]
    exact mul_ne_zero hvol hNZ
  obtain ⟨_, _, _, I, S₀, z, O, τ, hFD, a, _, hOrbit, hChar, hFixed⟩ := hSmooth r hr hr₁ hcr hrε (Q f)
  let : ∀ k, FiniteDimensional ℂ (τ k) := hFD
  obtain ⟨j₀, hj₀, hInter, m, hm⟩ := compactTraceDescentWitness_of_finiteSmoothing K' hK' ν ω
    ι hι s Q D σ.representation σ.isSmooth S₀ (fun j₁ => (τ j₁ : Type v))
      (fun j₁ => (τ j₁).representation)
      (fun j₁ => (τ j₁).isSmooth) (fun _ => a) hQ hD hFixed hF
  let τ₀ := (τ j₀).representation
  let hτ₀ := (τ j₀).isSmooth
  let y := s * ι m
  refine ⟨z j₀, O j₀, τ j₀, hFD j₀, hOrbit j₀ hj₀, hChar j₀ hj₀, hInter, m, hm, ?_, ?_⟩
  · exact compactTraceSelfIntertwining K' hK' τ₀ hτ₀ D y hD hm
  · exact fun K₀ hK₀ => compactTypeAdmissibility K₀ K' hK' ν π hπ τ₀ hτ₀ hirr hK₀ y hm


end Descent

end Langlands.BaseChange
