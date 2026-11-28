import Langlands.BaseChange.TwistedCharacter.EmbeddedTestPushforward
import Langlands.HarmonicAnalysis.UnitConjugation.LatticeCharacterOrbit
import Langlands.HarmonicAnalysis.UnitConjugation.OrbitFourierEvaluation
import Langlands.Representation.Character.CompactTypeAdmissibility

/-! # Evaluating an exponential trace test by a Fourier coset -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis UnitConjugation Character MeasureTheory Set Metric _root_.Topology

section Transport

variable {A K Y : Type*} [TopologicalSpace A] [T2Space A] [TopologicalSpace K]
  [TopologicalSpace Y] [T2Space Y] {C : Set A} (hC : IsOpen C)
  (E : C ≃ₜ K) {j : K → Y} (hj : IsOpenEmbedding j)

/-- Agreement on tests in an open chart from an additive domain through a compact group. -/
def ExponentialTraceChartAgreement (D : Distribution A) (T : Distribution Y) : Prop :=
  ∀ g : SchwartzBruhat K,
    D (openEmbeddingTestExtension (hC.isOpenEmbedding_subtypeVal.comp E.symm.isOpenEmbedding) g) =
      T (openEmbeddingTestExtension hj g)

end Transport

section Evaluation

variable {A Y X : Type*} [NormedRing A] [IsUltrametricDist A] [ProperSpace A]
  [SecondCountableTopology A] [CompactOpenExhaustion A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace Y] [T2Space Y] [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
  {e : A → A → ℂ} (he : IsSelfDualBicharacter e) (μ : Measure A) [μ.IsAddHaarMeasure]
  {r : ℝ} (hr : 0 < r) (hr₁ : r < 1)

local notation "C" => closedBall (0 : A) r
local notation "L" => OpenAddSubgroup.toAddSubgroup (IsUltrametricDist.closedBall_openAddSubgroup A hr)
local notation "K" => normUnitCongruence (R := A) hr.le hr₁
local notation "hLo" => IsUltrametricDist.isOpen_closedBall (0 : A) hr.ne'
local notation "hLc" => isCompact_closedBall (0 : A) r

/-- With exponential chart agreement, a compact trace whose frequencies form an
orbit vanishes exactly when the Fourier test centered at its representative vanishes. -/
def ExponentialTraceFourierStatement (E : C ≃ₜ K) {j : K → Y} (hj : IsOpenEmbedding j)
    (D : Distribution A) (T : Distribution Y) (B : Subgroup Aˣ) (Z : A)
    (O : Finset (AddChar L ℂ)) (τ : Representation ℂ K X) (hτ : IsSmooth τ) : Prop :=
  (∀ x : C, ((E x).val : A) = NormedSpace.exp (x : A)) →
  ExponentialTraceChartAgreement hLo E hj D T → IsConjugationInvariant D →
  (∀ b ∈ B, ∀ x ∈ L, conjugationHomeomorph b x ∈ L) →
  (∀ b ∈ B, ∀ x z, e (conjugationHomeomorph b x) (conjugationHomeomorph b z) = e x z) →
  (O : Set (AddChar L ℂ)) = latticeCharacterOrbit he L B Z → O.Nonempty →
  (∀ (x : L) (k : K), (k.val : A) = NormedSpace.exp (x : A) → τ.character k = ∑ χ ∈ O, χ x) →
  let Ldual := he.annihilator (L : Set A)
  let f := latticeCosetTest Ldual (he.isOpen_annihilator hLc)
    (he.isCompact_annihilator_compactOpen L hLo hLc) Z
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_normUnitCongruence hr.le hr₁)
  (T (openEmbeddingTestExtension hj (compactTraceTest τ hτ)) = 0 ↔
    D (bicharacterFourierSB μ he f) = 0)

set_option maxHeartbeats 1200000 in
theorem exponentialTraceFourier (E : C ≃ₜ K) {j : K → Y} (hj : IsOpenEmbedding j)
    (D : Distribution A) (T : Distribution Y) (B : Subgroup Aˣ) (Z : A)
    (O : Finset (AddChar L ℂ)) (τ : Representation ℂ K X) (hτ : IsSmooth τ) :
    ExponentialTraceFourierStatement he μ hr hr₁ E hj D T B Z O τ hτ := by
  classical
  intro hE hAgree hInv hBL hBe hO hOne hTrace
  dsimp only
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_normUnitCongruence hr.le hr₁)
  let g := compactTraceTest τ hτ
  let hJ := (hLo).isOpenEmbedding_subtypeVal.comp E.symm.isOpenEmbedding
  let f := openEmbeddingTestExtension hJ g
  have hG (χ : AddChar L ℂ) (hχ : χ ∈ O) : ∃ k : B,
      latticeAddChar he L (conjugationHomeomorph k.val Z) = χ := by
    change χ ∈ latticeCharacterOrbit he L B Z
    rw [← hO]
    exact hχ
  let z (χ : AddChar L ℂ) : A := if hχ : χ ∈ O then conjugationHomeomorph (hG χ hχ).choose.val Z else Z
  have hz (χ : AddChar L ℂ) (hχ : χ ∈ O) :
      z χ ∈ conjugationCosetOrbit B (he.annihilator (L : Set A)) Z := by
    refine ⟨_, (hG χ hχ).choose.property, 0, AddSubgroup.zero_mem _, ?_⟩
    simp only [z, dite_eq_left hχ, add_zero]
  have hzChar (χ : AddChar L ℂ) (hχ : χ ∈ O) : latticeAddChar he L (z χ) = χ := by
    simpa only [z, dite_eq_left hχ] using (hG χ hχ).choose_spec
  have hf : f = (1 : ℂ) • ∑ χ ∈ O, latticeCharacterTest he L hLo hLc (z χ) := by
    rw [one_smul]
    apply Hecke.TestFunction.ext
    intro x
    by_cases hx : x ∈ C
    · let w : L := ⟨x, hx⟩
      have hEw : (Subtype.val ∘ E.symm) (E w) = x :=
        congrArg Subtype.val (E.symm_apply_apply w)
      rw [← hEw, show f ((Subtype.val ∘ E.symm) (E w)) = g (E w) from
        openEmbeddingTestExtension_apply hJ g (E w)]
      rw [show (Subtype.val ∘ E.symm) (E w) = x from hEw]
      rw [show g (E w) = LinearMap.trace ℂ X (τ (E w)) from compactTraceTest_apply τ hτ (E w)]
      change τ.character (E w) = _
      rw [hTrace w (E w) (hE w)]
      simp only [Submodule.coe_sum, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro χ hχ
      erw [latticeCharacterTest_apply]
      rw [indicator_of_mem (show x ∈ L from hx)]
      exact (congrArg (fun ψ : AddChar L ℂ => ψ w) (hzChar χ hχ)).symm
    · have hx' : x ∉ range (Subtype.val ∘ E.symm) := by
        rintro ⟨u, rfl⟩
        exact hx (E.symm u).property
      rw [show f x = 0 from openEmbeddingTestExtension_apply_of_not_mem hJ g hx']
      simp only [Submodule.coe_sum, Finset.sum_apply]
      symm
      apply Finset.sum_eq_zero
      intro χ _
      erw [latticeCharacterTest_apply]
      rw [indicator_of_notMem (show x ∉ L from hx)]
  rw [← hAgree g]
  exact (orbitFourierEvaluation he L hLo hLc μ B O Z z 1 D f
    hBL hBe hInv hz hf).2 one_ne_zero hOne

end Evaluation

end Langlands.BaseChange
