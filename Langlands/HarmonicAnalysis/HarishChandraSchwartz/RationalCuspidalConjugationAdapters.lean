import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConjugationStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalIntegrability

/-! # Conditional adapters for the actual VIII.3 targets

The generic reductions retain their analytic hypotheses. The half-weight comparison
and conversion of constants are elementary; they prove neither closed VIII.3 target.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.QuotientIntegration

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  {K : OpenSubgroup (rationalPoints G)}

/-- The full actual chamber, read in the minimal parabolic for the generic interface. -/
def rationalParabolicConjugationChamber (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    Set (standardParabolicPoints i ν ∅) :=
  Subtype.val ⁻¹' rationalMinimalChamberInNormKernel i ν

/-- The actual Iwasawa half-weight restricted to the minimal parabolic. -/
def rationalConjugationHalfWeight
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup) :
    standardParabolicPoints i ν ∅ → ℝ :=
  fun p => iwasawaWeight hPK (rationalMinimalModulus i ν) p

variable (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

include hKc in
/-- Triviality of the actual modulus on `P₀ ∩ K` identifies the Iwasawa half-weight. -/
theorem rationalConjugationHalfWeight_eq_sqrt (p : standardParabolicPoints i ν ∅) :
    rationalConjugationHalfWeight hPK p =
      (NNReal.sqrt (rationalMinimalModulus i ν p : ℝ≥0) : ℝ) := by
  have h := iwasawaWeight_mul (hPK := hPK)
    (fun p hp => rationalMinimalModulus_eq_one i ν K.isOpen hKc p hp)
    p.property K.one_mem
  simpa only [rationalConjugationHalfWeight, mul_one] using h

include hKc in
/-- The squared generic weight is exactly the source's `δ₀`, on the whole parabolic. -/
theorem rationalConjugationHalfWeight_sq (p : standardParabolicPoints i ν ∅) :
    rationalConjugationHalfWeight hPK p ^ 2 =
      ((rationalMinimalModulus i ν p : ℝ≥0) : ℝ) := by
  rw [rationalConjugationHalfWeight_eq_sqrt hKc hPK]
  exact_mod_cast NNReal.sq_sqrt (rationalMinimalModulus i ν p : ℝ≥0)

private theorem enorm_le_nnreal_mul_ofReal_iff {z : ℂ} {c : ℝ≥0} {w : ℝ}
    (hw : 0 ≤ w) :
    ‖z‖ₑ ≤ (c : ℝ≥0∞) * ENNReal.ofReal w ↔ ‖z‖ ≤ (c : ℝ) * w := by
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg c),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (NNReal.coe_nonneg c) hw)]

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

include hKc in
/-- Exact conversion of the generic bound on the full actual chamber. The generic
nonnegative constant becomes a strictly positive real constant by adding one.
Neither side asserts convergence of the inner integral. -/
theorem conjugationIntegralBound_iff_rationalChamberBound
    (muG : Measure (rationalPoints G)) (f₁ f₂ : rationalPoints G → ℂ) :
    ConjugationIntegralBound muG (rationalParabolicConjugationChamber i ν) f₁ f₂
      (rationalConjugationHalfWeight hPK) (rationalHeight (F := F) ρ) ↔
    ∀ r : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ a : rationalMinimalChamberInNormKernel i ν,
      ‖conjugationPairing muG f₁ f₂ a‖ ≤
        c * (rationalMinimalModulus i ν (rationalMinimalChamberToParabolic i ν a) : ℝ≥0) *
          (1 + rationalHeight (F := F) ρ a) ^ (-r) := by
  constructor
  · intro h r
    obtain ⟨c, hc⟩ := h r
    refine ⟨(c : ℝ) + 1, by positivity, fun a => ?_⟩
    have hb := hc (rationalMinimalChamberToParabolic i ν a) a.property
    rw [rationalConjugationHalfWeight_sq hKc hPK] at hb
    have hw : 0 ≤
        ((rationalMinimalModulus i ν (rationalMinimalChamberToParabolic i ν a) : ℝ≥0) : ℝ) *
          (1 + rationalHeight (F := F) ρ a) ^ (-r) := by
      have := rationalHeight_nonneg ρ (a : rationalPoints G)
      positivity
    have hb' := (enorm_le_nnreal_mul_ofReal_iff hw).mp hb
    change ‖conjugationPairing muG f₁ f₂ a‖ ≤
      (c : ℝ) * (((rationalMinimalModulus i ν
        (rationalMinimalChamberToParabolic i ν a) : ℝ≥0) : ℝ) *
          (1 + rationalHeight (F := F) ρ a) ^ (-r)) at hb'
    calc
      _ ≤ _ := hb'
      _ ≤ ((c : ℝ) + 1) * _ :=
        mul_le_mul_of_nonneg_right (by linarith) hw
      _ = _ := by ring
  · intro h r
    obtain ⟨c, hc, hbound⟩ := h r
    refine ⟨⟨c, hc.le⟩, fun p hp => ?_⟩
    rw [rationalConjugationHalfWeight_sq hKc hPK]
    have hw : 0 ≤ ((rationalMinimalModulus i ν p : ℝ≥0) : ℝ) *
        (1 + rationalHeight (F := F) ρ p) ^ (-r) := by
      have := rationalHeight_nonneg ρ (p : rationalPoints G)
      positivity
    apply (enorm_le_nnreal_mul_ofReal_iff hw).mpr
    let a : rationalMinimalChamberInNormKernel i ν := ⟨p, hp⟩
    have hpa : rationalMinimalChamberToParabolic i ν a = p := Subtype.ext rfl
    have hb := hbound a
    rw [hpa] at hb
    change ‖conjugationPairing muG f₁ f₂ (p : rationalPoints G)‖ ≤
      c * (((rationalMinimalModulus i ν p : ℝ≥0) : ℝ) *
        (1 + rationalHeight (F := F) ρ p) ^ (-r))
    exact hb.trans_eq (mul_assoc _ _ _)

/-- The full local VIII.3.1 conclusion is equivalent to the generic bounds together
with its separate all-`h` convergence assertion. Convergence is retained on both sides. -/
theorem rationalCuspidalConjugationBound_iff_generic
    (muG : Measure (rationalPoints G)) :
    RationalCuspidalConjugationBound hKc hPK ρ muG ↔
      RationalCuspidalConjugationConverges hKc hPK ρ muG ∧
      ∀ f₁ : RationalSchwartzSpace hKc hPK ρ,
        f₁ ∈ rationalCuspidalSubmodule hKc hPK ρ →
      ∀ f₂ : RationalSchwartzSpace hKc hPK ρ,
        ConjugationIntegralBound muG (rationalParabolicConjugationChamber i ν)
          (f₁ : rationalPoints G → ℂ) (f₂ : rationalPoints G → ℂ)
          (rationalConjugationHalfWeight hPK) (rationalHeight (F := F) ρ) := by
  constructor
  · rintro ⟨hc, hbound⟩
    exact ⟨hc, fun f₁ hf₁ f₂ =>
      (conjugationIntegralBound_iff_rationalChamberBound hKc hPK ρ muG _ _).mpr
        (hbound f₁ hf₁ f₂)⟩
  · rintro ⟨hc, hbound⟩
    exact ⟨hc, fun f₁ hf₁ f₂ =>
      (conjugationIntegralBound_iff_rationalChamberBound hKc hPK ρ muG _ _).mp
        (hbound f₁ hf₁ f₂)⟩

section Quotient

variable (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)
  [MeasurableSpace (LeftQuotient (rationalPoints.map s).range)]
  (muG : Measure (rationalPoints G))
  [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (muQ : Measure (LeftQuotient (rationalPoints.map s).range))

/-- Specialize the generic countable-cover reduction to the actual descended complex
pairing. The displayed a.e. strong measurability premise upgrades its finite lower
integral to Bochner integrability. All cell, conjugate, volume and series hypotheses
are retained. Inner convergence remains a separate obligation. -/
theorem integrable_rationalLeftConjugationPairing_of_conjugationIntegralBound
    (f₁ f₂ : RationalSchwartzSpace hKc hPK ρ)
    {CellIndex : Type*} [Countable CellIndex]
    {Ω : CellIndex → Set (LeftQuotient (rationalPoints.map s).range)}
    (hcover : ∀ q, ∃ j, q ∈ Ω j)
    {a : CellIndex → standardParabolicPoints i ν ∅}
    (haT : ∀ j, a j ∈ rationalParabolicConjugationChamber i ν)
    {K' Y : Set (rationalPoints G)}
    (hcell : ∀ j, ∀ q ∈ Ω j, ∃ k ∈ K', ∃ y ∈ Y,
      q = Quotient.mk _ (k * (a j : rationalPoints G) * y))
    (hfin₁ : (Set.image (fun k =>
      conjFun k (f₁ : rationalPoints G → ℂ)) K').Finite)
    (hfin₂ : (Set.image (fun y =>
      conjFun y⁻¹ (f₂ : rationalPoints G → ℂ)) Y).Finite)
    (h31 : ∀ k ∈ K', ∀ y ∈ Y,
      ConjugationIntegralBound muG (rationalParabolicConjugationChamber i ν)
        (conjFun k (f₁ : rationalPoints G → ℂ))
        (conjFun y⁻¹ (f₂ : rationalPoints G → ℂ))
        (rationalConjugationHalfWeight hPK) (rationalHeight (F := F) ρ))
    {C₂ : ℝ}
    (hm : ∀ j, muQ (Ω j) ≤ ENNReal.ofReal
      (C₂ * (((rationalMinimalModulus i ν (a j) : ℝ≥0) : ℝ))⁻¹))
    {r : ℝ}
    (hsum : Summable fun j => (1 + rationalHeight (F := F) ρ (a j)) ^ (-r))
    (hmeas : AEStronglyMeasurable
      (rationalLeftConjugationPairing hKc hPK ρ s hs muG f₁ f₂) muQ) :
    Integrable (rationalLeftConjugationPairing hKc hPK ρ s hs muG f₁ f₂) muQ := by
  refine ⟨hmeas, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  exact lintegral_lt_top_of_conjugationIntegralBound
    («μ» := muG) (μX := muQ)
    (T := rationalParabolicConjugationChamber i ν)
    (e := rationalConjugationHalfWeight hPK) (σ := rationalHeight (F := F) ρ)
    (f₁ := (f₁ : rationalPoints G → ℂ)) (f₂ := (f₂ : rationalPoints G → ℂ))
    (π := fun h => (Quotient.mk _ h : LeftQuotient (rationalPoints.map s).range))
    (fun p _ => iwasawaWeight_pos (hPK := hPK) (δ := rationalMinimalModulus i ν) p)
    (rationalHeight_nonneg ρ)
    (fun h => by rw [rationalLeftConjugationPairing_mk]; rfl)
    hcover haT hcell hfin₁ hfin₂ h31
    (fun j => by simpa only [rationalConjugationHalfWeight_sq hKc hPK] using hm j)
    hsum

end Quotient

end Langlands.HarishChandraSchwartz
