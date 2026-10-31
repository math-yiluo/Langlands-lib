import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonMatrixSynthesis
import Langlands.Representation.Whittaker.MirabolicCompactAdapters
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-! Determinant-weighted synthesis of actual compact Whittaker functions. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.CompactWhittakerSynthesis

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis Induction GeneralLinear Whittaker

universe uK uF

section General

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]

omit [TopologicalSpace K] [IsTopologicalRing K] in
/-- The determinant power character is trivial on the actual upper-unipotent subgroup. -/
@[simp] theorem determinantPower_upperUnipotent (abv : AbsoluteValue K ℝ)
    (n : ℕ) (s : ℂ) (u : upperUnipotent (n + 1) K) :
    Shahidi.determinantPower abv (n + 1) s u.val = 1 := by
  apply Units.ext
  rw [Shahidi.determinantPower_apply, unipotent_det, map_one,
    Complex.ofReal_one, Complex.one_cpow, Units.val_one]

/-- Multiply a compact Whittaker induction function by the inverse determinant weight. -/
def weightedCompactFunction (abv : AbsoluteValue K ℝ) (hopen : Shahidi.IsOpenNormOne abv)
    (n : ℕ) (χ : upperUnipotent (n + 1) K →* ℂˣ) (s : ℂ) :
    CompactFunctions (upperUnipotent (n + 1) K) (characterRepresentation χ) →ₗ[ℂ]
      CompactFunctions (upperUnipotent (n + 1) K) (characterRepresentation χ) :=
  compactCharacterMultiply _ _ (Shahidi.determinantPower abv (n + 1) (-s))
    (determinantPower_upperUnipotent abv n (-s))
    (Shahidi.isOpen_ker_determinantPower hopen (n + 1) (-s))

@[simp] theorem weightedCompactFunction_apply (abv : AbsoluteValue K ℝ)
    (hopen : Shahidi.IsOpenNormOne abv) (n : ℕ)
    (χ : upperUnipotent (n + 1) K →* ℂˣ) (s : ℂ)
    (f : CompactFunctions (upperUnipotent (n + 1) K) (characterRepresentation χ))
    (g : Langlands.GeneralLinear (n + 1) K) :
    eval _ _ (weightedCompactFunction abv hopen n χ s f).val g =
      determinantWeight abv g (-s) * eval _ _ f.val g := rfl

end General

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- Every compact standard-Whittaker function is a determinant weight times an
actual absolutely convergent inverse-character integral of one full-matrix test. -/
theorem exists_weighted_matrix_whittaker_integral (ψ : UnitaryAdditiveCharacter F.Carrier)
    (n : ℕ) (s : ℂ)
    (f : CompactFunctions (upperUnipotent (n + 1) F.Carrier)
      (characterRepresentation (standardCharacter ψ n))) :
    ∃ Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier),
      (∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
        Integrable (fun u : upperUnipotent (n + 1) F.Carrier =>
          (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * Φ (u.val * g).val)
          (unipotentHaar F.Carrier n)) ∧
      ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
        eval _ _ f.val g = determinantWeight abv g s *
          (∫ u : upperUnipotent (n + 1) F.Carrier,
            (((standardCharacter ψ n u)⁻¹ : ℂˣ) : ℂ) * Φ (u.val * g).val
              ∂unipotentHaar F.Carrier n) := by
  have hopen : Shahidi.IsOpenNormOne abv :=
    PadicField.TopologicalData.isOpenNormOne_of_eq_normalizedAbs (fun _ => rfl)
  let f' := weightedCompactFunction abv hopen n (standardCharacter ψ n) s f
  have hbasis : ∀ O : Set (Langlands.GeneralLinear (n + 1) F.Carrier), IsOpen O →
      (1 : Langlands.GeneralLinear (n + 1) F.Carrier) ∈ O →
      ∃ L : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier),
        IsCompact (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ∧
          (L : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ⊆ O := by
    intro O hO h1
    exact ⟨(F.canonicalTopologicalData.generalLinearCompactOpen (n + 1) O
      (hO.mem_nhds h1)).val,
      (F.canonicalTopologicalData.generalLinearCompactOpen (n + 1) O
        (hO.mem_nhds h1)).property⟩
  obtain ⟨Φ, hΦi, hΦ⟩ := exists_matrix_characterOrbitIntegral_eq (n + 1) hbasis
    (upperUnipotent (n + 1) F.Carrier) UpperUnipotent.isClosed
    (unipotentHaar F.Carrier n) (standardCharacter ψ n)
    (standardCharacterContinuous ψ n).continuous f'
  refine ⟨Φ, hΦi, fun g => ?_⟩
  rw [hΦ g]
  change eval _ _ f.val g = determinantWeight abv g s *
    (determinantWeight abv g (-s) * eval _ _ f.val g)
  have hw : determinantWeight abv g s * determinantWeight abv g (-s) = 1 := by
    change (Shahidi.determinantPower abv (n + 1) s g : ℂ) *
      (Shahidi.determinantPower abv (n + 1) (-s) g : ℂ) = 1
    rw [Shahidi.determinantPower_neg, MonoidHom.inv_apply, Units.mul_inv]
  rw [← mul_assoc, hw, one_mul]

end Padic

end Langlands.RankinSelberg.CompactWhittakerSynthesis
