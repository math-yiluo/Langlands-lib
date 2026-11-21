import Langlands.Global.RankinSelberg.ComplexBruhatGaussChart
import Langlands.Representation.Archimedean.ComplexJacquetBorel
import Langlands.Group.GL.UpperTriangularCartan
import Mathlib.Analysis.Distribution.TestFunction

/-! # Smooth principal-series sections from compactly supported Gauss chart tests -/

noncomputable section

open Set TopologicalSpace
open scoped Classical ContDiff Distributions Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexBruhatTestExtension

open Langlands.GeneralLinear
open Langlands.Archimedean (borelChar borelChar_one contDiffAt_borelChar
  borelChar_diagonalUnits_mul borelFactor_eq_unitChar posWeight posExponent
  principalSeriesCharacter principalSeriesCharacter_eq complexPositionCharacter
  complexStandardModule mem_principalSeries_iff contMDiff_of_contDiffOn isOpen_setOf_isUnit_matrix)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexOppositeCompactChart (Coordinates oppositePoint contDiff_oppositePoint_val)
open ComplexBruhatGaussChart (chartMatrixDomain chartDomain chartCoordinates chartUpper chartSection
  isOpen_chartMatrixDomain contDiffOn_chartCoordinates continuous_chartSection chartUpper_mem
  chart_factorization chart_recover chart_left_mul)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "B" => fun n => upperTriangularSubgroup n ℂ

variable {n : ℕ}

/-- The complex tests on the full lower-coordinate space of a Gauss chart. -/
abbrev ChartTest (n : ℕ) := 𝓓((⊤ : Opens (Coordinates n)), ℂ)

/-- The union of the left Borel cosets through the chart representatives of `S`. -/
def chartSaturation (w : Equiv.Perm (Fin n)) (S : Set (Coordinates n)) : Set (G n) :=
  {g | ∃ z ∈ S, g * (chartSection w z)⁻¹ ∈ B n}

theorem mem_chartSaturation (w : Equiv.Perm (Fin n)) (S : Set (Coordinates n)) (g : G n) :
    g ∈ chartSaturation w S ↔ g ∈ chartDomain w ∧ chartCoordinates w g.val ∈ S := by
  constructor
  · rintro ⟨z, hz, hb⟩
    let b : B n := ⟨g * (chartSection w z)⁻¹, hb⟩
    have he : b.val * chartSection w z = g := inv_mul_cancel_right _ _
    obtain ⟨h, hCoord, _⟩ := chart_recover w b z
    rw [he] at h hCoord
    exact ⟨h, hCoord ▸ hz⟩
  · rintro ⟨hg, hz⟩
    refine ⟨chartCoordinates w g.val, hz, ?_⟩
    nth_rw 1 [← chart_factorization w g]
    rw [mul_inv_cancel_right]
    exact chartUpper_mem w g hg

theorem isClosed_chartSaturation (w : Equiv.Perm (Fin n)) {S : Set (Coordinates n)}
    (hS : IsCompact S) : IsClosed (chartSaturation w S) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let T : Set (G n × S) := {p | p.1 * (chartSection w p.2.val)⁻¹ ∈ B n}
  have hc : IsClosed T := (isClosed_upperTriangularSubgroup n ℂ).preimage
    (continuous_fst.mul (((continuous_chartSection w).comp
      (continuous_subtype_val.comp continuous_snd)).inv))
  have hImage : Prod.fst '' T = chartSaturation w S := by
    ext g
    constructor
    · rintro ⟨⟨_, z⟩, h, rfl⟩
      exact ⟨z.val, z.2, h⟩
    · rintro ⟨z, hz, h⟩
      exact ⟨(g, ⟨z, hz⟩), h, rfl⟩
  rw [← hImage]
  exact isClosedMap_fst_of_compactSpace _ hc

/-- The open Gauss domain restricted to invertible matrices. -/
def chartUnitMatrixDomain (w : Equiv.Perm (Fin n)) : Set (Mat n) :=
  {X | IsUnit X} ∩ chartMatrixDomain w

theorem isOpen_chartUnitMatrixDomain (w : Equiv.Perm (Fin n)) : IsOpen (chartUnitMatrixDomain w) :=
  isOpen_setOf_isUnit_matrix.inter (isOpen_chartMatrixDomain w)

/-- The ambient matrix expression for the upper factor of the Gauss chart. -/
def chartUpperMatrix (w : Equiv.Perm (Fin n)) (X : Mat n) : Mat n :=
  X * (permutation n ℂ w)⁻¹.val * (oppositePoint (chartCoordinates w X)).val

theorem chartUpperMatrix_val (w : Equiv.Perm (Fin n)) (g : G n) :
    chartUpperMatrix w g.val = (chartUpper w g).val := rfl

theorem contDiffOn_chartUpperMatrix (w : Equiv.Perm (Fin n)) :
    ContDiffOn ℝ ∞ (chartUpperMatrix w) (chartMatrixDomain w) :=
  (contDiff_id.contDiffOn.mul contDiff_const.contDiffOn).mul
    ((contDiff_oppositePoint_val n).comp_contDiffOn (contDiffOn_chartCoordinates w))

private def weight (ds : List ComplexCharacterData) (i : Fin n) : ℤ := posWeight ds i

private def exponent (ds : List ComplexCharacterData) (i : Fin n) : ℂ :=
  2 * (posExponent ds i + (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)))

/-- The normalized inducing multiplier written on the ambient matrix space. -/
def inducingMultiplier (ds : List ComplexCharacterData) (X : Mat n) : ℂ :=
  borelChar (weight ds) (exponent ds) X

@[simp] theorem inducingMultiplier_one (ds : List ComplexCharacterData) :
    inducingMultiplier (n := n) ds 1 = 1 := borelChar_one _ _

private theorem principalSeriesCharacter_eq_product (ds : List ComplexCharacterData) (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n (complexPositionCharacter ds) a =
      ∏ i, Langlands.Archimedean.borelFactor (weight ds i) (exponent ds i) (a i) := by
  rw [principalSeriesCharacter_eq]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [borelFactor_eq_unitChar, exponent, mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℂ) ≠ 0)]
  rfl

theorem contDiffOn_chartMultiplier (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData) :
    ContDiffOn ℝ ∞ (fun X => inducingMultiplier ds (chartUpperMatrix w X)) (chartUnitMatrixDomain w) := by
  intro X hX
  let g : G n := hX.1.unit
  have he : g.val = X := hX.1.unit_spec
  have hg : g ∈ chartDomain w := by
    change g.val ∈ chartMatrixDomain w
    rw [he]
    exact hX.2
  have hD (i : Fin n) : chartUpperMatrix w X i i ≠ 0 := by
    rw [← he, chartUpperMatrix_val]
    exact Langlands.GeneralLinear.UpperBruhatCoordinates.diag_ne_zero_of_upper
      (chartUpper w g) (chartUpper_mem w g hg) i
  exact ((contDiffAt_borelChar (weight ds) (exponent ds) hD).comp X
    ((contDiffOn_chartUpperMatrix w).contDiffAt ((isOpen_chartMatrixDomain w).mem_nhds hX.2))).contDiffWithinAt

/-- The section formula on matrices, extended by zero off the pivot domain. -/
def extendTestMatrix (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData) (φ : ChartTest n)
    (X : Mat n) : ℂ :=
  if X ∈ chartMatrixDomain w then inducingMultiplier ds (chartUpperMatrix w X) * φ (chartCoordinates w X)
  else 0

theorem extendTestMatrix_of_mem (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData)
    (φ : ChartTest n) {g : G n} (hg : g ∈ chartDomain w) :
    extendTestMatrix w ds φ g.val = inducingMultiplier ds (chartUpper w g).val * φ (chartCoordinates w g.val) := by
  change g.val ∈ chartMatrixDomain w at hg
  rw [extendTestMatrix, ite_eq_left hg, chartUpperMatrix_val]

private theorem extendTestMatrix_of_notMem (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData)
    (φ : ChartTest n) {g : G n} (hg : g ∉ chartDomain w) : extendTestMatrix w ds φ g.val = 0 :=
  ite_eq_right (show g.val ∉ chartMatrixDomain w from hg)

theorem extendTestMatrix_zero (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData)
    (φ : ChartTest n) {g : G n} (hg : g ∉ chartSaturation w (tsupport φ)) :
    extendTestMatrix w ds φ g.val = 0 := by
  by_cases hc : g ∈ chartDomain w
  · have hz : chartCoordinates w g.val ∉ tsupport φ :=
      fun hz => hg ((mem_chartSaturation w _ g).mpr ⟨hc, hz⟩)
    rw [extendTestMatrix_of_mem w ds φ hc, image_eq_zero_of_notMem_tsupport hz, mul_zero]
  · exact extendTestMatrix_of_notMem w ds φ hc

private theorem contDiffOn_extendTestMatrix (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData)
    (φ : ChartTest n) : ContDiffOn ℝ ∞ (extendTestMatrix w ds φ) {X : Mat n | IsUnit X} := by
  intro X hX
  let g : G n := hX.unit
  have he : g.val = X := hX.unit_spec
  by_cases hc : g ∈ chartDomain w
  · have h : X ∈ chartUnitMatrixDomain w := ⟨hX, he ▸ hc⟩
    have hf := (contDiffOn_chartMultiplier w ds).mul
      (φ.contDiff.comp_contDiffOn ((contDiffOn_chartCoordinates w).mono inter_subset_right))
    apply ContDiffAt.contDiffWithinAt
    apply (hf.contDiffAt ((isOpen_chartUnitMatrixDomain w).mem_nhds h)).congr_of_eventuallyEq
    filter_upwards [(isOpen_chartUnitMatrixDomain w).mem_nhds h] with Y hY
    exact ite_eq_left hY.2
  · have hg : g ∉ chartSaturation w (tsupport φ) :=
      fun hg => hc ((mem_chartSaturation w _ g).mp hg).1
    let U := (chartSaturation w (tsupport φ))ᶜ
    have ho : IsOpen (Units.val '' U) := Units.isOpenEmbedding_val.isOpenMap U
      (isClosed_chartSaturation w φ.hasCompactSupport).isOpen_compl
    have hXu : X ∈ Units.val '' U := ⟨g, hg, he⟩
    apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [ho.mem_nhds hXu] with Y hY
    obtain ⟨y, hy, rfl⟩ := hY
    exact extendTestMatrix_zero w ds φ hy

private theorem extendTestMatrix_covariant (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData)
    (φ : ChartTest n) (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) (g : G n) :
    extendTestMatrix w ds φ (Iwasawa.diagonalUnits a * u.val * g).val =
      principalSeriesCharacter ℂ n (complexPositionCharacter ds) a * extendTestMatrix w ds φ g.val := by
  let b : B n := ⟨Iwasawa.diagonalUnits a * u.val, mul_mem
    (diagonalUnits_mem_upperTriangular n _) (upperUnipotent_le_upperTriangular n ℂ u.2)⟩
  change extendTestMatrix w ds φ (b.val * g).val = _
  by_cases hg : g ∈ chartDomain w
  · obtain ⟨hbg, hCoord, hB⟩ := chart_left_mul w b g hg
    rw [extendTestMatrix_of_mem w ds φ hbg, extendTestMatrix_of_mem w ds φ hg, hCoord, hB]
    have hT := chartUpper_mem w g hg
    have hD := Langlands.GeneralLinear.UpperBruhatCoordinates.diag_ne_zero_of_upper (chartUpper w g) hT
    change inducingMultiplier ds ((Iwasawa.diagonalUnits a).val * u.val.val * (chartUpper w g).val) * _ = _
    rw [inducingMultiplier, borelChar_diagonalUnits_mul _ _ a u hT hD,
      principalSeriesCharacter_eq_product, mul_assoc]
    rfl
  · have hbg : b.val * g ∉ chartDomain w := by
      intro hbg
      have h := (chart_left_mul w b⁻¹ (b.val * g) hbg).1
      exact hg (by simpa only [Subgroup.coe_inv, inv_mul_cancel_left] using h)
    rw [extendTestMatrix_of_notMem w ds φ hbg, extendTestMatrix_of_notMem w ds φ hg, mul_zero]

/-- Extension by the inducing multiplier gives a smooth vector of the exact principal series. -/
def extendTest (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData) :
    ChartTest n →ₗ[ℂ] complexStandardModule n ds where
  toFun φ := ⟨fun g => extendTestMatrix w ds φ g.val,
    (mem_principalSeries_iff ℂ n (complexPositionCharacter ds) _).mpr
      ⟨contMDiff_of_contDiffOn (contDiffOn_extendTestMatrix w ds φ) (fun _ => rfl),
        extendTestMatrix_covariant w ds φ⟩⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext g
    change extendTestMatrix w ds (φ + ψ) g.val = extendTestMatrix w ds φ g.val + extendTestMatrix w ds ψ g.val
    by_cases hg : g ∈ chartDomain w
    · simp only [extendTestMatrix_of_mem w ds _ hg]
      change inducingMultiplier ds (chartUpper w g).val * (φ _ + ψ _) = _
      rw [mul_add]
    · simp only [extendTestMatrix_of_notMem w ds _ hg, add_zero]
  map_smul' c φ := by
    apply Subtype.ext
    funext g
    change extendTestMatrix w ds (c • φ) g.val = c * extendTestMatrix w ds φ g.val
    by_cases hg : g ∈ chartDomain w
    · simp only [extendTestMatrix_of_mem w ds _ hg]
      change inducingMultiplier ds (chartUpper w g).val * (c * φ (chartCoordinates w g.val)) = _
      ring
    · simp only [extendTestMatrix_of_notMem w ds _ hg, mul_zero]

@[simp] theorem extendTest_apply (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData)
    (φ : ChartTest n) (g : G n) : (extendTest w ds φ).val g = extendTestMatrix w ds φ g.val := rfl

@[simp] theorem extendTest_chartSection (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData)
    (φ : ChartTest n) (z : Coordinates n) : (extendTest w ds φ).val (chartSection w z) = φ z := by
  obtain ⟨hg, hCoord, hB⟩ := chart_recover w (1 : B n) z
  simp only [Subgroup.coe_one, one_mul] at hg hCoord hB
  rw [extendTest_apply, extendTestMatrix_of_mem w ds φ hg, hCoord, hB, Units.val_one,
    inducingMultiplier_one, one_mul]

theorem tsupport_extendTest_subset (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData)
    (φ : ChartTest n) : tsupport (extendTest w ds φ).val ⊆ chartSaturation w (tsupport φ) := by
  apply closure_minimal _ (isClosed_chartSaturation w φ.hasCompactSupport)
  intro g hg
  by_contra h
  exact hg (extendTestMatrix_zero w ds φ h)

/-- Extension to the principal series recovers the original test on the chart representatives
and keeps its support inside the saturation of the coordinate support. -/
def ComplexBruhatTestExtensionStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (w : Equiv.Perm (Fin n)),
    ∃ E : ChartTest n →ₗ[ℂ] complexStandardModule n ds,
      (∀ (φ : ChartTest n) (z : Coordinates n), (E φ).val (chartSection w z) = φ z) ∧
      (∀ φ : ChartTest n, tsupport (E φ).val ⊆ chartSaturation w (tsupport φ))

theorem complexBruhatTestExtension : ComplexBruhatTestExtensionStatement :=
  fun _ ds w => ⟨extendTest w ds, extendTest_chartSection w ds, tsupport_extendTest_subset w ds⟩

end Langlands.Global.RankinSelbergGlobal.ComplexBruhatTestExtension
