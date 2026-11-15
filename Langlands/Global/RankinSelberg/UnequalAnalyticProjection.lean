import Langlands.Global.RankinSelberg.UnequalAnalyticPoints
import Langlands.Global.RankinSelberg.UnequalAnalyticQuotientMeasure
import Langlands.GroupScheme.GeneralLinearBlockUnipotentCoordinates

/-! # The padded projection of an automorphic function

For a function `φ` on `GL_(r+1)(𝔸)` that is continuous and left invariant under `GL_(r+1)(F)`,
and an integer `m ≤ r`, this module studies `g ↦ P φ (diag(g, 1))` on `GL_m(𝔸)`, where `P` is
the projection `projection` of `Langlands.Global.RankinSelberg.UnequalIntegrals` (Cogdell's
`P^(r+1)_(m+1)`, extended to all of `GL_(m+1)(𝔸)`). It is the product of a power of
`|det g|` and the coefficient `∫_{Y(F) \ Y(𝔸)} φ(y diag(g, I)) conj ψ_Y(y) dy` along the radical
`Y = Y_(r+1,m)`. The main results:

* `continuous_padProjection`: it is continuous;
* `padProjection_rational_mul`: it is left invariant under `GL_m(F)`;
* `exists_norm_padProjection_le`: it decays faster than every power of `|det g|` and of
  `|det g|⁻¹`, provided `φ` decays in this way on matrices with a standard basis column and a
  standard basis row (the decay estimate of `UnequalAnalyticDecay` for cusp forms).

The invariance is a change of variables `y ↦ D⁻¹ y D` on `Y(F) \ Y(𝔸)` for
`D = diag(γ, I)` with `γ ∈ GL_m(F)`, using `UnequalAnalyticQuotientMeasure`. -/

noncomputable section
universe u
set_option autoImplicit false

open NumberField MeasureTheory Langlands Langlands.Global
open Langlands.GroupScheme.GeneralLinear (blockUnipotentSubgroup blockParabolicSubgroup)
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.RankinSelbergGlobal.UnequalAnalytic

local instance projectionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance projectionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-! ### Generic facts -/

/-- A measure normalized by its total mass has total mass at most one. -/
theorem inv_measure_univ_smul_univ_le_one {X : Type*} [MeasurableSpace X] (ν : Measure X) :
    ((ν Set.univ)⁻¹ • ν) Set.univ ≤ 1 := by
  rw [Measure.smul_apply, smul_eq_mul]
  rcases eq_or_ne (ν Set.univ) 0 with h0 | h0
  · simp [h0]
  rcases eq_or_ne (ν Set.univ) ⊤ with ht | ht
  · simp [ht]
  rw [ENNReal.inv_mul_cancel h0 ht]

/-- On a left quotient, the descended function at a class is the function at the chosen
representative. -/
theorem lift_eq_out {H : Type*} [Group H] (Γ : Subgroup H) {Z : Type*} (f : H → Z)
    (hf : ∀ (c : Γ) (x : H), f ((c : H) * x) = f x) (q : LeftCosetSpace Γ) :
    LeftCosetSpace.lift Γ f hf q = f (Quotient.out q) := by
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation `y ↦ D⁻¹ y D` of a subgroup normalized by `D`. -/
def subgroupConjMulEquiv (S : Subgroup G) (D : G) (hD : ∀ y, D⁻¹ * y * D ∈ S ↔ y ∈ S) :
    S ≃* S where
  toFun y := ⟨D⁻¹ * y * D, (hD y).2 y.2⟩
  invFun y := ⟨D * y * D⁻¹, (hD _).1 (by simp [mul_assoc])⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' y z := Subtype.ext (by simp [mul_assoc])

/-- Conjugation `y ↦ D⁻¹ y D` as a topological automorphism of a subgroup normalized by
`D`. -/
def subgroupConj (S : Subgroup G) (D : G) (hD : ∀ y, D⁻¹ * y * D ∈ S ↔ y ∈ S) : S ≃ₜ* S where
  toMulEquiv := subgroupConjMulEquiv S D hD
  continuous_toFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

@[simp]
theorem coe_subgroupConj_apply (S : Subgroup G) (D : G) (hD : ∀ y, D⁻¹ * y * D ∈ S ↔ y ∈ S)
    (y : S) : ((subgroupConj S D hD y : S) : G) = D⁻¹ * y * D := rfl

end Conj

/-- Conjugation by an element of the parabolic preserves the radical in both directions. -/
theorem conj_mem_blockUnipotent_iff {A : Type*} [CommRing A] {n k : ℕ}
    {P : Matrix.GeneralLinearGroup (Fin n) A}
    (hP : P ∈ blockParabolicSubgroup A (projectionWeight n k))
    (y : Matrix.GeneralLinearGroup (Fin n) A) :
    P⁻¹ * y * P ∈ blockUnipotentSubgroup A (projectionWeight n k) ↔
      y ∈ blockUnipotentSubgroup A (projectionWeight n k) := by
  refine ⟨fun hy => ?_, fun hy => radical_conj hy hP⟩
  have h := radical_conj hy ((blockParabolicSubgroup A (projectionWeight n k)).inv_mem hP)
  rwa [inv_inv, show P * (P⁻¹ * y * P) * P⁻¹ = y by group] at h

/-! ### The radical and its character -/

variable (F : Type u) [Field F] [NumberField F]

/-- The adelic points `Y(𝔸)` of the radical `Y_(r+1,m)`. -/
abbrev radical (r m : ℕ) : Subgroup (Points F (r + 1)) :=
  AdelicSubgroupPoints.adelicPoints F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) m)

/-- The rational points `Y(F)` inside `Y(𝔸)`. -/
abbrev radicalRational (r m : ℕ) : Subgroup (radical F r m) :=
  AdelicSubgroupPoints.rationalSubgroup F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) m)

local instance radicalLocallyCompact (r m : ℕ) : LocallyCompactSpace (radical F r m) :=
  (projectionUnipotentClosed F (r + 1) m).locallyCompactSpace

local notation "E" => GeneralLinearGroupPoints.adelicEquiv F
local notation "Q" => GeneralLinearGroupPoints.rationalEquiv F
local notation "R" => AdelicGroupPoints.rational F

variable {r m : ℕ}

theorem mem_radical_iff (y : Points F (r + 1)) :
    y ∈ radical F r m ↔
      E (r + 1) y ∈ blockUnipotentSubgroup (Adeles F) (projectionWeight (r + 1) m) :=
  GroupScheme.GeneralLinear.mem_blockUnipotent_affinePoints_iff _ _ _ y

omit [NumberField F] in
theorem mem_rationalPoints_iff (c : RationalGroupPoints F (Scheme F (r + 1))) :
    c ∈ AdelicSubgroupPoints.rationalPoints F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) m)
      ↔ Q (r + 1) c ∈ blockUnipotentSubgroup F (projectionWeight (r + 1) m) :=
  GroupScheme.GeneralLinear.mem_blockUnipotent_affinePoints_iff _ _ _ c

theorem mem_radicalRational_iff (y : radical F r m) :
    y ∈ radicalRational F r m ↔ ∃ c : RationalGroupPoints F (Scheme F (r + 1)),
      Q (r + 1) c ∈ blockUnipotentSubgroup F (projectionWeight (r + 1) m) ∧
        R (Scheme F (r + 1)) c = y := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.val, (mem_rationalPoints_iff F c.val).1 c.property, rfl⟩
  · rintro ⟨c, hc, hy⟩
    exact ⟨⟨c, (mem_rationalPoints_iff F c).2 hc⟩, Subtype.ext hy⟩

/-- Elements of `Y(𝔸)` have determinant norm `1`. -/
theorem detNorm_radical (y : radical F r m) : detNorm F (r + 1) y = 1 := by
  have hy := (mem_radical_iff F (y : Points F (r + 1))).1 y.2
  have hdet : AdelicGL.determinant F (r + 1) (E (r + 1) y) = 1 := by
    apply Units.ext
    exact radical_det hy
  rw [detNorm_eq_absDet]
  simp only [absDet, hdet, map_one, Units.val_one, NNReal.coe_one]

variable (ψ : AddChar (Adeles F) ℂ)

theorem projectionCharacter_mul (y z : radical F r m) :
    projectionCharacter F r m ψ (y * z) =
      projectionCharacter F r m ψ y * projectionCharacter F r m ψ z := by
  have hy := (mem_radical_iff F (y : Points F (r + 1))).1 y.2
  have hz := (mem_radical_iff F (z : Points F (r + 1))).1 z.2
  simp only [projectionCharacter, Subgroup.coe_mul, map_mul]
  rw [← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => radical_superdiag_mul hy hz i

theorem projectionCharacter_rational (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (y : radical F r m) (hy : y ∈ radicalRational F r m) :
    projectionCharacter F r m ψ y = 1 := by
  obtain ⟨c, -, he⟩ := (mem_radicalRational_iff F y).1 hy
  simp only [projectionCharacter, ← he, GeneralLinearGroupPoints.adelicEquiv_rational,
    AdelicGL.rational_apply, ← map_sum]
  exact hψ _

theorem norm_projectionCharacter (hψ : ∀ x : Adeles F, ‖ψ x‖ = 1) (y : radical F r m) :
    ‖projectionCharacter F r m ψ y‖ = 1 :=
  hψ _

theorem continuous_projectionCharacter (hψ : Continuous ψ) :
    Continuous (projectionCharacter F r m ψ) := by
  refine hψ.comp (continuous_finsetSum _ fun i _ => ?_)
  exact (continuous_apply _).comp (Matrix.GeneralLinearGroup.continuous_apply _
    ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).continuous.comp
      continuous_subtype_val) _)

/-- The character is unchanged by conjugation with `D` if `D` fixes the superdiagonal. -/
theorem projectionCharacter_conj (D : Points F (r + 1))
    (hD : ∀ y, D⁻¹ * y * D ∈ radical F r m ↔ y ∈ radical F r m)
    (hsd : ∀ y : Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F),
      y ∈ blockUnipotentSubgroup (Adeles F) (projectionWeight (r + 1) m) → ∀ i : Fin r,
        (((E (r + 1) D)⁻¹ * y * E (r + 1) D : Matrix.GeneralLinearGroup (Fin (r + 1))
          (Adeles F)) : Matrix _ _ (Adeles F)) i.castSucc i.succ =
          (y : Matrix _ _ (Adeles F)) i.castSucc i.succ)
    (y : radical F r m) :
    projectionCharacter F r m ψ (subgroupConj (radical F r m) D hD y) =
      projectionCharacter F r m ψ y := by
  have hy := (mem_radical_iff F (y : Points F (r + 1))).1 y.2
  simp only [projectionCharacter, coe_subgroupConj_apply, map_mul, map_inv]
  congr 1
  exact Finset.sum_congr rfl fun i _ => hsd _ hy i

/-! ### The coefficient along the radical -/

variable (φ : Points F (r + 1) → ℂ)

/-- The integrand `y ↦ φ(y x) conj ψ_Y(y)` of the coefficient along `Y`. -/
def coeffKernel (x : Points F (r + 1)) (y : radical F r m) : ℂ :=
  φ ((y : Points F (r + 1)) * x) * starRingEnd ℂ (projectionCharacter F r m ψ y)

variable {F ψ φ}

theorem coeffKernel_rational_mul
    (hφ : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (x : Points F (r + 1)),
      φ (R (Scheme F (r + 1)) c * x) = φ x)
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) (x : Points F (r + 1))
    (c : radicalRational F r m) (y : radical F r m) :
    coeffKernel F ψ φ x ((c : radical F r m) * y) = coeffKernel F ψ φ x y := by
  unfold coeffKernel
  rw [projectionCharacter_mul, projectionCharacter_rational F ψ hψ _ c.2, one_mul]
  congr 1
  obtain ⟨c', -, he⟩ := (mem_radicalRational_iff F _).1 c.2
  rw [Subgroup.coe_mul, ← he, mul_assoc]
  exact hφ c' _

theorem continuous_coeffKernel (hφc : Continuous φ) (hψc : Continuous ψ) (x : Points F (r + 1)) :
    Continuous (coeffKernel F ψ φ (m := m) x) :=
  (hφc.comp (continuous_subtype_val.mul continuous_const)).mul
    (Complex.continuous_conj.comp (continuous_projectionCharacter F ψ hψc))

/-- The coefficient along `Y` is the integral of the descended kernel. -/
theorem coeff_eq
    (hφ : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (x : Points F (r + 1)),
      φ (R (Scheme F (r + 1)) c * x) = φ x)
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) (x : Points F (r + 1)) :
    subgroupCharacterCoefficient F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) m)
      (projectionCharacter F r m ψ) φ x =
    ∫ q, LeftCosetSpace.lift (radicalRational F r m) (coeffKernel F ψ φ x)
        (coeffKernel_rational_mul hφ hψ x) q
      ∂AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F (Scheme F (r + 1))
        (projectionUnipotent F (r + 1) m) := by
  unfold subgroupCharacterCoefficient
  congr 1
  funext q
  rw [lift_eq_out]
  rfl

theorem normalizedMeasure_univ_le_one :
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F (Scheme F (r + 1))
      (projectionUnipotent F (r + 1) m) Set.univ ≤ 1 :=
  inv_measure_univ_smul_univ_le_one _

instance normalizedMeasure_isFiniteMeasure :
    IsFiniteMeasure (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F
      (Scheme F (r + 1)) (projectionUnipotent F (r + 1) m)) :=
  ⟨normalizedMeasure_univ_le_one.trans_lt ENNReal.one_lt_top⟩

/-- **Bound for the coefficient.** -/
theorem norm_coeff_le (hψ1 : ∀ x : Adeles F, ‖ψ x‖ = 1) {x : Points F (r + 1)} {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ y : radical F r m, ‖φ (y * x)‖ ≤ M) :
    ‖subgroupCharacterCoefficient F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) m)
      (projectionCharacter F r m ψ) φ x‖ ≤ M := by
  unfold subgroupCharacterCoefficient
  refine (norm_integral_le_of_norm_le_const (C := M)
    (Filter.Eventually.of_forall fun q => ?_)).trans ?_
  · rw [norm_mul, Complex.norm_conj, norm_projectionCharacter F ψ hψ1, mul_one]
    exact hb _
  · have h1 : (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F (Scheme F (r + 1))
        (projectionUnipotent F (r + 1) m)).real Set.univ ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by rw [ENNReal.ofReal_one]; exact normalizedMeasure_univ_le_one)
    calc _ ≤ M * 1 := mul_le_mul_of_nonneg_left h1 hM
      _ = M := mul_one M

/-- **Continuity of the coefficient along a continuous family.** -/
theorem continuous_coeff_comp (hφc : Continuous φ)
    (hφ : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (x : Points F (r + 1)),
      φ (R (Scheme F (r + 1)) c * x) = φ x)
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) (hψc : Continuous ψ)
    (hψ1 : ∀ x : Adeles F, ‖ψ x‖ = 1) {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X]
    {f : X → Points F (r + 1)} (hf : Continuous f) {M : ℝ}
    (hb : ∀ (a : X) (y : radical F r m), ‖φ (y * f a)‖ ≤ M) :
    Continuous fun a => subgroupCharacterCoefficient F (Scheme F (r + 1))
      (projectionUnipotent F (r + 1) m) (projectionCharacter F r m ψ) φ (f a) := by
  let := AdelicSubgroupPoints.rationalQuotientBorelSpace F (Scheme F (r + 1))
    (projectionUnipotent F (r + 1) m)
  unfold subgroupCharacterCoefficient
  refine continuous_of_dominated (bound := fun _ => M) (fun a => ?_)
    (fun a => Filter.Eventually.of_forall fun q => ?_) (integrable_const M)
    (Filter.Eventually.of_forall fun q => ?_)
  · have he : (fun q : AdelicSubgroupPoints.RationalQuotient F (Scheme F (r + 1))
        (projectionUnipotent F (r + 1) m) =>
        φ (((Quotient.out q : radical F r m) : Points F (r + 1)) * f a) *
          starRingEnd ℂ (projectionCharacter F r m ψ (Quotient.out q))) =
        LeftCosetSpace.lift (radicalRational F r m) (coeffKernel F ψ φ (f a))
          (coeffKernel_rational_mul hφ hψ (f a)) := by
      funext q
      rw [lift_eq_out]
      rfl
    rw [he]
    exact (LeftCosetSpace.continuous_lift _ _ _
      (continuous_coeffKernel hφc hψc (f a))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_conj, norm_projectionCharacter F ψ hψ1, mul_one]
    exact hb _ _
  · exact (hφc.comp (continuous_const.mul hf)).mul continuous_const

/-- **Invariance of the coefficient under rational conjugation.** If `D` is a rational point
whose matrix lies in the parabolic over `F` and over `𝔸` and fixes the superdiagonal of `Y`
under conjugation, then the coefficient at `D x` equals the coefficient at `x`. -/
theorem coeff_rational_mul
    (hφ : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (x : Points F (r + 1)),
      φ (R (Scheme F (r + 1)) c * x) = φ x)
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (D₀ : RationalGroupPoints F (Scheme F (r + 1)))
    (hPF : Q (r + 1) D₀ ∈ blockParabolicSubgroup F (projectionWeight (r + 1) m))
    (hPA : E (r + 1) (R (Scheme F (r + 1)) D₀) ∈
      blockParabolicSubgroup (Adeles F) (projectionWeight (r + 1) m))
    (hsd : ∀ y : Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F),
      y ∈ blockUnipotentSubgroup (Adeles F) (projectionWeight (r + 1) m) → ∀ i : Fin r,
        (((E (r + 1) (R (Scheme F (r + 1)) D₀))⁻¹ * y * E (r + 1) (R (Scheme F (r + 1)) D₀) :
          Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F)) : Matrix _ _ (Adeles F))
            i.castSucc i.succ = (y : Matrix _ _ (Adeles F)) i.castSucc i.succ)
    (x : Points F (r + 1)) :
    subgroupCharacterCoefficient F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) m)
        (projectionCharacter F r m ψ) φ (R (Scheme F (r + 1)) D₀ * x) =
      subgroupCharacterCoefficient F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) m)
        (projectionCharacter F r m ψ) φ x := by
  set D := R (Scheme F (r + 1)) D₀ with hDdef
  have hD : ∀ y, D⁻¹ * y * D ∈ radical F r m ↔ y ∈ radical F r m := fun y => by
    rw [mem_radical_iff, mem_radical_iff, map_mul, map_mul, map_inv]
    exact conj_mem_blockUnipotent_iff hPA _
  let α := subgroupConj (radical F r m) D hD
  let Γ := radicalRational F r m
  have hαΓ : ∀ y, α.toMulEquiv y ∈ Γ ↔ y ∈ Γ := by
    intro y
    change α y ∈ Γ ↔ y ∈ Γ
    rw [mem_radicalRational_iff, mem_radicalRational_iff]
    constructor
    · rintro ⟨c, hc, he⟩
      refine ⟨D₀ * c * D₀⁻¹, ?_, ?_⟩
      · rw [map_mul, map_mul, map_inv]
        have h := (conj_mem_blockUnipotent_iff
          ((blockParabolicSubgroup F (projectionWeight (r + 1) m)).inv_mem hPF) (Q (r + 1) c)).2 hc
        rwa [inv_inv] at h
      · rw [map_mul, map_mul, map_inv, he, coe_subgroupConj_apply, ← hDdef]
        group
    · rintro ⟨c, hc, he⟩
      refine ⟨D₀⁻¹ * c * D₀, ?_, ?_⟩
      · rw [map_mul, map_mul, map_inv]
        exact (conj_mem_blockUnipotent_iff hPF (Q (r + 1) c)).2 hc
      · rw [map_mul, map_mul, map_inv, he, coe_subgroupConj_apply, ← hDdef]
  have hK : ∀ y, coeffKernel F ψ φ (D * x) y = coeffKernel F ψ φ x (α y) := by
    intro y
    unfold coeffKernel
    rw [projectionCharacter_conj F ψ D hD (by rw [hDdef]; exact hsd) y]
    congr 1
    rw [coe_subgroupConj_apply, ← hφ D₀ (D⁻¹ * (y : Points F (r + 1)) * D * x), ← hDdef]
    congr 1
    group
  have hm : Measurable α.toMulEquiv := α.continuous.measurable
  have hm' : Measurable α.toMulEquiv.symm := α.symm.continuous.measurable
  let e := cosetMeasurableEquiv Γ α.toMulEquiv hαΓ hm hm'
  have hΓ := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F (Scheme F (r + 1))
    (projectionUnipotent F (r + 1) m)
  have hmap : Measure.map e (AdelicSubgroupPoints.rationalQuotientHaarMeasure F
      (Scheme F (r + 1)) (projectionUnipotent F (r + 1) m)) =
      ((mulEquivHaarChar α : ℝ≥0∞))⁻¹ • AdelicSubgroupPoints.rationalQuotientHaarMeasure F
        (Scheme F (r + 1)) (projectionUnipotent F (r + 1) m) :=
    map_cosetMap_discreteQuotientMeasure Γ hΓ α.toMulEquiv hαΓ hm hm' Measure.haar _
      (map_haar_eq_smul α)
  have hmp : MeasurePreserving e
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F (Scheme F (r + 1))
        (projectionUnipotent F (r + 1) m))
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F (Scheme F (r + 1))
        (projectionUnipotent F (r + 1) m)) :=
    ⟨e.measurable, map_inv_measure_univ_smul e _ _ hmap⟩
  rw [coeff_eq hφ hψ, coeff_eq hφ hψ]
  rw [← hmp.integral_comp' (LeftCosetSpace.lift Γ (coeffKernel F ψ φ x)
    (coeffKernel_rational_mul hφ hψ x))]
  congr 1
  funext q
  obtain ⟨y, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
  rw [coe_cosetMeasurableEquiv, cosetMap_mk, LeftCosetSpace.lift_mk, LeftCosetSpace.lift_mk, hK]
  rfl

/-! ### The padded projection -/

variable (F) in
/-- Rapid decay in `|log |det||` on matrices having a standard basis column and a standard
basis row. This is the conclusion of `exists_norm_le_of_basis_column_row` for cusp forms. -/
def HasBasisDecay (n : ℕ) (f : Points F n → ℂ) : Prop :=
  ∀ N : ℝ, 0 ≤ N → ∃ C : ℝ, ∀ x : Points F n,
    (∃ j, ∀ i, (E n x : Matrix (Fin n) (Fin n) (Adeles F)) i j =
      (1 : Matrix (Fin n) (Fin n) (Adeles F)) i j) →
    (∃ i, ∀ j, (E n x : Matrix (Fin n) (Fin n) (Adeles F)) i j =
      (1 : Matrix (Fin n) (Fin n) (Adeles F)) i j) →
    ‖f x‖ ≤ C * Real.exp (-(N * |Real.log (detNorm F n x)|))

/-- `P φ (diag(g, 1)) = |det g|^(-(r-m)/2) · (coefficient along Y at diag(g, I))`. -/
theorem projection_pad_eq (h : m < r + 1) (g : Points F m) :
    projection F h ψ φ (pad F (Nat.le_succ m) g) =
      detPower F m g (-((r - m : ℕ) : ℂ) / 2) *
        subgroupCharacterCoefficient F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) m)
          (projectionCharacter F r m ψ) φ (pad F h.le g) := by
  unfold projection
  rw [detPower_pad, pad_pad]

/-- For `y ∈ Y(𝔸)`, the matrix `y diag(g, I)` has a standard basis column (index `m`) and a
standard basis row (the last one), and `|det (y diag(g, I))| = |det g|`; so the decay of `φ`
applies. -/
theorem exists_norm_radical_mul_pad_le (h : m < r + 1) (hφP : HasBasisDecay F (r + 1) φ)
    (N : ℝ) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : radical F r m) (g : Points F m),
      ‖φ (y * pad F h.le g)‖ ≤ C * Real.exp (-(N * |Real.log (detNorm F m g)|)) := by
  obtain ⟨C, hC⟩ := hφP N hN
  refine ⟨max C 0, le_max_right _ _, fun y g => ?_⟩
  have hy := (mem_radical_iff F (y : Points F (r + 1))).1 y.2
  have hx : E (r + 1) ((y : Points F (r + 1)) * pad F h.le g) =
      E (r + 1) y * padGL h.le (E m g) := by
    rw [map_mul, adelicEquiv_pad]
  have hcol : ∃ j, ∀ i, (E (r + 1) ((y : Points F (r + 1)) * pad F h.le g) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i j =
      (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i j := by
    refine ⟨⟨m, h⟩, fun i => ?_⟩
    rw [hx, Units.val_mul, mul_apply_of_col _ (fun k => padGL_col h.le _ ⟨m, h⟩ le_rfl k) i]
    exact radical_col hy ⟨m, h⟩ rfl i
  have hrow : ∃ i, ∀ j, (E (r + 1) ((y : Points F (r + 1)) * pad F h.le g) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i j =
      (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i j := by
    refine ⟨Fin.last r, fun j => ?_⟩
    rw [hx, Units.val_mul, mul_apply_of_row _ (fun k => radical_row hy k) j]
    exact padGL_row h.le _ (Fin.last r) (by rw [Fin.val_last]; omega) j
  have hdet : detNorm F (r + 1) ((y : Points F (r + 1)) * pad F h.le g) = detNorm F m g := by
    rw [detNorm_mul, detNorm_radical, one_mul, detNorm_pad]
  calc ‖φ (y * pad F h.le g)‖
      ≤ C * Real.exp (-(N * |Real.log (detNorm F (r + 1) (y * pad F h.le g))|)) :=
        hC _ hcol hrow
    _ ≤ max C 0 * Real.exp (-(N * |Real.log (detNorm F (r + 1) (y * pad F h.le g))|)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ = max C 0 * Real.exp (-(N * |Real.log (detNorm F m g)|)) := by rw [hdet]

/-- **Continuity of the padded projection.** -/
theorem continuous_projection_pad (h : m < r + 1) (hφc : Continuous φ)
    (hφ : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (x : Points F (r + 1)),
      φ (R (Scheme F (r + 1)) c * x) = φ x)
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) (hψc : Continuous ψ)
    (hψ1 : ∀ x : Adeles F, ‖ψ x‖ = 1) (hφP : HasBasisDecay F (r + 1) φ) :
    Continuous fun g : Points F m => projection F h ψ φ (pad F (Nat.le_succ m) g) := by
  obtain ⟨C, -, hC⟩ := exists_norm_radical_mul_pad_le h hφP 0 le_rfl
  have hb : ∀ (g : Points F m) (y : radical F r m), ‖φ (y * pad F h.le g)‖ ≤ C :=
    fun g y => by simpa using hC y g
  have he : (fun g : Points F m => projection F h ψ φ (pad F (Nat.le_succ m) g)) =
      fun g => detPower F m g (-((r - m : ℕ) : ℂ) / 2) *
        subgroupCharacterCoefficient F (Scheme F (r + 1)) (projectionUnipotent F (r + 1) m)
          (projectionCharacter F r m ψ) φ (pad F h.le g) :=
    funext fun g => projection_pad_eq h g
  rw [he]
  exact (continuous_detPower F m _).mul
    (continuous_coeff_comp hφc hφ hψ hψc hψ1 (continuous_pad F h.le) hb)

/-- **Left `GL_m(F)`-invariance of the padded projection.** -/
theorem projection_pad_rational_mul (h : m < r + 1)
    (hφ : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (x : Points F (r + 1)),
      φ (R (Scheme F (r + 1)) c * x) = φ x)
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    (c : RationalGroupPoints F (Scheme F m)) (g : Points F m) :
    projection F h ψ φ (pad F (Nat.le_succ m) (R (Scheme F m) c * g)) =
      projection F h ψ φ (pad F (Nat.le_succ m) g) := by
  have hA : AdelicGL.rational F (r + 1) (padGL h.le (Q m c)) =
      padGL h.le (AdelicGL.rational F m (Q m c)) := (padGL_map _ h.le _).symm
  rw [projection_pad_eq h, projection_pad_eq h, detPower_rational_mul, pad_mul, pad_rational]
  congr 1
  apply coeff_rational_mul hφ hψ
  · rw [MulEquiv.apply_symm_apply]
    exact padGL_mem_parabolic h.le (Nat.le_succ m) _
  · rw [GeneralLinearGroupPoints.adelicEquiv_rational, MulEquiv.apply_symm_apply, hA]
    exact padGL_mem_parabolic h.le (Nat.le_succ m) _
  · intro y hy i
    rw [GeneralLinearGroupPoints.adelicEquiv_rational, MulEquiv.apply_symm_apply, hA]
    exact radical_superdiag_conj h.le le_rfl _ hy i

/-- **Rapid decay of the padded projection.** For every `N ≥ 0`,
`|P φ (diag(g, 1))| ≤ C exp (-N |log |det g||)`. -/
theorem exists_norm_projection_pad_le (h : m < r + 1) (hψ1 : ∀ x : Adeles F, ‖ψ x‖ = 1)
    (hφP : HasBasisDecay F (r + 1) φ) (N : ℝ) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Points F m, ‖projection F h ψ φ (pad F (Nat.le_succ m) g)‖ ≤
      C * Real.exp (-(N * |Real.log (detNorm F m g)|)) := by
  set a : ℝ := ((r - m : ℕ) : ℝ) / 2 with ha_def
  have ha : 0 ≤ a := by positivity
  obtain ⟨C, hC0, hC⟩ := exists_norm_radical_mul_pad_le h hφP (N + a) (by linarith)
  refine ⟨C, hC0, fun g => ?_⟩
  set L := Real.log (detNorm F m g)
  have hre : (-((r - m : ℕ) : ℂ) / 2).re = -a := by
    rw [ha_def]
    simp [neg_div]
  have hcoeff := norm_coeff_le (φ := φ) (x := pad F h.le g) hψ1
    (mul_nonneg hC0 (Real.exp_pos _).le) (fun y => hC y g)
  rw [projection_pad_eq h, norm_mul, norm_detPower, hre]
  calc Real.exp (-a * L) * _
      ≤ Real.exp (a * |L|) * (C * Real.exp (-((N + a) * |L|))) :=
        mul_le_mul (Real.exp_le_exp.2 (by
          nlinarith [mul_nonneg ha (show 0 ≤ |L| + L by linarith [neg_abs_le L])]))
          hcoeff (norm_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp (a * |L| + -((N + a) * |L|)) := by rw [Real.exp_add]; ring
    _ = C * Real.exp (-(N * |L|)) := by congr 2; ring

end Langlands.Global.RankinSelbergGlobal.UnequalAnalytic
