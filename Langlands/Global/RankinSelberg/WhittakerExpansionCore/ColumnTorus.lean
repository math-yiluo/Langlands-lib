import Langlands.Global.RankinSelberg.WhittakerExpansionCore.Interface
import Langlands.Automorphic.CuspidalWhittaker.WhittakerCoefficient

/-! # Column periods as torus integrals

For `j < r`, the normalized period over the chosen fundamental domain of `V_(j+1)(F)` in
`V_(j+1)(𝔸)` of a continuous function `h` with `y ↦ h(colPoint y)` periodic equals the torus
integral `∫_{(𝔸/F)^(r+1)} h(colPoint y) dy`. Both sides are continuous linear functionals of a
continuous function on the torus; they agree on the characters (orthogonality on both sides),
hence everywhere by the density of the characters. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints Langlands.Automorphic.CuspidalWhittaker

local instance columnTorusSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance columnTorusSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _
local instance columnTorusClosed (F : Type u) [Field F] [NumberField F] (r j : ℕ) :
    IsClosed (adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j) :
      Set (Points F (r + 1))) :=
  GeneralLinearBlockSemidirect.isClosed_adelicPoints_leviUnipotent F _ _
local instance columnTorusLocallyCompact (F : Type u) [Field F] [NumberField F] (r j : ℕ) :
    LocallyCompactSpace (adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j)) :=
  (columnTorusClosed F r j).locallyCompactSpace

variable (F : Type u) [Field F] [NumberField F]

section ColumnPoints

variable {r j : ℕ}

/-- Column points multiply by adding their vectors. -/
theorem colPoint_add (c d : Fin (r + 1) → Adeles F) :
    colPoint F (j := j) (c + d) = colPoint F (j := j) c * colPoint F (j := j) d := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  apply Units.ext
  rw [map_mul, Units.val_mul]
  change pointMatrix F _ = pointMatrix F _ * pointMatrix F _
  rw [pointMatrix_colPoint, pointMatrix_colPoint, pointMatrix_colPoint, one_add_colMatrix_mul]

theorem colMatrix_truncVec {A : Type*} [CommRing A] (c : Fin (r + 1) → A) :
    colMatrix j (truncVec (j + 1) c) = colMatrix j c := by
  ext a b
  simp only [colMatrix_apply, truncVec]
  by_cases h : (a : ℕ) < j + 1 ∧ (b : ℕ) = j + 1
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h.1]
  · rw [ite_eq_right h, ite_eq_right h]

/-- A column point only depends on the coordinates `≤ j`. -/
theorem colPoint_truncVec (c : Fin (r + 1) → Adeles F) :
    colPoint F (j := j) (truncVec (j + 1) c) = colPoint F (j := j) c := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  apply Units.ext
  change pointMatrix F _ = pointMatrix F _
  rw [pointMatrix_colPoint, pointMatrix_colPoint, colMatrix_truncVec]

theorem colPoint_colVec (hj : j < r) {m : Points F (r + 1)}
    (hm : m ∈ adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j)) :
    colPoint F (j := j) (colVec F hj m) = m := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  apply Units.ext
  change pointMatrix F _ = pointMatrix F _
  rw [pointMatrix_colPoint, pointMatrix_eq_of_mem_column F hj hm]

theorem colVec_colPoint (hj : j < r) (c : Fin (r + 1) → Adeles F) :
    colVec F hj (colPoint F (j := j) c) = truncVec (j + 1) c := by
  refine colVec_eq_of_pointMatrix_eq F hj (fun a ha => ?_) ?_
  · simp only [truncVec]
    rw [ite_eq_right (by omega)]
  · rw [pointMatrix_colPoint, colMatrix_truncVec]

theorem truncVec_colVec (hj : j < r) (m : Points F (r + 1)) :
    truncVec (j + 1) (colVec F hj m) = colVec F hj m := by
  funext a
  simp only [truncVec]
  by_cases ha : (a : ℕ) < j + 1
  · rw [ite_eq_left ha]
  · rw [ite_eq_right ha, isColSupported_colVec F hj m a (by omega)]

/-- In matrix coordinates a column point is the column unit of the library torus framework. -/
theorem adelicEquiv_colPoint (hj : j < r) (c : Fin (r + 1) → Adeles F) :
    GeneralLinearGroupPoints.adelicEquiv F (r + 1) (colPoint F (j := j) c) =
      colUnit (colIdx j hj) c := by
  apply Units.ext
  change pointMatrix F _ = _
  rw [pointMatrix_colPoint, colUnit_val]
  congr 1

theorem colPoint_eq_symm_colUnit (hj : j < r) (c : Fin (r + 1) → Adeles F) :
    colPoint F (j := j) c =
      (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm (colUnit (colIdx j hj) c) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [adelicEquiv_colPoint F hj]
  exact ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).apply_symm_apply _).symm

theorem continuous_colPoint (hj : j < r) : Continuous (colPoint F (j := j) (r := r)) := by
  have : colPoint F (j := j) (r := r) = fun c =>
      (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm (colUnit (colIdx j hj) c) :=
    funext (colPoint_eq_symm_colUnit F hj)
  rw [this]
  exact (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm.continuous.comp
    (continuous_colUnit _)

end ColumnPoints

section Characters

variable {F}

theorem pairingCharacter_truncVec {r : ℕ} (m : ℕ) (a : Fin (r + 1) → F)
    (y : Fin (r + 1) → Adeles F) :
    pairingCharacter a (truncVec m y) = pairingCharacter (truncVec m a) y := by
  have hsum : ∑ i, algebraMap F (Adeles F) (a i) * truncVec m y i =
      ∑ i, algebraMap F (Adeles F) (truncVec m a i) * y i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [truncVec]
    split_ifs <;> simp
  simp only [pairingCharacter, hsum]

theorem pairingCharacter_ratVec {Idx : Type*} [Fintype Idx] (a k : Idx → F) :
    pairingCharacter a (ratVec k) = 1 := by
  have h := isPeriodic_pairingCharacter a 0 k
  rw [zero_add] at h
  rw [h]
  simp [pairingCharacter]

variable [CompactSpace (AdeleQuotient F)]

/-- Orthogonality on the torus: a nontrivial character integrates to zero. -/
theorem torusIntegral_pairingCharacter {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {a : Idx → F} (ha : a ≠ 0) : torusIntegral Idx (pairingCharacter a) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! hh
    exact ha (funext hh)
  obtain ⟨x0, hx0⟩ := exists_adelicCharacter_ne_one F
  set t : Idx → Adeles F := Pi.single i (algebraMap F (Adeles F) (a i)⁻¹ * x0) with ht
  have hpt : pairingCharacter a t = (adelicCharacter F x0 : ℂ) := by
    unfold pairingCharacter
    congr 2
    rw [Finset.sum_eq_single i]
    · rw [ht, Pi.single_eq_same, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
    · intro k _ hk
      rw [ht, Pi.single_eq_of_ne hk, mul_zero]
    · intro hh
      exact absurd (Finset.mem_univ i) hh
  have key := torusIntegral_add_right (isPeriodic_pairingCharacter a) t
  have hmul : torusIntegral Idx (pairingCharacter a) * (adelicCharacter F x0 : ℂ) =
      torusIntegral Idx (pairingCharacter a) := by
    rw [← torusIntegral_mul_const, ← key]
    refine torusIntegral_congr fun y => ?_
    rw [pairingCharacter_add_right, hpt]
  have hne : (adelicCharacter F x0 : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr fun h => hx0 (Circle.coe_eq_one.mp h)
  have h4 : torusIntegral Idx (pairingCharacter a) * ((adelicCharacter F x0 : ℂ) - 1) = 0 := by
    rw [mul_sub, mul_one, hmul, sub_self]
  exact (mul_eq_zero.mp h4).resolve_right hne

end Characters

section Bridge

variable [CompactSpace (AdeleQuotient F)] {r j : ℕ}

/-- `truncVec (j + 1)` as an additive map. -/
def truncHom (r j : ℕ) : (Fin (r + 1) → Adeles F) →+ (Fin (r + 1) → Adeles F) where
  toFun := truncVec (j + 1)
  map_zero' := by
    funext i
    simp [truncVec]
  map_add' v w := truncVec_add (j + 1) v w

omit [CompactSpace (AdeleQuotient F)] in
theorem truncHom_apply (y : Fin (r + 1) → Adeles F) : truncHom F r j y = truncVec (j + 1) y :=
  rfl

omit [CompactSpace (AdeleQuotient F)] in
theorem preservesRational_truncHom : PreservesRational (truncHom F r j) := fun k =>
  ⟨truncVec (j + 1) k, by
    funext i
    simp only [truncHom_apply, truncVec, ratVec_apply]
    split_ifs <;> simp⟩

omit [CompactSpace (AdeleQuotient F)] in
theorem continuous_truncHom : Continuous (truncHom F r j) :=
  continuous_truncVec (j + 1)

/-- **Column periods are torus integrals.** For `h` with `y ↦ h(colPoint y)` continuous and
periodic, the normalized period of `h` over the chosen fundamental domain of `V_(j+1)(F)` in
`V_(j+1)(𝔸)` is the torus integral of `y ↦ h(colPoint y)`. -/
theorem normalized_setIntegral_column_eq_torusIntegral (hj : j < r) (h : Points F (r + 1) → ℂ)
    (hc : Continuous (fun y => h (colPoint F (j := j) y)))
    (hper : IsPeriodic (fun y => h (colPoint F (j := j) y))) :
    ((Measure.haar : Measure (adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j)))
        (LeftCosetSpace.fundamentalDomain
          (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
          (isDiscrete_rationalSubgroup F _ _))).toReal⁻¹ •
        ∫ m in LeftCosetSpace.fundamentalDomain
            (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
            (isDiscrete_rationalSubgroup F _ _), h (m : Points F (r + 1)) ∂Measure.haar =
      torusIntegral (Fin (r + 1)) (fun y => h (colPoint F (j := j) y)) := by
  classical
  have := compactSpace_columnRationalQuotient F r j
  have : IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure
      (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
      (isDiscrete_rationalSubgroup F _ _)) :=
    rationalQuotientHaarMeasure_isFiniteMeasure F _ _
  have := haar_isMulRightInvariant_of_compactRationalQuotient F (Scheme F (r + 1))
    (columnUnipotent F r j)
  set ν := (Measure.haar : Measure (adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j)))
    with hν
  set E := LeftCosetSpace.fundamentalDomain
    (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
    (isDiscrete_rationalSubgroup F _ _) with hE
  have hE0 : ν E ≠ 0 := LeftCosetSpace.haar_fundamentalDomain_ne_zero
    (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
    (isDiscrete_rationalSubgroup F _ _)
  have hEtop : ν E ≠ ⊤ := LeftCosetSpace.haar_fundamentalDomain_ne_top
    (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
    (isDiscrete_rationalSubgroup F _ _)
  have : IsFiniteMeasure (ν.restrict E) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hEtop.lt_top⟩
  -- the two functionals on the torus
  set κ : adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j) →
      (Fin (r + 1) → AdeleQuotient F) :=
    fun m => torusMk (colVec F hj (m : Points F (r + 1))) with hκ
  have hκc : Continuous κ :=
    continuous_torusMk.comp ((continuous_colVec F hj).comp continuous_subtype_val)
  set τ := torusMap (preservesRational_truncHom F (r := r) (j := j)) with hτ
  have hτc : Continuous τ :=
    continuous_torusMap _ (continuous_truncHom F (r := r) (j := j))
  have hint₁ : ∀ p : C(Fin (r + 1) → AdeleQuotient F, ℂ),
      Integrable (fun m => p (κ m)) (ν.restrict E) := fun p =>
    Integrable.of_bound (p.continuous.comp hκc).aestronglyMeasurable ‖p‖
      (ae_of_all _ fun m => p.norm_coe_le_norm _)
  have hint₂ : ∀ p : C(Fin (r + 1) → AdeleQuotient F, ℂ),
      Integrable (fun t => p (τ t)) (torusHaar F (Fin (r + 1))) := fun p =>
    integrable_of_continuous (p.continuous.comp hτc)
  let L₁ : C(Fin (r + 1) → AdeleQuotient F, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun p => ∫ m in E, p (κ m) ∂ν
      map_add' := fun p q => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (hint₁ p) (hint₁ q)
      map_smul' := fun c p => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
  let L₂ : C(Fin (r + 1) → AdeleQuotient F, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun p => ∫ t, p (τ t) ∂torusHaar F (Fin (r + 1))
      map_add' := fun p q => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (hint₂ p) (hint₂ q)
      map_smul' := fun c p => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
  let L₁c : C(Fin (r + 1) → AdeleQuotient F, ℂ) →L[ℂ] ℂ := L₁.mkContinuous (ν.real E) fun p => by
    calc ‖L₁ p‖ ≤ ‖p‖ * ν.real E :=
          norm_setIntegral_le_of_norm_le_const hEtop.lt_top fun m _ => p.norm_coe_le_norm _
      _ = ν.real E * ‖p‖ := mul_comm _ _
  let L₂c : C(Fin (r + 1) → AdeleQuotient F, ℂ) →L[ℂ] ℂ := L₂.mkContinuous 1 fun p => by
    calc ‖L₂ p‖ ≤ ‖p‖ * (torusHaar F (Fin (r + 1))).real Set.univ :=
          norm_integral_le_of_norm_le_const (ae_of_all _ fun t => p.norm_coe_le_norm _)
      _ = 1 * ‖p‖ := by rw [probReal_univ]; ring
  set D : C(Fin (r + 1) → AdeleQuotient F, ℂ) →L[ℂ] ℂ := L₁c - (ν.real E : ℂ) • L₂c with hD
  have hDapp : ∀ p, D p = (∫ m in E, p (κ m) ∂ν) -
      (ν.real E : ℂ) * ∫ t, p (τ t) ∂torusHaar F (Fin (r + 1)) := fun p => rfl
  -- values on characters
  have hχκ : ∀ (a : Fin (r + 1) → F) m,
      torusCharacterMap F (Fin (r + 1)) a (κ m) = pairingCharacter a (colVec F hj m.val) :=
    fun a m => (isPeriodic_pairingCharacter a).lift_mk _
  have hχτ : ∀ (a : Fin (r + 1) → F) t,
      torusCharacterMap F (Fin (r + 1)) a (τ t) =
        pairingCharacter (truncVec (j + 1) a) (torusLift t) := by
    intro a t
    rw [torusCharacterMap_apply]
    change pairingCharacter a (torusLift (torusMk (truncHom F r j (torusLift t)))) = _
    rw [(isPeriodic_pairingCharacter a).lift_mk, truncHom_apply, pairingCharacter_truncVec]
  have hspan : Submodule.span ℂ (Set.range (torusCharacterMap F (Fin (r + 1)))) ≤
      LinearMap.ker (D : _ →ₗ[ℂ] ℂ) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    change D (torusCharacterMap F (Fin (r + 1)) a) = 0
    rw [hDapp]
    simp_rw [hχκ, hχτ]
    by_cases ha : truncVec (j + 1) a = 0
    · have h1 : ∀ m : adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j),
          pairingCharacter a (colVec F hj m.val) = 1 := fun m => by
        rw [← truncVec_colVec F hj, pairingCharacter_truncVec, ha, pairingCharacter_zero]
      simp_rw [h1, ha, pairingCharacter_zero]
      rw [setIntegral_const, integral_const, probReal_univ, one_smul, Complex.real_smul,
        sub_self]
    · have h2 : ∫ t, pairingCharacter (truncVec (j + 1) a) (torusLift t)
          ∂torusHaar F (Fin (r + 1)) = 0 := torusIntegral_pairingCharacter ha
      obtain ⟨i, hi⟩ : ∃ i, truncVec (j + 1) a i ≠ 0 := by
        by_contra! hh
        exact ha (funext hh)
      have hij : (i : ℕ) < j + 1 := by
        by_contra hh
        exact hi (by simp only [truncVec]; rw [ite_eq_right hh])
      have hai : a i ≠ 0 := by
        simpa only [truncVec, ite_eq_left hij] using hi
      obtain ⟨x0, hx0⟩ := exists_adelicCharacter_ne_one F
      set t0 : Fin (r + 1) → Adeles F := Pi.single i (algebraMap F (Adeles F) (a i)⁻¹ * x0)
        with ht0
      set m₀ : adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j) :=
        ⟨colPoint F (j := j) t0, colPoint_mem_column F t0⟩ with hm₀
      have hθ : pairingCharacter a (colVec F hj m₀.val) ≠ 1 := by
        rw [hm₀]
        change pairingCharacter a (colVec F hj (colPoint F (j := j) t0)) ≠ 1
        rw [colVec_colPoint, pairingCharacter_truncVec]
        have hti : truncVec (j + 1) a i = a i := by
          simp only [truncVec]
          exact ite_eq_left hij
        have hsum : ∑ k, algebraMap F (Adeles F) (truncVec (j + 1) a k) * t0 k = x0 := by
          rw [Finset.sum_eq_single i]
          · rw [ht0, Pi.single_eq_same, ← mul_assoc, ← map_mul, hti, mul_inv_cancel₀ hai,
              map_one, one_mul]
          · intro k _ hk
            rw [ht0, Pi.single_eq_of_ne hk, mul_zero]
          · intro hh
            exact absurd (Finset.mem_univ i) hh
        rw [pairingCharacter, hsum]
        exact fun h => hx0 (Circle.coe_eq_one.mp h)
      have h3 := LeftCosetSpace.Semidirect.setIntegral_fundamentalDomain_character_eq_zero
        (rationalSubgroup F (Scheme F (r + 1)) (columnUnipotent F r j))
        (isDiscrete_rationalSubgroup F _ _)
        (fun m => pairingCharacter a (colVec F hj (m : Points F (r + 1))))
        (fun m₁ m₂ => by
          change pairingCharacter a (colVec F hj ((m₁ : Points F (r + 1)) * m₂)) = _
          rw [colVec_mul F hj m₁.property m₂.property, pairingCharacter_add_right])
        (fun k hk => by
          obtain ⟨q, hq⟩ := hk
          rw [← hq, AdelicSubgroupPoints.rational_coe]
          choose e he using colVec_rational F hj q.val
          have hv : colVec F hj (AdelicGroupPoints.rational F (Scheme F (r + 1)) q.val) =
              ratVec e := funext fun b => he b
          rw [hv, pairingCharacter_ratVec])
        (m₀ := m₀) hθ
      rw [h3, h2, mul_zero, sub_zero]
  have hker := Submodule.topologicalClosure_minimal _ hspan D.isClosed_ker
  rw [span_torusCharacterMap_closure_eq_top] at hker
  -- the function on the torus
  set P : C(Fin (r + 1) → AdeleQuotient F, ℂ) :=
    ⟨(fun y => h (colPoint F (j := j) y)) ∘ torusLift,
      hper.continuous_lift hc⟩ with hP
  have hDP : D P = 0 := hker Submodule.mem_top
  rw [hDapp] at hDP
  have hP1 : ∀ m : adelicPoints F (Scheme F (r + 1)) (columnUnipotent F r j),
      P (κ m) = h (m : Points F (r + 1)) := by
    intro m
    change h (colPoint F (j := j) (torusLift (torusMk (colVec F hj m.val)))) = _
    rw [hper.lift_mk, colPoint_colVec F hj m.property]
  have hP2 : ∀ t, P (τ t) = h (colPoint F (j := j) (torusLift t)) := by
    intro t
    change h (colPoint F (j := j) (torusLift (torusMk (truncHom F r j (torusLift t))))) = _
    rw [hper.lift_mk, truncHom_apply, colPoint_truncVec]
  simp_rw [hP1, hP2] at hDP
  have hreal : (ν.real E : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact ENNReal.toReal_ne_zero.mpr ⟨hE0, hEtop⟩
  rw [sub_eq_zero] at hDP
  unfold Automorphic.CuspidalWhittaker.torusIntegral
  rw [hDP, Complex.real_smul, ← mul_assoc, Complex.ofReal_inv]
  change ((ν.real E : ℂ))⁻¹ * (ν.real E : ℂ) * _ = _
  rw [inv_mul_cancel₀ hreal, one_mul]

end Bridge

end Langlands.Global.RankinSelbergGlobal.Unfolding
