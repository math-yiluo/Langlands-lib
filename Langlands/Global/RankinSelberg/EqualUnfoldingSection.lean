import Langlands.Global.RankinSelberg.EqualUnfoldingScalar

/-! # The Eisenstein section and series in the equal-rank unfolding -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Pointwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualUnfolding

open Langlands.Global Unfolding

local instance equalSectionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalSectionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section Invariance

variable {H E : Type*} [Group H]

/-- The subgroup of the `g` with `f (g x) = f x` for all `x`. -/
def leftInvarianceSubgroup (f : H → E) : Subgroup H where
  carrier := {g | ∀ x, f (g * x) = f x}
  mul_mem' {a b} ha hb x := by
    rw [mul_assoc, ha, hb]
  one_mem' x := by
    change f (1 * x) = f x
    rw [one_mul]
  inv_mem' {a} ha x := by
    rw [← ha (a⁻¹ * x), mul_inv_cancel_left]

theorem mem_leftInvarianceSubgroup_iff (f : H → E) (g : H) :
    g ∈ leftInvarianceSubgroup f ↔ ∀ x, f (g * x) = f x := Iff.rfl

end Invariance

variable (F : Type u) [Field F] [NumberField F]

section Measures

instance isMulLeftInvariant_ideleMeasure : (ideleMeasure F).IsMulLeftInvariant := by
  unfold ideleMeasure
  infer_instance

instance sFinite_ideleMeasure : SFinite (ideleMeasure F) := by
  unfold ideleMeasure
  infer_instance

/-- `GL_n(F)` is countable: it embeds in the discrete subgroup `GL_n(F)` of `GL_n(𝔸)`. -/
instance countable_rationalGL (n : ℕ) : Countable (RationalGL F n) := by
  have := LeftCosetSpace.countable_of_isDiscrete _
    (AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F n))
  refine Function.Injective.countable
    (f := fun g : RationalGL F n => (⟨rationalPoint F n g, rationalPoint_mem_rationalSubgroup F n g⟩ :
      AdelicGroupPoints.rationalSubgroup F (Scheme F n))) ?_
  intro a b h
  exact rationalPoint_injective F n (congrArg Subtype.val h)

end Measures

variable {F} {r : ℕ}

section Section

variable (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) (Φ : RowVector F (r + 1) → ℂ) (s : ℂ)

theorem detPower_ne_zero (n : ℕ) (x : Points F n) (t : ℂ) : detPower F n x t ≠ 0 := by
  unfold detPower
  exact Complex.exp_ne_zero _

/-- Left translation by `diag(a, …, a)` in the section integrand is the substitution
`a' ↦ a a'`. -/
theorem eisensteinSectionIntegrand_scalarPoint_mul (z w : Points F 1) (x : Points F (r + 1)) :
    eisensteinSectionIntegrand F χ Φ s (scalarPoint F r z * x) w *
        (detPower F 1 z ((r + 1 : ℂ) * s) *
          (Automorphic.centralIdeleCharacter F χ (ideleOf F z) : ℂ)) =
      eisensteinSectionIntegrand F χ Φ s x (z * w) := by
  unfold eisensteinSectionIntegrand
  simp only [lastRow_scalarPoint_mul, smul_smul, ideleOf_mul, map_mul, Units.val_mul,
    detPower_mul]
  rw [mul_comm (ideleOf F w : Adeles F)]
  ring

/-- `F(diag(a, …, a) g, Φ; s, χ) = χ(a)⁻¹ F(g, Φ; s, χ)`. -/
theorem eisensteinSection_scalarPoint_mul (z : Points F 1) (x : Points F (r + 1)) :
    eisensteinSection F χ Φ s (scalarPoint F r z * x) =
      (Automorphic.centralIdeleCharacter F χ (ideleOf F z) : ℂ)⁻¹ *
        eisensteinSection F χ Φ s x := by
  have hd := detPower_ne_zero 1 z ((r + 1 : ℂ) * s)
  have hχ : (Automorphic.centralIdeleCharacter F χ (ideleOf F z) : ℂ) ≠ 0 := Units.ne_zero _
  have hI : (∫ w, eisensteinSectionIntegrand F χ Φ s (scalarPoint F r z * x) w ∂ideleMeasure F) *
      (detPower F 1 z ((r + 1 : ℂ) * s) *
        (Automorphic.centralIdeleCharacter F χ (ideleOf F z) : ℂ)) =
      ∫ w, eisensteinSectionIntegrand F χ Φ s x w ∂ideleMeasure F := by
    rw [← integral_mul_const]
    simp_rw [eisensteinSectionIntegrand_scalarPoint_mul]
    exact integral_mul_left_eq_self (fun w => eisensteinSectionIntegrand F χ Φ s x w) z
  unfold eisensteinSection
  rw [← hI, detPower_mul, detPower_scalarPoint]
  field_simp

/-- The section depends only on the last row and on `|det g|^s`. -/
theorem eisensteinSection_congr {x y : Points F (r + 1)} (hl : lastRow F r x = lastRow F r y)
    (hd : detPower F (r + 1) x s = detPower F (r + 1) y s) :
    eisensteinSection F χ Φ s x = eisensteinSection F χ Φ s y := by
  unfold eisensteinSection eisensteinSectionIntegrand
  simp only [hl, hd]

theorem eisensteinSection_mirabolic_mul {p : Points F (r + 1)}
    (hp : p ∈ mirabolicRationalImage F r) (x : Points F (r + 1)) :
    eisensteinSection F χ Φ s (p * x) = eisensteinSection F χ Φ s x :=
  eisensteinSection_congr χ Φ s (lastRow_mirabolic_mul F r hp x)
    (detPower_rational_mul F (r + 1) (mirabolicRationalImage_le F r hp) x s)

/-- The section is left invariant under `P'_n(F) = Z_n(F) P_n(F)`. -/
theorem eisensteinSection_eisensteinRational_mul {l : Points F (r + 1)}
    (hl : l ∈ eisensteinRationalImage F r) (x : Points F (r + 1)) :
    eisensteinSection F χ Φ s (l * x) = eisensteinSection F χ Φ s x := by
  obtain ⟨b, hb, p, hp, rfl⟩ := exists_scalarPoint_mul_inv F r hl
  rw [mul_assoc, eisensteinSection_scalarPoint_mul, centralIdeleCharacter_ideleOf_rational F χ hb,
    Units.val_one, inv_one, one_mul,
    eisensteinSection_mirabolic_mul χ Φ s (Subgroup.inv_mem _ hp)]

/-- The right translation `q ↦ q γ` of `P'_n(F) \ GL_n(F)`, as an equivalence. -/
def eisensteinCosetTranslate (g : RationalGL F (r + 1)) :
    LeftCosetSpace (eisensteinParabolic F r) ≃ LeftCosetSpace (eisensteinParabolic F r) where
  toFun := LeftCosetSpace.rightTranslate _ g
  invFun := LeftCosetSpace.rightTranslate _ g⁻¹
  left_inv q := by
    simp only [LeftCosetSpace.rightTranslate_mul, mul_inv_cancel,
      LeftCosetSpace.rightTranslate_one]
  right_inv q := by
    simp only [LeftCosetSpace.rightTranslate_mul, inv_mul_cancel,
      LeftCosetSpace.rightTranslate_one]

/-- The Eisenstein series is left invariant under `GL_n(F)`. -/
theorem eisensteinSeries_rational_mul {k : Points F (r + 1)}
    (hk : k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1))) (x : Points F (r + 1)) :
    eisensteinSeries F χ Φ s (k * x) = eisensteinSeries F χ Φ s x := by
  obtain ⟨g, rfl⟩ := exists_rationalPoint_eq F (r + 1) hk
  set f : LeftCosetSpace (eisensteinParabolic F r) → ℂ :=
    fun q => eisensteinSection F χ Φ s (rationalPoint F (r + 1) q.out * x) with hf
  have key : ∀ q : LeftCosetSpace (eisensteinParabolic F r),
      f (eisensteinCosetTranslate g q) =
        eisensteinSection F χ Φ s (rationalPoint F (r + 1) q.out * (rationalPoint F (r + 1) g * x)) := by
    intro q
    have hq : eisensteinCosetTranslate g q = LeftCosetSpace.mk _ (q.out * g) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    obtain ⟨l, hl⟩ := exists_out_mk_eq (eisensteinParabolic F r) (q.out * g)
    rw [hq, hf]
    dsimp only
    rw [hl, rationalPoint_mul, rationalPoint_mul, mul_assoc, mul_assoc,
      eisensteinSection_eisensteinRational_mul χ Φ s
        (rationalPoint_mem_eisensteinRationalImage F r l.property)]
  have h1 : eisensteinSeries F χ Φ s (rationalPoint F (r + 1) g * x) =
      ∑' q, f (eisensteinCosetTranslate g q) := (tsum_congr key).symm
  have h2 : eisensteinSeries F χ Φ s x = ∑' q, f q := rfl
  rw [h1, h2]
  exact (eisensteinCosetTranslate g).tsum_eq f

/-- `E(diag(a, …, a) g) = χ(a)⁻¹ E(g)`. -/
theorem eisensteinSeries_scalarPoint_mul (z : Points F 1) (x : Points F (r + 1)) :
    eisensteinSeries F χ Φ s (scalarPoint F r z * x) =
      (Automorphic.centralIdeleCharacter F χ (ideleOf F z) : ℂ)⁻¹ *
        eisensteinSeries F χ Φ s x := by
  unfold eisensteinSeries
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [← mul_assoc, ← scalarPoint_commute, mul_assoc, eisensteinSection_scalarPoint_mul]

variable {χ Φ s}

/-- With `φ φ'` transforming by `χ` under the center, `φ(g) φ'(g) F(g, Φ; s, χ)` is the
integral over `𝔸^×` of the kernel at `diag(a, …, a) g`. -/
theorem mul_eisensteinSection_eq_integral {φ φ' : Points F (r + 1) → ℂ}
    (hφz : ∀ (z : Points F 1) (x : Points F (r + 1)),
      φ (scalarPoint F r z * x) * φ' (scalarPoint F r z * x) =
        (Automorphic.centralIdeleCharacter F χ (ideleOf F z) : ℂ) * (φ x * φ' x))
    (x : Points F (r + 1)) :
    φ x * φ' x * eisensteinSection F χ Φ s x =
      ∫ z, equalKernel F φ φ' Φ s (scalarPoint F r z * x) ∂ideleMeasure F := by
  unfold eisensteinSection
  rw [← mul_assoc, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [equalKernel, eisensteinSectionIntegrand]
  rw [hφz, lastRow_scalarPoint_mul, detPower_mul, detPower_scalarPoint]
  ring

/-- The kernel `φ φ' Φ(e_n ·) |det|^s` at `diag(a, …, a) g`. -/
theorem equalKernel_scalarPoint_mul {φ φ' : Points F (r + 1) → ℂ}
    (hφz : ∀ (z : Points F 1) (x : Points F (r + 1)),
      φ (scalarPoint F r z * x) * φ' (scalarPoint F r z * x) =
        (Automorphic.centralIdeleCharacter F χ (ideleOf F z) : ℂ) * (φ x * φ' x))
    (z : Points F 1) (x : Points F (r + 1)) :
    equalKernel F φ φ' Φ s (scalarPoint F r z * x) =
      φ x * φ' x * detPower F (r + 1) x s * eisensteinSectionIntegrand F χ Φ s x z := by
  simp only [equalKernel, eisensteinSectionIntegrand]
  rw [hφz, lastRow_scalarPoint_mul, detPower_mul, detPower_scalarPoint]
  ring

end Section

section Measurability

/-- Row vectors carry their Borel σ-algebra, as in `WhittakerIntegrals`. -/
local instance equalSectionRowMeasurableSpace (n : ℕ) : MeasurableSpace (RowVector F n) :=
  borel _

local instance equalSectionRowBorelSpace (n : ℕ) : BorelSpace (RowVector F n) := ⟨rfl⟩

variable (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) {Φ : RowVector F (r + 1) → ℂ} (s : ℂ)

theorem measurable_eisensteinSectionIntegrand (hΦ : Measurable Φ) :
    Measurable fun p : Points F (r + 1) × Points F 1 =>
      eisensteinSectionIntegrand F χ Φ s p.1 p.2 := by
  unfold eisensteinSectionIntegrand
  have ha : Continuous fun p : Points F (r + 1) × Points F 1 => (ideleOf F p.2 : Adeles F) :=
    Units.continuous_val.comp ((continuous_ideleOf F).comp continuous_snd)
  refine ((hΦ.comp (ha.smul ((continuous_lastRow F r).comp continuous_fst)).measurable).mul
    ((continuous_detPower F 1 _).comp continuous_snd).measurable).mul ?_
  exact (Units.continuous_val.comp
    ((Automorphic.centralIdeleCharacter F χ).continuous.comp
      ((continuous_ideleOf F).comp continuous_snd))).measurable

theorem measurable_eisensteinSection (hΦ : Measurable Φ) :
    Measurable (eisensteinSection F χ Φ s) :=
  (continuous_detPower F (r + 1) s).measurable.mul
    ((measurable_eisensteinSectionIntegrand χ s hΦ).stronglyMeasurable.integral_prod_right'
      (ν := ideleMeasure F)).measurable

theorem measurable_eisensteinSeries (hΦ : Measurable Φ) :
    Measurable (eisensteinSeries F χ Φ s) := by
  unfold eisensteinSeries
  exact (StronglyMeasurable.tsum fun q =>
    ((measurable_eisensteinSection χ s hΦ).comp
      (measurable_const_mul _)).stronglyMeasurable).measurable

theorem measurable_lastRow_comp (hΦ : Measurable Φ) :
    Measurable fun x : Points F (r + 1) => Φ (lastRow F r x) :=
  hΦ.comp (continuous_lastRow F r).measurable

end Measurability

end Langlands.Global.RankinSelbergGlobal.EqualUnfolding
