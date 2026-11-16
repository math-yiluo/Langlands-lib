import Langlands.Global.RankinSelberg.EqualUnfoldingStatement
import Langlands.Global.RankinSelberg.UnfoldingDual
import Langlands.Group.GL.MirabolicProjection
import Langlands.Global.RankinSelberg.ProjectionExpansion

/-! # Rational points, the mirabolic subgroup and the kernel of the equal-rank unfolding -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Pointwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualUnfolding

open Langlands.Global Unfolding

local instance equalKernelSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalKernelSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

section RationalPoints

/-- The map `g ↦ g` from `GL_n(F)` to `GL_n(𝔸)`, as a monoid homomorphism; its values are
the Library's `rationalPoint`. -/
def rationalPointHom (n : ℕ) : RationalGL F n →* Points F n :=
  (AdelicGroupPoints.rational F (Scheme F n)).comp
    (GeneralLinearGroupPoints.rationalEquiv F n).symm.toMonoidHom

theorem rationalPointHom_apply (n : ℕ) (g : RationalGL F n) :
    rationalPointHom F n g = rationalPoint F n g := rfl

theorem rationalPoint_mul (n : ℕ) (g h : RationalGL F n) :
    rationalPoint F n (g * h) = rationalPoint F n g * rationalPoint F n h :=
  map_mul (rationalPointHom F n) g h

theorem rationalPoint_inv (n : ℕ) (g : RationalGL F n) :
    rationalPoint F n g⁻¹ = (rationalPoint F n g)⁻¹ :=
  map_inv (rationalPointHom F n) g

theorem rationalPoint_one (n : ℕ) : rationalPoint F n 1 = 1 :=
  map_one (rationalPointHom F n)

theorem adelicEquiv_rationalPoint (n : ℕ) (g : RationalGL F n) :
    GeneralLinearGroupPoints.adelicEquiv F n (rationalPoint F n g) = AdelicGL.rational F n g := by
  rw [rationalPoint, GeneralLinearGroupPoints.adelicEquiv_rational, MulEquiv.apply_symm_apply]

theorem rationalPoint_injective (n : ℕ) : Function.Injective (rationalPoint F n) := by
  intro a b hab
  apply AdelicGL.rational_injective F n
  rw [← adelicEquiv_rationalPoint, ← adelicEquiv_rationalPoint, hab]

theorem rationalPoint_mem_rationalSubgroup (n : ℕ) (g : RationalGL F n) :
    rationalPoint F n g ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n) := ⟨_, rfl⟩

theorem exists_rationalPoint_eq (n : ℕ) {x : Points F n}
    (hx : x ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n)) :
    ∃ g : RationalGL F n, rationalPoint F n g = x := by
  obtain ⟨q, rfl⟩ := hx
  exact ⟨GeneralLinearGroupPoints.rationalEquiv F n q, by
    simp only [rationalPoint, MulEquiv.symm_apply_apply]⟩

/-- `rationalPoint g` lies in `N_n(F)` exactly when `g` is upper unitriangular. -/
theorem rationalPoint_mem_unipotentRationalImage_iff (n : ℕ) (g : RationalGL F n) :
    rationalPoint F n g ∈ unipotentRationalImage F n ↔
      g ∈ GeneralLinear.upperUnipotent n F := by
  rw [mem_unipotentRationalImage_iff_mem_inf]
  simp only [rationalPoint_mem_rationalSubgroup, true_and]
  rw [mem_unipotentAdelic_iff, adelicEquiv_rationalPoint]
  have hinj := AdeleRing.algebraMap_injective (𝓞 F) F
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => hinj ?_, fun i => hinj ?_⟩
    · have := h1 hij
      rw [AdelicGL.rational_apply] at this
      rw [this, map_zero]
    · have := h2 i
      rw [AdelicGL.rational_apply] at this
      rw [this, map_one]
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [AdelicGL.rational_apply]
      rw [show (g : Matrix (Fin n) (Fin n) F) i j = 0 from h1 hij, map_zero]
    · rw [AdelicGL.rational_apply, h2 i, map_one]

end RationalPoints

section Mirabolic

variable (r : ℕ)

/-- The mirabolic subgroup `P_n(F)` (last row `e_n`), `n = r + 1`, as a subgroup of
`GL_n(𝔸)`. -/
def mirabolicRationalImage : Subgroup (Points F (r + 1)) :=
  (GeneralLinear.mirabolic r F).map (rationalPointHom F (r + 1))

theorem mirabolicRationalImage_le :
    mirabolicRationalImage F r ≤ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)) := by
  rintro x ⟨g, -, rfl⟩
  exact rationalPoint_mem_rationalSubgroup F _ g

theorem isDiscrete_mirabolicRationalImage :
    IsDiscrete (mirabolicRationalImage F r : Set (Points F (r + 1))) :=
  (AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F (r + 1))).mono
    (mirabolicRationalImage_le F r)

theorem rationalPoint_mem_mirabolicRationalImage_iff (g : RationalGL F (r + 1)) :
    rationalPoint F (r + 1) g ∈ mirabolicRationalImage F r ↔ g ∈ GeneralLinear.mirabolic r F := by
  constructor
  · rintro ⟨h, hh, he⟩
    rwa [← rationalPoint_injective F _ he]
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem unipotentRationalImage_le_mirabolicRationalImage :
    unipotentRationalImage F (r + 1) ≤ mirabolicRationalImage F r := by
  intro x hx
  obtain ⟨g, rfl⟩ := exists_rationalPoint_eq F _ (unipotentRationalImage_le F _ hx)
  rw [rationalPoint_mem_unipotentRationalImage_iff] at hx
  exact (rationalPoint_mem_mirabolicRationalImage_iff F r g).mpr
    (GeneralLinear.upperUnipotent_le_mirabolic hx)

omit [NumberField F] in
/-- `N_r(F)` is the upper unitriangular subgroup of `GL_r(F)`. -/
theorem mem_rationalUpperUnipotent_iff (g : RationalGL F r) :
    g ∈ rationalUpperUnipotent F r ↔ g ∈ GeneralLinear.upperUnipotent r F := by
  rw [rationalUpperUnipotent, Subgroup.mem_map_equiv,
    mem_rationalPoints_upperUnipotent_iff, MulEquiv.apply_symm_apply]
  rfl

/-- The corner point `diag(a, 1)` is the rational point of the Levi element. -/
theorem cornerAdelicPoint_eq (a : RationalGL F r) :
    cornerAdelicPoint F r a =
      rationalPoint F (r + 1) (GeneralLinear.Mirabolic.levi a).val := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [adelicEquiv_rationalPoint, cornerAdelicPoint, MulEquiv.apply_symm_apply]
  congr 1

theorem cornerAdelicPoint_mem_mirabolicRationalImage (a : RationalGL F r) :
    cornerAdelicPoint F r a ∈ mirabolicRationalImage F r := by
  rw [cornerAdelicPoint_eq]
  exact ⟨_, (GeneralLinear.Mirabolic.levi a).property, rfl⟩

omit [NumberField F] in
/-- A mirabolic matrix is upper unitriangular exactly when its upper-left block is. -/
theorem val_mem_upperUnipotent_iff (m : GeneralLinear.mirabolic r F) :
    m.val ∈ GeneralLinear.upperUnipotent (r + 1) F ↔
      GeneralLinear.Mirabolic.projection m ∈ GeneralLinear.upperUnipotent r F := by
  have hl : ∀ j, (m.val : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (Fin.last r) j =
      if j = Fin.last r then 1 else 0 := m.property
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · exact h1 (show j.castSucc < i.castSucc from Fin.castSucc_lt_castSucc_iff.mpr hij)
    · exact h2 i.castSucc
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · induction i using Fin.lastCases with
      | last =>
        exact (hl j).trans (ite_eq_right_of_eq_false _ _ (eq_false (ne_of_lt hij)))
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.mpr (Fin.le_last _))
        | cast j =>
          exact h1 (show j < i from Fin.castSucc_lt_castSucc_iff.mp hij)
    · induction i using Fin.lastCases with
      | last => simpa using hl (Fin.last r)
      | cast i => exact h2 i

/-- Each point of `P_n(F)` lies in exactly one coset `N_n(F) diag(γ, 1)`, for `γ` running
over the chosen representatives of `N_r(F) \ GL_r(F)`. -/
theorem existsUnique_cornerAdelicPoint {p : Points F (r + 1)}
    (hp : p ∈ mirabolicRationalImage F r) :
    ∃! q : UnipotentRationalCosets F r,
      p * (cornerAdelicPoint F r q.out)⁻¹ ∈ unipotentRationalImage F (r + 1) := by
  obtain ⟨g, hg, rfl⟩ := hp
  set m : GeneralLinear.mirabolic r F := ⟨g, hg⟩
  have hkey : ∀ a : RationalGL F r,
      rationalPointHom F (r + 1) g * (cornerAdelicPoint F r a)⁻¹ ∈
          unipotentRationalImage F (r + 1) ↔
        GeneralLinear.Mirabolic.projection m * a⁻¹ ∈ rationalUpperUnipotent F r := by
    intro a
    have he : rationalPointHom F (r + 1) g * (cornerAdelicPoint F r a)⁻¹ =
        rationalPoint F (r + 1) (m * (GeneralLinear.Mirabolic.levi a)⁻¹).val := by
      rw [cornerAdelicPoint_eq, ← rationalPoint_inv, rationalPointHom_apply, ← rationalPoint_mul]
      rfl
    rw [he, rationalPoint_mem_unipotentRationalImage_iff, val_mem_upperUnipotent_iff,
      mem_rationalUpperUnipotent_iff, map_mul, map_inv,
      GeneralLinear.Mirabolic.projection_levi]
  refine ⟨Quotient.mk'' (GeneralLinear.Mirabolic.projection m), ?_, fun q hq => ?_⟩
  · beta_reduce
    rw [hkey]
    have h := Quotient.mk_out (s := QuotientGroup.rightRel (rationalUpperUnipotent F r))
      (GeneralLinear.Mirabolic.projection m)
    exact QuotientGroup.rightRel_apply.mp h
  · beta_reduce at hq
    rw [hkey] at hq
    rw [← Quotient.out_eq q]
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr hq)

/-- Left multiplication by `P_n(F)` does not change the last row. -/
theorem lastRow_mirabolic_mul {p : Points F (r + 1)} (hp : p ∈ mirabolicRationalImage F r)
    (x : Points F (r + 1)) : lastRow F r (p * x) = lastRow F r x := by
  obtain ⟨g, hg, rfl⟩ := hp
  ext i j
  simp only [lastRow, Matrix.of_apply, map_mul, rationalPointHom_apply,
    adelicEquiv_rationalPoint, Units.val_mul, Matrix.mul_apply, AdelicGL.rational_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [show (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (Fin.last r) (Fin.last r) = 1 by
      simpa using hg (Fin.last r), map_one, one_mul]
  · intro k _ hk
    rw [show (g : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (Fin.last r) k = 0 by
      simpa [hk] using hg k, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Left multiplication by `N_n(𝔸)` does not change the last row. -/
theorem lastRow_unipotent_mul (u : unipotentAdelic F (r + 1)) (x : Points F (r + 1)) :
    lastRow F r ((u : Points F (r + 1)) * x) = lastRow F r x := by
  have hu := isUnitriangular_of_mem_unipotentAdelic F u
  ext i j
  simp only [lastRow, Matrix.of_apply, map_mul, Units.val_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [hu.2 (Fin.last r), one_mul]
  · intro k _ hk
    have h0 : ((GeneralLinearGroupPoints.adelicEquiv F (r + 1) (u : Points F (r + 1)) :
        Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) (Fin.last r) k = 0 :=
      hu.1 (lt_of_le_of_ne (Fin.le_last k) hk)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem continuous_lastRow : Continuous (lastRow F r) := by
  have he : Continuous fun x : Points F (r + 1) =>
      ((GeneralLinearGroupPoints.adelicEquiv F (r + 1) x :
        Matrix.GeneralLinearGroup (Fin (r + 1)) (Adeles F)) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) :=
    Units.continuous_val.comp (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).continuous
  exact continuous_pi fun _ => continuous_pi fun j => he.matrix_elem _ _

end Mirabolic

section Kernel

variable {r : ℕ}

/-- `x ↦ f(x) f'(x) Φ(e_n x) |det x|^s` on `GL_n(𝔸)`, `n = r + 1`: with two Whittaker
functions it is the Whittaker integrand, with cusp forms the integrand over `P_n(F) \ GL_n(𝔸)`. -/
def equalKernel (f f' : Points F (r + 1) → ℂ) (Φ : RowVector F (r + 1) → ℂ) (s : ℂ)
    (x : Points F (r + 1)) : ℂ :=
  f x * f' x * Φ (lastRow F r x) * detPower F (r + 1) x s

theorem equalWhittakerIntegrand_eq (W W' : Points F (r + 1) → ℂ) (Φ : RowVector F (r + 1) → ℂ)
    (s : ℂ) (q : WhittakerQuotient F (r + 1)) :
    equalWhittakerIntegrand F W W' Φ s q = equalKernel F W W' Φ s q.out := rfl

theorem measurable_equalKernel {f f' : Points F (r + 1) → ℂ} {Φ : RowVector F (r + 1) → ℂ}
    (hf : Measurable f) (hf' : Measurable f') (hΦ : Measurable fun x => Φ (lastRow F r x))
    (s : ℂ) : Measurable (equalKernel F f f' Φ s) :=
  ((hf.mul hf').mul hΦ).mul (continuous_detPower F (r + 1) s).measurable

end Kernel


end Langlands.Global.RankinSelbergGlobal.EqualUnfolding
