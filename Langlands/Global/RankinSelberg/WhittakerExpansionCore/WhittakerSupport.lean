import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerCosets
import Langlands.Global.FiniteAdelicGL.StandardIntegralCompact

/-! # Finite-level support of Whittaker terms

If `f` is right invariant under an open subgroup `L` of `GL_(r+1)(𝔸_f)`, then the last row `ξ`
of `γ ∈ GL_(j+1)(F)` with `W_f(diag(γ, I) ρ x) ≠ 0` has bounded denominators: there is a
positive integer `D₀`, depending only on `f`, `ψ` and a compact set `C ∋ x`, with
`D₀ e² ξ` integral whenever `e ρ` and `e ρ⁻¹` are integral. The proof translates by finite
column points `1 + colMatrix(c)`: conjugated by `ρ x`, they lie in `L` once `c ∈ D₀ e² Ô`
(an absorption argument in the compact group `GL_(r+1)(Ô)`), so the character
`c ↦ ψ(b ξ c)` is trivial on `D₀ e² Ô^(j+1)`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter Topology
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints PrimitiveAdelicHeight Langlands.Automorphic.CuspidalWhittaker

local instance supportSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance supportSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section Absorption

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Absorption.** For an open compact subgroup `U`, an open subgroup `L` and a compact set
`Q`, some positive power `δ` satisfies `x⁻¹ g^δ x ∈ L` for all `g ∈ U` and `x ∈ Q`. -/
theorem exists_pow_conj_mem (U : Subgroup G) (hUc : IsCompact (U : Set G))
    (L : Subgroup G) (hL : IsOpen (L : Set G)) {Q : Set G} (hQ : IsCompact Q) :
    ∃ δ : ℕ, 0 < δ ∧ ∀ g ∈ U, ∀ x ∈ Q, x⁻¹ * g ^ δ * x ∈ L := by
  let H : Subgroup G :=
    { carrier := {g | ∀ x ∈ Q, x⁻¹ * g * x ∈ L}
      mul_mem' := fun {a b} ha hb x hx => by
        have h := L.mul_mem (ha x hx) (hb x hx)
        simpa only [mul_assoc, mul_inv_cancel_left] using h
      one_mem' := fun x _ => by
        simp only [mul_one, inv_mul_cancel]
        exact L.one_mem
      inv_mem' := fun {a} ha x hx => by
        have h := L.inv_mem (ha x hx)
        simpa only [mul_inv_rev, inv_inv, mul_assoc] using h }
  have hHn : (H : Set G) ∈ 𝓝 (1 : G) := by
    have h := hQ.eventually_forall_of_forall_eventually (x₀ := (1 : G))
      (P := fun g x => x⁻¹ * g * x ∈ L) (fun y _ => by
        have hc : Continuous (fun p : G × G => p.2⁻¹ * p.1 * p.2) := by fun_prop
        have h1 : (fun p : G × G => p.2⁻¹ * p.1 * p.2) (1, y) ∈ L := by
          simp only [mul_one, inv_mul_cancel]
          exact L.one_mem
        exact hc.continuousAt.preimage_mem_nhds (hL.mem_nhds h1))
    exact h
  have hHo : IsOpen (H : Set G) := H.isOpen_of_mem_nhds hHn
  have : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  let K := H.subgroupOf U
  have hKo : IsOpen (K : Set U) := hHo.preimage continuous_subtype_val
  have : Finite (U ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKo
  have : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨K.normalCore.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero,
    fun g hg x hx => ?_⟩
  have h1 := K.normalCore.pow_index_mem (⟨g, hg⟩ : U)
  have h2 : (⟨g, hg⟩ : U) ^ K.normalCore.index ∈ K := K.normalCore_le h1
  rw [Subgroup.mem_subgroupOf] at h2
  exact h2 x hx

end Absorption

section SquareZero

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The unit `1 + Y` for a square-zero matrix `Y`, with inverse `1 - Y`. -/
def sqZeroUnit (Y : Matrix (Fin n) (Fin n) A) (hY : Y * Y = 0) :
    Matrix.GeneralLinearGroup (Fin n) A where
  val := 1 + Y
  inv := 1 - Y
  val_inv := by rw [add_mul, one_mul, mul_sub, mul_one, hY, sub_zero, sub_add_cancel]
  inv_val := by rw [sub_mul, one_mul, mul_add, mul_one, hY, add_zero, add_sub_cancel_right]

theorem val_sqZeroUnit_pow (Y : Matrix (Fin n) (Fin n) A) (hY : Y * Y = 0) (k : ℕ) :
    ((sqZeroUnit Y hY ^ k : Matrix.GeneralLinearGroup (Fin n) A) :
      Matrix (Fin n) (Fin n) A) = 1 + k • Y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Units.val_mul, ih]
    change (1 + k • Y) * (1 + Y) = _
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hY, smul_zero, add_zero, succ_nsmul]
    abel

end SquareZero

variable (F : Type u) [Field F] [NumberField F]

section Coordinates

/-- The finite coordinates `y_f ∈ GL_n(𝔸_f)` of an adelic point. -/
def finCoord {n : ℕ} (y : Points F n) : FiniteAdelicGL F n :=
  AdelicGL.finite F n (GeneralLinearGroupPoints.adelicEquiv F n y)

theorem finCoord_mul {n : ℕ} (x y : Points F n) :
    finCoord F (x * y) = finCoord F x * finCoord F y := by
  simp only [finCoord, map_mul]

theorem finCoord_inv {n : ℕ} (x : Points F n) : finCoord F x⁻¹ = (finCoord F x)⁻¹ := by
  simp only [finCoord, map_inv]

theorem continuous_finCoord {n : ℕ} : Continuous (finCoord F (n := n)) := by
  unfold finCoord
  exact (AdelicGL.finite F n).continuous.comp
    (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous

theorem finCoord_ratPoint_apply {n : ℕ} (ρ : RationalGL F n) (a b : Fin n) :
    ((finCoord F (ratPoint F ρ) : FiniteAdelicGL F n) :
      Matrix (Fin n) (Fin n) (FiniteAdeles F)) a b =
      algebraMap F (FiniteAdeles F) ((ρ : Matrix (Fin n) (Fin n) F) a b) := by
  simp only [finCoord, ratPoint, MulEquiv.apply_symm_apply]
  rfl

/-- Conjugating a point with trivial archimedean part gives a finite point. -/
theorem inv_mul_mul_eq_finitePoint {n : ℕ} (P y : Points F n)
    (hP : AdelicGL.infinite F n (GeneralLinearGroupPoints.adelicEquiv F n P) = 1) :
    y⁻¹ * P * y = finitePoint F n ((finCoord F y)⁻¹ * finCoord F P * finCoord F y) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  simp only [finitePoint, MulEquiv.apply_symm_apply, map_mul, map_inv]
  apply AdelicGL.ext_infinite_finite
  · simp only [map_mul, map_inv, AdelicGL.infinite_ofFinite, hP, mul_one, inv_mul_cancel,
      inv_one]
  · simp only [map_mul, map_inv, AdelicGL.finite_ofFinite, finCoord]

variable {r : ℕ} (j : ℕ)

/-- The column of finite adeles `c`, as adeles with zero archimedean part. -/
def finCol (c : Fin (r + 1) → FiniteAdeles F) : Fin (r + 1) → Adeles F :=
  fun a => EqualAnalytic.finiteAdele F (c a)

theorem infinite_colPoint_finCol (c : Fin (r + 1) → FiniteAdeles F) :
    AdelicGL.infinite F (r + 1)
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (colPoint F (j := j) (finCol F c))) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro a b
  change (pointMatrix F (colPoint F (j := j) (finCol F c)) a b).1 = _
  rw [pointMatrix_colPoint, Matrix.add_apply, colMatrix_apply, Units.val_one, Matrix.one_apply,
    Matrix.one_apply, adeles_add_fst]
  split_ifs <;> simp [finCol, EqualAnalytic.finiteAdele] <;> rfl

theorem finCoord_colPoint_finCol (c : Fin (r + 1) → FiniteAdeles F) :
    ((finCoord F (colPoint F (j := j) (finCol F c)) : FiniteAdelicGL F (r + 1)) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteAdeles F)) = 1 + colMatrix j c := by
  apply Matrix.ext
  intro a b
  change (pointMatrix F (colPoint F (j := j) (finCol F c)) a b).2 = _
  rw [pointMatrix_colPoint, Matrix.add_apply, colMatrix_apply, Matrix.add_apply, colMatrix_apply,
    Matrix.one_apply, Matrix.one_apply, adeles_add_snd]
  split_ifs <;> simp [finCol, EqualAnalytic.finiteAdele] <;> rfl

omit [NumberField F] in
theorem colMatrix_nsmul {A : Type*} [CommRing A] (k : ℕ) (c : Fin (r + 1) → A) :
    colMatrix j (k • c) = k • colMatrix j c := by
  refine Matrix.ext fun a b => ?_
  simp only [colMatrix_apply, Matrix.smul_apply, Pi.smul_apply]
  split_ifs <;> simp

theorem isColSupported_finCol {c : Fin (r + 1) → FiniteAdeles F} (hc : IsColSupported j c) :
    IsColSupported j (finCol F c) := by
  intro a ha
  simp only [finCol, hc a ha]
  rfl

end Coordinates

section Integrality

theorem algebraMap_mem_integralFiniteAdeles {x : F} (hx : IsIntegral ℤ x) :
    algebraMap F (FiniteAdeles F) x ∈ integralFiniteAdeles F := by
  exact algebraMap_integer_mem F ⟨x, hx⟩

theorem exists_nat_mul_isIntegral (x : F) : ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : F) * x) := by
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset F)
  have h := hint x (Finset.mem_singleton_self x)
  rw [zsmul_eq_mul] at h
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  have hc : ((y.natAbs : ℕ) : F) = ((y.natAbs : ℤ) : F) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq y with h' | h'
  · rw [hc, ← h']
    exact h
  · have : ((y.natAbs : ℤ)) = -y := by omega
    rw [hc, this, Int.cast_neg, neg_mul]
    exact h.neg

/-- The integral elements of `GL_n(𝔸_f)` of the form `1 + Y`, `Y` integral and square-zero. -/
theorem sqZeroUnit_mem_standardIntegral {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) (FiniteAdeles F)) (hY : Y * Y = 0)
    (hYi : ∀ a b, Y a b ∈ integralFiniteAdeles F) :
    sqZeroUnit Y hY ∈ FiniteAdelicGL.standardIntegral F n := by
  rw [FiniteAdelicGL.mem_standardIntegral_iff]
  have h1 : ∀ a b, (1 : Matrix (Fin n) (Fin n) (FiniteAdeles F)) a b ∈
      integralFiniteAdeles F := fun a b => by
    rw [Matrix.one_apply]
    split_ifs
    · exact (integralFiniteAdeles F).one_mem
    · exact (integralFiniteAdeles F).zero_mem
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · change (1 + Y) a b ∈ FiniteAdelicGL.integralAdeles F
    rw [FiniteAdelicGL.integralAdeles_eq_integralFiniteAdeles, Matrix.add_apply]
    exact add_mem (h1 a b) (hYi a b)
  · change (1 - Y) a b ∈ FiniteAdelicGL.integralAdeles F
    rw [FiniteAdelicGL.integralAdeles_eq_integralFiniteAdeles, Matrix.sub_apply]
    exact sub_mem (h1 a b) (hYi a b)

end Integrality

section Conjugation

variable {r : ℕ} (j : ℕ)

/-- **Conjugated finite column.** If `e ρ` and `e ρ⁻¹` are integral and `c'` is an integral
column, then `ρ_f⁻¹ (1 + colMatrix(δ e² c')) ρ_f = (1 + Y)^δ` with `Y` integral and
square-zero. -/
theorem exists_conj_colPoint_eq_pow (ρ : RationalGL F (r + 1)) {e : ℕ}
    (he : ∀ a b, IsIntegral ℤ ((e : F) * (ρ : Matrix (Fin (r + 1)) (Fin (r + 1)) F) a b))
    (hei : ∀ a b, IsIntegral ℤ ((e : F) *
      ((ρ⁻¹ : RationalGL F (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) a b))
    (c' : Fin (r + 1) → FiniteAdeles F) (hc' : ∀ a, c' a ∈ integralFiniteAdeles F) (δ : ℕ) :
    ∃ g ∈ FiniteAdelicGL.standardIntegral F (r + 1),
      (finCoord F (ratPoint F ρ))⁻¹ *
          finCoord F (colPoint F (j := j) (finCol F ((δ * e ^ 2) • c'))) *
          finCoord F (ratPoint F ρ) = g ^ δ := by
  set P := finCoord F (ratPoint F ρ) with hPdef
  set ρf : Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteAdeles F) :=
    ((P : FiniteAdelicGL F (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteAdeles F))
    with hρf
  set ρfi : Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteAdeles F) :=
    ((P⁻¹ : FiniteAdelicGL F (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (FiniteAdeles F))
    with hρfi
  have hinv1 : ρf * ρfi = 1 := by rw [hρf, hρfi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinv2 : ρfi * ρf = 1 := by rw [hρf, hρfi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPi : P⁻¹ = finCoord F (ratPoint F ρ⁻¹) := by rw [hPdef, ratPoint_inv, finCoord_inv]
  set C := colMatrix j c' with hC
  set Y := ρfi * ((e ^ 2) • C) * ρf with hY
  have hYY : Y * Y = 0 := by
    simp only [hY, mul_assoc]
    rw [← mul_assoc ρf ρfi, hinv1, one_mul, ← mul_assoc ((e ^ 2) • C), smul_mul_smul_comm,
      hC, colMatrix_mul_colMatrix, smul_zero, zero_mul, mul_zero]
  have hYform : Y = (e • ρfi) * C * (e • ρf) := by
    rw [hY]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sq]
  have hρfi_int : ∀ a b, (e • ρfi) a b ∈ integralFiniteAdeles F := fun a b => by
    rw [Matrix.smul_apply, hρfi, hPi, finCoord_ratPoint_apply, nsmul_eq_mul, ← map_natCast
      (algebraMap F (FiniteAdeles F)), ← map_mul]
    exact algebraMap_mem_integralFiniteAdeles F (hei a b)
  have hρf_int : ∀ a b, (e • ρf) a b ∈ integralFiniteAdeles F := fun a b => by
    rw [Matrix.smul_apply, hρf, hPdef, finCoord_ratPoint_apply, nsmul_eq_mul, ← map_natCast
      (algebraMap F (FiniteAdeles F)), ← map_mul]
    exact algebraMap_mem_integralFiniteAdeles F (he a b)
  have hC_int : ∀ a b, C a b ∈ integralFiniteAdeles F := fun a b => by
    rw [hC, colMatrix_apply]
    split_ifs
    · exact hc' a
    · exact (integralFiniteAdeles F).zero_mem
  have hYi : ∀ a b, Y a b ∈ integralFiniteAdeles F := fun a b => by
    rw [hYform, Matrix.mul_apply]
    refine sum_mem fun k _ => mul_mem ?_ (hρf_int k b)
    rw [Matrix.mul_apply]
    exact sum_mem fun l _ => mul_mem (hρfi_int a l) (hC_int l k)
  refine ⟨sqZeroUnit Y hYY, sqZeroUnit_mem_standardIntegral F Y hYY hYi, ?_⟩
  apply Units.ext
  rw [val_sqZeroUnit_pow, Units.val_mul, Units.val_mul, finCoord_colPoint_finCol,
    colMatrix_nsmul, ← hC]
  change ρfi * (1 + (δ * e ^ 2) • C) * ρf = 1 + δ • Y
  rw [mul_add, mul_one, add_mul, hinv2, hY]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]

end Conjugation

section Support

variable [CompactSpace (AdeleQuotient F)] {r j : ℕ} (hj : j < r)
  (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
  (f : Points F (r + 1) → ℂ)
  (hfΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x, f (k * x) = f x)
  (L : Subgroup (FiniteAdelicGL F (r + 1))) (hL : IsOpen (L : Set (FiniteAdelicGL F (r + 1))))
  (hfL : ∀ x, ∀ l ∈ L, f (x * finitePoint F (r + 1) l) = f x)

include hj hψ hfΓ hL hfL

/-- **Support.** For a compact set `C` there is a positive integer `D₀` such that, whenever
`e ρ` and `e ρ⁻¹` are integral, `x ∈ C` and `W_f(diag(γ, I) ρ x) ≠ 0`, the last row of `γ`
becomes integral after multiplication by `D₀ e²`. -/
theorem exists_support_denominator {C : Set (Points F (r + 1))} (hC : IsCompact C) :
    ∃ D₀ : ℕ, 0 < D₀ ∧ ∀ (e : ℕ) (ρ : RationalGL F (r + 1)),
      (∀ a b, IsIntegral ℤ ((e : F) * (ρ : Matrix (Fin (r + 1)) (Fin (r + 1)) F) a b)) →
      (∀ a b, IsIntegral ℤ ((e : F) *
        ((ρ⁻¹ : RationalGL F (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) a b)) →
      ∀ x ∈ C, ∀ g0 : RationalGL F (j + 1),
        whittaker F r ψ f (padRational F (by omega : j + 1 ≤ r + 1) g0 *
          (ratPoint F ρ * x)) ≠ 0 →
        ∀ b : Fin (j + 1), IsIntegral ℤ (((D₀ * e ^ 2 : ℕ) : F) *
          (g0 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j) b) := by
  obtain ⟨β, hβ0, hβ⟩ := EqualAnalytic.exists_eq_standardCharacter_mul F ψ hψ
  obtain ⟨D, hD0, hD⟩ := EqualAnalytic.exists_dual_denominator_finite F
  have hQ : IsCompact (finCoord F '' C) := hC.image (continuous_finCoord F)
  obtain ⟨δ, hδ, hδL⟩ := exists_pow_conj_mem (FiniteAdelicGL.standardIntegral F (r + 1)).toSubgroup
    (FiniteAdelicGL.isCompact_standardIntegral F (r + 1)) L hL hQ
  have hDF : ((D : 𝓞 F) : F) ≠ 0 := by exact_mod_cast hD0
  obtain ⟨m, hm0, hm⟩ := exists_nat_mul_isIntegral F (((D : F) * β)⁻¹)
  refine ⟨m * δ, Nat.mul_pos hm0 hδ, ?_⟩
  intro e ρ he hei x hx g0 hW b
  set ξb := (g0 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j) b with hξb
  set b' : Fin (r + 1) := ⟨b, by omega⟩ with hb'
  -- the character is trivial on `δ e² Ô`
  have hz : ∀ t ∈ integralFiniteAdeles F,
      adelicCharacter F (finiteToAdeles F
        (algebraMap F (FiniteAdeles F) (β * ξb * ((δ * e ^ 2 : ℕ) : F)) * t)) = 1 := by
    intro t ht
    set c' : Fin (r + 1) → FiniteAdeles F := Pi.single b' t with hc'
    have hc'i : ∀ a, c' a ∈ integralFiniteAdeles F := fun a => by
      rw [hc']
      by_cases ha : a = b'
      · subst ha
        rw [Pi.single_eq_same]
        exact ht
      · rw [Pi.single_eq_of_ne ha]
        exact (integralFiniteAdeles F).zero_mem
    set c := (δ * e ^ 2) • c' with hc
    have hcs : IsColSupported j c := by
      intro a ha
      have hne : a ≠ b' := fun h => by
        rw [h, hb'] at ha
        simp only at ha
        omega
      rw [hc, Pi.smul_apply, hc', Pi.single_eq_of_ne hne, smul_zero]
    obtain ⟨g, hg, hgeq⟩ := exists_conj_colPoint_eq_pow F j ρ he hei c' hc'i δ
    rw [← hc] at hgeq
    set z := ratPoint F ρ * x with hz
    set l := (finCoord F z)⁻¹ * finCoord F (colPoint F (j := j) (finCol F c)) * finCoord F z
      with hl
    have hlL : l ∈ L := by
      have : l = (finCoord F x)⁻¹ * g ^ δ * finCoord F x := by
        rw [hl, hz, finCoord_mul, ← hgeq]
        simp only [mul_inv_rev, mul_assoc]
      rw [this]
      exact hδL g hg _ ⟨x, hx, rfl⟩
    have hPz : colPoint F (j := j) (finCol F c) * z = z * finitePoint F (r + 1) l := by
      rw [hl, ← inv_mul_mul_eq_finitePoint F _ z (infinite_colPoint_finCol F j c)]
      group
    have h1 := whittaker_padRational_colPoint F ψ hψ f hfΓ hj g0 (finCol F c)
      (isColSupported_finCol F j hcs) z
    rw [hPz, ← mul_assoc, whittaker_mul_right_of_invariant F ψ f _
      (fun y => hfL y l hlL)] at h1
    have h2 : ψ (∑ a : Fin (r + 1), (if h : (a : ℕ) < j + 1 then
        algebraMap F (Adeles F) ((g0 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j)
          ⟨a, h⟩) else 0) * finCol F c a) = 1 := by
      have hW' : whittaker F r ψ f (padRational F (by omega : j + 1 ≤ r + 1) g0 * z) ≠ 0 := hW
      have := h1.symm
      rw [mul_eq_right₀ hW'] at this
      exact this
    have hsum : (∑ a : Fin (r + 1), (if h : (a : ℕ) < j + 1 then
        algebraMap F (Adeles F) ((g0 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j)
          ⟨a, h⟩) else 0) * finCol F c a) =
        algebraMap F (Adeles F) ξb * EqualAnalytic.finiteAdele F ((δ * e ^ 2) • t) := by
      rw [Finset.sum_eq_single b']
      · rw [dite_eq_left (by simp only [hb']; omega)]
        simp only [finCol, hc, Pi.smul_apply, hc', Pi.single_eq_same, hξb, hb']
      · intro a _ ha
        simp only [finCol, hc, Pi.smul_apply, hc', Pi.single_eq_of_ne ha, smul_zero]
        have : EqualAnalytic.finiteAdele F 0 = 0 := rfl
        rw [this, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum, hβ, ← mul_assoc, ← map_mul, EqualAnalytic.standardCharacter_mul_finiteAdele] at h2
    have h3 : algebraMap F (FiniteAdeles F) (β * ξb) * ((δ * e ^ 2) • t) =
        algebraMap F (FiniteAdeles F) (β * ξb * ((δ * e ^ 2 : ℕ) : F)) * t := by
      rw [nsmul_eq_mul]
      simp only [map_mul, map_natCast]
      ring
    rw [h3] at h2
    exact Circle.coe_eq_one.mp h2
  have h4 := hD _ hz
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeles F), ← map_mul] at h4
  obtain ⟨a, ha⟩ := EqualAnalytic.exists_eq_algebraMap_of_integral F _ h4
  have h5 : IsIntegral ℤ ((D : F) * (β * ξb * ((δ * e ^ 2 : ℕ) : F))) := by
    rw [← ha]
    exact a.isIntegral_coe
  have h6 : ((m * δ * e ^ 2 : ℕ) : F) * ξb =
      ((m : F) * ((D : F) * β)⁻¹) * ((D : F) * (β * ξb * ((δ * e ^ 2 : ℕ) : F))) := by
    push_cast
    field_simp
  rw [h6]
  exact hm.mul h5

end Support

end Langlands.Global.RankinSelbergGlobal.Unfolding
