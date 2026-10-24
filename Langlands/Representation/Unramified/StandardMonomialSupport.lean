import Langlands.Representation.Unramified.StandardMonomial
import Langlands.Representation.Hecke.DoubleCosetSandwich

/-! # Dominance bound for the support of the standard monomials -/

noncomputable section

namespace Langlands.Unramified

open Correspondence Matrix GeneralLinear.Cartan GeneralLinear.Iwasawa

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance supportFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance supportFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance supportFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance supportGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopology n
local instance supportGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopologicalGroup n
local instance supportGeneralLinearT2 (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance supportGeneralLinearMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance supportGeneralLinearBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩

/-- The standard uniformizer is a uniformizing element for the canonical valuation. -/
theorem standardUniformizer_isUniformizing :
    IsUniformizingElement (ValuativeRel.valuation F.Carrier) (standardUniformizer F) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have hex : e (ValuativeRel.valuation F.Carrier (standardUniformizer F : F.Carrier)) =
      WithZero.exp (-1) := by
    have h := LocalFactor.PadicAbelian.uniformizerUnit_zpow_value F.canonicalTopologicalData 1
    rw [zpow_one] at h
    exact h
  refine ⟨?_, fun y hy => ?_⟩
  · rw [← e.strictMono.lt_iff_lt, hex, map_one, WithZero.exp_lt_one_iff]
    norm_num
  · have hy0 : e (ValuativeRel.valuation F.Carrier y) ≠ 0 := by
      simpa using hy
    refine ⟨-WithZero.log (e (ValuativeRel.valuation F.Carrier y)), ?_⟩
    have key : e (ValuativeRel.valuation F.Carrier y) =
        e (ValuativeRel.valuation F.Carrier (standardUniformizer F : F.Carrier) ^
          (-WithZero.log (e (ValuativeRel.valuation F.Carrier y)))) := by
      rw [map_zpow₀, hex, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one, neg_neg,
        WithZero.exp_log hy0]
    exact e.injective key

/-- `x` is minor-dominated by `lam`: for every `k`, every `(r + 1 - k)`-minor of `x` has
valuation at most `v ϖ ^ tailSum lam k`, and `v (det x) = v ϖ ^ ∑ lam`. -/
def MinorDominated {r : ℕ} (lam : Fin (r + 1) → ℤ) (x : GeneralLinear (r + 1) F.Carrier) :
    Prop :=
  (∀ (k : ℕ) (f h : Fin (r + 1 - k) → Fin (r + 1)),
    ValuativeRel.valuation F.Carrier ((x : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier).submatrix
      f h).det ≤
      ValuativeRel.valuation F.Carrier (standardUniformizer F : F.Carrier) ^ tailSum lam k) ∧
  ValuativeRel.valuation F.Carrier (x : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier).det =
    ValuativeRel.valuation F.Carrier (standardUniformizer F : F.Carrier) ^ ∑ j, lam j

theorem tailSum_add {m : ℕ} (a b : Fin m → ℤ) (k : ℕ) :
    tailSum (a + b) k = tailSum a k + tailSum b k := by
  simp only [tailSum, Pi.add_apply, Finset.sum_add_distrib]

theorem tailSum_zero {m : ℕ} (k : ℕ) : tailSum (0 : Fin m → ℤ) k = 0 := by
  simp [tailSum]

variable {F}

theorem mem_integralRange_of_mem_spherical {r : ℕ} {k : GeneralLinear (r + 1) F.Carrier}
    (hk : k ∈ sphericalOpenSubgroup F r) :
    k ∈ integralRange (ValuativeRel.valuation F.Carrier) (r + 1) := hk

/-- A spherical element has determinant of valuation one. -/
theorem valuation_det_of_mem_spherical {r : ℕ} {k : GeneralLinear (r + 1) F.Carrier}
    (hk : k ∈ sphericalOpenSubgroup F r) :
    ValuativeRel.valuation F.Carrier (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier).det = 1 := by
  set v := ValuativeRel.valuation F.Carrier
  have h1 : v (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier).det ≤ 1 :=
    (v.mem_integer_iff _).1 (det_mem_integer _ (entry_mem_of_mem
      (mem_integralRange_of_mem_spherical hk)))
  have h2 : v ((k⁻¹ : GeneralLinear (r + 1) F.Carrier) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier).det ≤ 1 :=
    (v.mem_integer_iff _).1 (det_mem_integer _ (entry_mem_of_mem
      (mem_integralRange_of_mem_spherical (inv_mem hk))))
  have h3 : (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier).det *
      ((k⁻¹ : GeneralLinear (r + 1) F.Carrier) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have h4 := congrArg v h3
  rw [map_mul, map_one] at h4
  refine le_antisymm h1 ?_
  calc (1 : ValuativeRel.ValueGroupWithZero F.Carrier) = _ := h4.symm
    _ ≤ v (k : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier).det * 1 := mul_le_mul' le_rfl h2
    _ = _ := mul_one _

theorem minorDominated_integral_mul {r : ℕ} {lam : Fin (r + 1) → ℤ}
    {k x : GeneralLinear (r + 1) F.Carrier} (hk : k ∈ sphericalOpenSubgroup F r)
    (hx : MinorDominated F lam x) : MinorDominated F lam (k * x) := by
  refine ⟨fun j f h => ?_, ?_⟩
  · rw [Units.val_mul]
    exact minor_mul_left_le (entry_mem_of_mem (mem_integralRange_of_mem_spherical hk))
      (hx.1 j) f h
  · rw [Units.val_mul, Matrix.det_mul, map_mul, valuation_det_of_mem_spherical hk, one_mul, hx.2]

theorem minorDominated_mul_integral {r : ℕ} {lam : Fin (r + 1) → ℤ}
    {k x : GeneralLinear (r + 1) F.Carrier} (hk : k ∈ sphericalOpenSubgroup F r)
    (hx : MinorDominated F lam x) : MinorDominated F lam (x * k) := by
  refine ⟨fun j f h => ?_, ?_⟩
  · rw [Units.val_mul]
    exact minor_mul_right_le (entry_mem_of_mem (mem_integralRange_of_mem_spherical hk))
      (hx.1 j) f h
  · rw [Units.val_mul, Matrix.det_mul, map_mul, valuation_det_of_mem_spherical hk, mul_one, hx.2]

theorem minorDominated_one (r : ℕ) : MinorDominated F (0 : Fin (r + 1) → ℤ) 1 := by
  refine ⟨fun k f h => ?_, ?_⟩
  · rw [tailSum_zero, zpow_zero]
    exact (Valuation.mem_integer_iff _ _).1 (det_mem_integer _ fun i j => entry_mem_of_mem
      (mem_integralRange_of_mem_spherical (one_mem (sphericalOpenSubgroup F r))) (f i) (h j))
  · simp

theorem diagonal_mul_submatrix {m l : ℕ} (d : Fin m → F.Carrier)
    (X : Matrix (Fin m) (Fin m) F.Carrier) (f h : Fin l → Fin m) :
    (diagonal d * X).submatrix f h = diagonal (d ∘ f) * X.submatrix f h := by
  ext s t
  simp [Matrix.diagonal_mul]

/-- Left multiplication by a torus element with antitone exponent adds the tail sums. -/
theorem minorDominated_torus_mul {r : ℕ} {lam b : Fin (r + 1) → ℤ} (hb : Antitone b)
    {x : GeneralLinear (r + 1) F.Carrier} (hx : MinorDominated F lam x) :
    MinorDominated F (b + lam) (standardTorus F b * x) := by
  set v := ValuativeRel.valuation F.Carrier
  have hϖ := standardUniformizer_isUniformizing F
  have hpos : (0 : ValuativeRel.ValueGroupWithZero F.Carrier) <
      v (standardUniformizer F : F.Carrier) :=
    (Valuation.pos_iff v).2 (Units.ne_zero _)
  refine ⟨fun k f h => ?_, ?_⟩
  · by_cases hf : Function.Injective f
    · rw [Units.val_mul, standardTorus, torus_val, diagonal_mul_submatrix, Matrix.det_mul,
        Matrix.det_diagonal, map_mul, tailSum_add, zpow_add₀ hpos.ne']
      refine mul_le_mul' ?_ (hx.1 k f h)
      rw [map_prod]
      simp only [Function.comp_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]
      rw [prod_zpow_eq _ hpos.ne']
      exact (zpow_le_zpow_iff_right_of_lt_one₀ hpos hϖ.1).2 (tailSum_le_sum hb k f hf)
    · obtain ⟨s, t, hst, hne⟩ : ∃ s t, f s = f t ∧ s ≠ t := by
        simp only [Function.Injective, not_forall] at hf
        obtain ⟨s, t, hst, hne⟩ := hf
        exact ⟨s, t, hst, hne⟩
      rw [Matrix.det_zero_of_row_eq hne (by funext j; simp [hst]), map_zero]
      exact zero_le
  · rw [Units.val_mul, Matrix.det_mul, map_mul, hx.2, standardTorus, torus_val,
      Matrix.det_diagonal, map_prod]
    simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
    rw [prod_zpow_eq _ hpos.ne', ← zpow_add₀ hpos.ne', ← Finset.sum_add_distrib]
    rfl

/-- Left multiplication by an element of the double coset of `ϖ ^ b`, `b` antitone. -/
theorem minorDominated_doubleCoset_mul {r : ℕ} {lam b : Fin (r + 1) → ℤ} (hb : Antitone b)
    {x y : GeneralLinear (r + 1) F.Carrier}
    (hy : y ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r) (standardTorus F b))
    (hx : MinorDominated F lam x) : MinorDominated F (b + lam) (y * x) := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (Hecke.TestFunction.mem_doubleCosetSet _ _ _).1 hy
  rw [mul_assoc, mul_assoc]
  exact minorDominated_integral_mul hk₁
    (minorDominated_torus_mul hb (minorDominated_integral_mul hk₂ hx))

/-- Minor domination of an antitone torus element is dominance of exponents. -/
theorem le_of_minorDominated_torus {r : ℕ} {lam ν : Fin (r + 1) → ℤ}
    (h : MinorDominated F lam (standardTorus F ν)) :
    (∀ k, tailSum lam k ≤ tailSum ν k) ∧ ∑ j, ν j = ∑ j, lam j := by
  set v := ValuativeRel.valuation F.Carrier
  have hϖ := standardUniformizer_isUniformizing F
  have hpos : (0 : ValuativeRel.ValueGroupWithZero F.Carrier) <
      v (standardUniformizer F : F.Carrier) :=
    (Valuation.pos_iff v).2 (Units.ne_zero _)
  refine ⟨fun k => ?_, ?_⟩
  · have hbound := h.1 k (tailIndex (r + 1) k) (tailIndex (r + 1) k)
    rw [standardTorus, torus_val, submatrix_diagonal _ _ (tailIndex_injective (r + 1) k),
      det_diagonal, map_prod] at hbound
    simp only [Function.comp_apply, Units.val_zpow_eq_zpow_val, map_zpow₀] at hbound
    rw [prod_zpow_eq _ hpos.ne', sum_tailIndex] at hbound
    exact (zpow_le_zpow_iff_right_of_lt_one₀ hpos hϖ.1).1 hbound
  · have hd := h.2
    rw [standardTorus, torus_val, det_diagonal, map_prod] at hd
    simp only [Units.val_zpow_eq_zpow_val, map_zpow₀] at hd
    rw [prod_zpow_eq _ hpos.ne'] at hd
    exact le_antisymm ((zpow_le_zpow_iff_right_of_lt_one₀ hpos hϖ.1).1 hd.ge)
      ((zpow_le_zpow_iff_right_of_lt_one₀ hpos hϖ.1).1 hd.le)

variable (F)

/-- The support of a corner element is minor-dominated by `lam`. -/
def SupportDominated {r : ℕ} (f : SphericalHeckeAlgebra F r) (lam : Fin (r + 1) → ℤ) : Prop :=
  ∀ x, f x ≠ 0 → MinorDominated F lam x

variable {F}

/-- The support of a product lies in the product of the supports. -/
theorem exists_of_mul_apply_ne_zero {r : ℕ} {f g : SphericalHeckeAlgebra F r}
    {x : GeneralLinear (r + 1) F.Carrier} (h : (f * g) x ≠ 0) :
    ∃ y, f y ≠ 0 ∧ g (y⁻¹ * x) ≠ 0 := by
  by_contra hne
  simp only [not_exists, not_and, not_not, ne_eq] at hne
  apply h
  rw [Hecke.HeckeAlgebra.Corner.mul_apply]
  have : (fun y => f y * g (y⁻¹ * x)) = fun _ => 0 := by
    funext y
    by_cases hy : f y = 0
    · rw [hy, zero_mul]
    · rw [hne y hy, mul_zero]
  rw [this, MeasureTheory.integral_zero]

theorem supportDominated_one (r : ℕ) :
    SupportDominated F (1 : SphericalHeckeAlgebra F r) 0 := by
  intro x hx
  rw [Hecke.HeckeAlgebra.Corner.one_apply] at hx
  have hxK : x ∈ (sphericalOpenSubgroup F r : Set (GeneralLinear (r + 1) F.Carrier)) := by
    by_contra hn
    rw [Set.indicator_of_notMem hn, mul_zero] at hx
    exact hx rfl
  simpa using minorDominated_mul_integral hxK (minorDominated_one (F := F) r)

/-- The exponent of the `i`-th standard diagonal element. -/
def standardExponent {r : ℕ} (i : Fin (r + 2)) : Fin (r + 1) → ℤ :=
  fun j => if j.val < i.val then 1 else 0

theorem standardExponent_antitone {r : ℕ} (i : Fin (r + 2)) :
    Antitone (standardExponent (r := r) i) := by
  intro j l hjl
  simp only [standardExponent]
  split_ifs with h1 h2 <;> omega

theorem standardDiagonal_eq_torus {r : ℕ} (i : Fin (r + 2)) :
    standardDiagonal F r i = standardTorus F (standardExponent i) := by
  unfold standardDiagonal standardTorus torus standardExponent
  congr 1
  funext j
  split_ifs <;> simp

theorem supportDominated_standard_mul {r : ℕ} (i : Fin (r + 2)) {g : SphericalHeckeAlgebra F r}
    {lam : Fin (r + 1) → ℤ} (hg : SupportDominated F g lam) :
    SupportDominated F (standardHeckeElement F r i * g) (standardExponent i + lam) := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := exists_of_mul_apply_ne_zero hx
  have hyD : y ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r)
      (standardTorus F (standardExponent i)) := by
    rw [standardHeckeElement_apply] at hy
    by_contra hn
    rw [standardDiagonal_eq_torus, Set.indicator_of_notMem hn] at hy
    exact hy rfl
  have := minorDominated_doubleCoset_mul (standardExponent_antitone i) hyD (hg _ hyx)
  rwa [mul_inv_cancel_left] at this

theorem supportDominated_pow_mul {r : ℕ} (i : Fin (r + 2)) (n : ℕ)
    {g : SphericalHeckeAlgebra F r} {lam : Fin (r + 1) → ℤ} (hg : SupportDominated F g lam) :
    SupportDominated F (standardHeckeElement F r i ^ n * g) (n • standardExponent i + lam) := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [pow_succ', mul_assoc, succ_nsmul', add_assoc]
    exact supportDominated_standard_mul i ih

theorem supportDominated_list {r : ℕ} (l : List (Fin (r + 2) × ℕ)) :
    SupportDominated F (l.map fun q => standardHeckeElement F r q.1 ^ q.2).prod
      (l.map fun q => q.2 • standardExponent q.1).sum := by
  induction l with
  | nil => exact supportDominated_one r
  | cons q l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons]
    exact supportDominated_pow_mul q.1 q.2 ih

theorem monomialExponent_eq_sum {r : ℕ} (a : Fin (r + 2) → ℕ) :
    monomialExponent a = ∑ i, a i • standardExponent i := by
  funext j
  simp only [monomialExponent, Finset.sum_apply, Pi.smul_apply, standardExponent]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem supportDominated_standardMonomial {r : ℕ} (a : Fin (r + 2) → ℕ) :
    SupportDominated F (standardMonomial F a) (monomialExponent a) := by
  have h := supportDominated_list (F := F) (List.ofFn fun i => (i, a i))
  rw [List.map_ofFn, List.map_ofFn, List.sum_ofFn] at h
  rw [monomialExponent_eq_sum]
  exact h

/-- The support part of the triangularity of the standard monomials. -/
theorem standardMonomial_support {r : ℕ} (a : Fin (r + 2) → ℕ)
    (x : GeneralLinear (r + 1) F.Carrier) (hx : standardMonomial F a x ≠ 0) :
    ∃ ν : Fin (r + 1) → ℤ, Antitone ν ∧
      x ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r) (standardTorus F ν) ∧
      (∀ k, tailSum (monomialExponent a) k ≤ tailSum ν k) ∧
      ∑ j, ν j = ∑ j, monomialExponent a j := by
  have hdom := supportDominated_standardMonomial (F := F) a x hx
  obtain ⟨ν, hν, k₁, hk₁, k₂, hk₂, hx'⟩ :=
    exists_cartan (standardUniformizer_isUniformizing F) (r + 1) x
  have hk₁' : k₁ ∈ sphericalOpenSubgroup F r := hk₁
  have hk₂' : k₂ ∈ sphericalOpenSubgroup F r := hk₂
  refine ⟨ν, hν, (Hecke.TestFunction.mem_doubleCosetSet _ _ _).2 ⟨k₁, hk₁', k₂, hk₂', hx'⟩, ?_⟩
  have ht : standardTorus F ν = k₁⁻¹ * x * k₂⁻¹ := by
    rw [hx']
    simp [standardTorus, mul_assoc]
  have hdomt : MinorDominated F (monomialExponent a) (standardTorus F ν) := by
    rw [ht]
    exact minorDominated_mul_integral (inv_mem hk₂') (minorDominated_integral_mul (inv_mem hk₁') hdom)
  exact le_of_minorDominated_torus hdomt

end Langlands.Unramified
