import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Shahidi.TwoBlocks
import Langlands.Representation.Shahidi.Geometry
import Langlands.Group.GL.SingleBlock
import Langlands.Group.GL.UnramifiedCharacter
import Langlands.LocalFactor.Euler.Definitions

/-!
# Shahidi's two-block induced representations `I(s, π₁ ⊗ π₂)` and `I(-s, π₂ ⊗ π₁)`

For positive ranks `m, n`, a complex number `s` and representations `π₁` of `GL_m(F)`
and `π₂` of `GL_n(F)`, Shahidi (1984, printed pages 67 and 72) induces
`π₁ |det|^(s/2) ⊗ π₂ |det|^(-s/2)` from the standard upper parabolic of `GL_(m+n)(F)`
with Levi `GL_m × GL_n`, and compares it with the induction `I(-s, π₂ ⊗ π₁)` from the
parabolic with Levi `GL_n × GL_m`.

Both representations are the published normalized block induction
`BlockShape.productInducedOf` (respectively `TopologicalData.normalizedProductInduced`)
of a block tensor product of determinant twists. The normalizing character is the
positive square root of the explicit block modulus `|det m₁|^n / |det m₂|^m`. The
resulting covariance exponents are `(s + n)/2` and `-(s + m)/2` for the original order
and `(m - s)/2` and `(s - n)/2` for the swapped order.

The general layer works over any field with a topology and a real absolute value whose
norm-one units form an open set; for a non-archimedean local field this holds when the
absolute value is trivial on valuation units. The p-adic layer feeds the unit
`q^(-t) = exp(-t log q)` to the Library's unramified determinant characters.
-/

noncomputable section

open scoped NNReal

namespace Langlands.Shahidi

universe uH uF uV uR

open GeneralLinear

/-! ## Complex powers of positive characters -/

section ComplexPower

variable {H : Type uH} [Group H]

/-- `h ↦ δ(h)^t` for a positive character `δ` and an arbitrary complex exponent `t`,
using Mathlib's complex power of the positive real `δ(h)`. -/
def complexPower (δ : H →* ℝ≥0ˣ) (t : ℂ) : H →* ℂˣ where
  toFun h := Units.mk0 ((((δ h : ℝ≥0) : ℝ) : ℂ) ^ t)
    (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (δ h).ne_zero))))
  map_one' := by
    apply Units.ext
    simp
  map_mul' g h := by
    apply Units.ext
    simp only [map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul, Units.val_mk0]
    exact Complex.mul_cpow_ofReal_nonneg (δ g : ℝ≥0).coe_nonneg (δ h : ℝ≥0).coe_nonneg t

@[simp]
theorem complexPower_apply (δ : H →* ℝ≥0ˣ) (t : ℂ) (h : H) :
    (complexPower δ t h : ℂ) = (((δ h : ℝ≥0) : ℝ) : ℂ) ^ t := rfl

private theorem coe_ne_zero (δ : H →* ℝ≥0ˣ) (h : H) : (((δ h : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (δ h).ne_zero)

@[simp]
theorem complexPower_zero (δ : H →* ℝ≥0ˣ) : complexPower δ 0 = 1 := by
  ext h
  simp

theorem complexPower_add (δ : H →* ℝ≥0ˣ) (s t : ℂ) :
    complexPower δ (s + t) = complexPower δ s * complexPower δ t := by
  ext h
  simp only [complexPower_apply, MonoidHom.mul_apply, Units.val_mul]
  exact Complex.cpow_add s t (coe_ne_zero δ h)

theorem complexPower_neg (δ : H →* ℝ≥0ˣ) (t : ℂ) :
    complexPower δ (-t) = (complexPower δ t)⁻¹ := by
  ext h
  simp only [complexPower_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact Complex.cpow_neg _ t

/-- Complex powers are multiplicative in the positive character. -/
theorem complexPower_mul (δ₁ δ₂ : H →* ℝ≥0ˣ) (t : ℂ) :
    complexPower (δ₁ * δ₂) t = complexPower δ₁ t * complexPower δ₂ t := by
  ext h
  simp only [complexPower_apply, MonoidHom.mul_apply, Units.val_mul, NNReal.coe_mul,
    Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) t

theorem complexPower_inv (δ : H →* ℝ≥0ˣ) (t : ℂ) :
    complexPower δ⁻¹ t = (complexPower δ t)⁻¹ := by
  ext h
  simp only [complexPower_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    NNReal.coe_inv, Complex.ofReal_inv]
  exact Complex.inv_cpow_ofReal_nonneg (NNReal.coe_nonneg _) t

/-- `(δ^k)^t = δ^(k t)` for the positive real values. -/
theorem complexPower_pow (δ : H →* ℝ≥0ˣ) (k : ℕ) (t : ℂ) :
    complexPower (δ ^ k) t = complexPower δ (k * t) := by
  ext h
  simp only [complexPower_apply, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, NNReal.coe_pow]
  rw [← Real.rpow_natCast, ← Complex.cpow_mul_ofReal_nonneg (NNReal.coe_nonneg _),
    Complex.ofReal_natCast]

/-- The exponent `1/2` is the canonical positive square root used by the Library's
normalized induction. -/
theorem complexPower_half (δ : H →* ℝ≥0ˣ) :
    complexPower δ (1 / 2) = Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ) := by
  ext h
  simp only [complexPower_apply, Jacquet.complexCharacter_apply,
    Jacquet.positiveHalfCharacter_apply, Real.coe_sqrt]
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  norm_num

/-- Real exponents recover the Library's real-power characters. -/
theorem complexPower_ofReal (δ : H →* ℝ≥0ˣ) (s : ℝ) :
    complexPower δ (s : ℂ) = realPowerCharacter δ s := by
  ext h
  simp only [complexPower_apply, coe_realPowerCharacter]
  exact (Complex.ofReal_cpow (NNReal.coe_nonneg _) s).symm

theorem ker_le_ker_complexPower (δ : H →* ℝ≥0ˣ) (t : ℂ) :
    δ.ker ≤ (complexPower δ t).ker := by
  intro h hh
  rw [MonoidHom.mem_ker] at hh ⊢
  ext
  simp [hh]

/-- The scalar identity behind both covariance laws: for positive reals `x, y`,
`√(x^b / y^a) · x^t₁ y^t₂ = x^(t₁ + b/2) y^(t₂ - a/2)`. -/
theorem sqrt_mul_cpow_mul_cpow (x y : ℝ≥0ˣ) (a b : ℕ) (t₁ t₂ : ℂ) :
    ((NNReal.sqrt ((x ^ b / y ^ a : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) *
        ((((x : ℝ≥0) : ℝ) : ℂ) ^ t₁ * (((y : ℝ≥0) : ℝ) : ℂ) ^ t₂) =
      (((x : ℝ≥0) : ℝ) : ℂ) ^ (t₁ + b / 2) * (((y : ℝ≥0) : ℝ) : ℂ) ^ (t₂ - a / 2) := by
  have hx : (0 : ℝ) < ((x : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr x.ne_zero)
  have hy : (0 : ℝ) < ((y : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr y.ne_zero)
  have hx' : (((x : ℝ≥0) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hy' : (((y : ℝ≥0) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hsqrt : ((NNReal.sqrt ((x ^ b / y ^ a : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) =
      (((x : ℝ≥0) : ℝ) : ℂ) ^ ((b : ℂ) / 2) / (((y : ℝ≥0) : ℝ) : ℂ) ^ ((a : ℂ) / 2) := by
    rw [Real.coe_sqrt, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_pow,
      Real.sqrt_eq_rpow, Real.div_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_natCast ((y : ℝ≥0) : ℝ), ← Real.rpow_mul hx.le,
      ← Real.rpow_mul hy.le, Complex.ofReal_div, Complex.ofReal_cpow hx.le,
      Complex.ofReal_cpow hy.le]
    congr 2 <;> push_cast <;> ring
  rw [hsqrt, Complex.cpow_add _ _ hx', Complex.cpow_sub _ _ hy']
  field_simp

end ComplexPower

/-! ## Absolute values and determinant powers -/

section AbsoluteValue

variable {F : Type uF} [Field F] (abv : AbsoluteValue F ℝ)

/-- A real absolute value restricted to the units, as a positive character. -/
def absUnits : Fˣ →* ℝ≥0ˣ where
  toFun u := Units.mk0 ⟨abv u, abv.nonneg _⟩ (by
    intro h0
    exact u.ne_zero (abv.eq_zero.mp (congrArg Subtype.val h0)))
  map_one' := by
    apply Units.ext
    apply Subtype.ext
    change abv ((1 : Fˣ) : F) = 1
    rw [Units.val_one, abv.map_one]
  map_mul' u v := by
    apply Units.ext
    apply Subtype.ext
    change abv ((u * v : Fˣ) : F) = abv u * abv v
    rw [Units.val_mul, abv.map_mul]

@[simp]
theorem absUnits_apply (u : Fˣ) : ((absUnits abv u : ℝ≥0) : ℝ) = abv u := rfl

/-- `g ↦ |det g|` on the actual general linear group. -/
def determinantAbs (n : ℕ) : GeneralLinear n F →* ℝ≥0ˣ :=
  (absUnits abv).comp GeneralLinear.determinant

@[simp]
theorem determinantAbs_apply (n : ℕ) (g : GeneralLinear n F) :
    ((determinantAbs abv n g : ℝ≥0) : ℝ) = abv (Matrix.det g.val) := rfl

/-- The determinant twist `g ↦ |det g|^t`, for every complex `t`. -/
def determinantPower (n : ℕ) (t : ℂ) : GeneralLinear n F →* ℂˣ :=
  complexPower (determinantAbs abv n) t

/-- The value is the complex power of the real absolute value of the determinant. -/
theorem determinantPower_apply (n : ℕ) (t : ℂ) (g : GeneralLinear n F) :
    (determinantPower abv n t g : ℂ) = ((abv (Matrix.det g.val) : ℝ) : ℂ) ^ t := rfl

theorem determinantPower_add (n : ℕ) (s t : ℂ) :
    determinantPower abv n (s + t) = determinantPower abv n s * determinantPower abv n t :=
  complexPower_add _ s t

theorem determinantPower_neg (n : ℕ) (t : ℂ) :
    determinantPower abv n (-t) = (determinantPower abv n t)⁻¹ :=
  complexPower_neg _ t

@[simp]
theorem determinantPower_zero (n : ℕ) : determinantPower abv n 0 = 1 :=
  complexPower_zero _

variable [TopologicalSpace F]

/-- The smoothness hypothesis on the absolute value: its norm-one units form an open
subset of the unit group. -/
def IsOpenNormOne : Prop :=
  IsOpen ((absUnits abv).ker : Set Fˣ)

variable {abv} [IsTopologicalRing F]

theorem isOpen_ker_determinantAbs (hopen : IsOpenNormOne abv) (n : ℕ) :
    IsOpen ((determinantAbs abv n).ker : Set (GeneralLinear n F)) := by
  change IsOpen (GeneralLinear.determinant ⁻¹' ((absUnits abv).ker : Set Fˣ))
  exact hopen.preimage (GeneralLinear.determinantContinuous (R := F) (n := n)).continuous

theorem isOpen_ker_determinantPower (hopen : IsOpenNormOne abv) (n : ℕ) (t : ℂ) :
    IsOpen ((determinantPower abv n t).ker : Set (GeneralLinear n F)) :=
  Subgroup.isOpen_mono (ker_le_ker_complexPower _ t) (isOpen_ker_determinantAbs hopen n)

/-- The determinant twist as a smooth character. -/
def determinantPowerCharacter (hopen : IsOpenNormOne abv) (n : ℕ) (t : ℂ) :
    Induction.SmoothCharacter ℂ (GeneralLinear n F) :=
  ⟨determinantPower abv n t, isOpen_ker_determinantPower hopen n t⟩

/-- On a non-archimedean local field (more generally, a field with a valuative topology),
an absolute value equal to one on the valuation units satisfies the smoothness
hypothesis. This is the unit normalization `abv_unit` of the Library's Jacquet
normalization data. -/
theorem isOpenNormOne_of_valuation [ValuativeRel F] [IsValuativeTopology F]
    (habv : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1) :
    IsOpenNormOne abv := by
  have ho : IsOpen (Units.val ⁻¹' {x : F | ValuativeRel.valuation F x = 1} : Set Fˣ) := by
    refine IsOpen.preimage Units.continuous_val ?_
    simpa only [Valuation.restrict_eq_one_iff] using
      Valuation.isOpen_sphere (v := ValuativeRel.valuation F) (r := 1) one_ne_zero
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  refine Filter.mem_of_superset (ho.mem_nhds (by simp)) ?_
  intro u hu
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  apply Units.ext
  apply Subtype.ext
  exact habv u hu

end AbsoluteValue

/-! ## The explicit block modulus for an absolute value -/

section Modulus

variable {F : Type uF} [Field F] (abv : AbsoluteValue F ℝ) {r : ℕ} (B : BlockShape r)

/-- `|det m_i|` for the diagonal block `i` of the actual Levi. -/
def blockDeterminantAbs (i : Fin B.length) : B.Levi F →* ℝ≥0ˣ where
  toFun m := determinantAbs abv (B.size i) (m i)
  map_one' := map_one _
  map_mul' m m' := (determinantAbs abv (B.size i)).map_mul (m i) (m' i)

@[simp]
theorem blockDeterminantAbs_apply (i : Fin B.length) (m : B.Levi F) :
    blockDeterminantAbs abv B i m = determinantAbs abv (B.size i) (m i) := rfl

/-- The standard upper-block modulus formula `∏_{i<j} |det m_i|^(n_j) / |det m_j|^(n_i)`,
with the same shape as the p-adic `TopologicalData.leviModulus`. -/
def leviModulus : B.Levi F →* ℝ≥0ˣ :=
  ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    blockDeterminantAbs abv B i ^ B.size j / blockDeterminantAbs abv B j ^ B.size i

theorem leviModulus_apply (m : B.Levi F) :
    leviModulus abv B m =
      ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        determinantAbs abv (B.size i) (m i) ^ B.size j /
          determinantAbs abv (B.size j) (m j) ^ B.size i := by
  simp [leviModulus]

/-- The positive complex half `δ_P^(1/2)`. -/
def leviHalfModulus : B.Levi F →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (leviModulus abv B))

@[simp]
theorem leviHalfModulus_apply (m : B.Levi F) :
    (leviHalfModulus abv B m : ℂ) = ((NNReal.sqrt (leviModulus abv B m : ℝ≥0) : ℝ) : ℂ) :=
  rfl

theorem leviHalfModulus_eq_complexPower :
    leviHalfModulus abv B = complexPower (leviModulus abv B) (1 / 2) :=
  (complexPower_half _).symm

theorem leviHalfModulus_eq_one (m : B.Levi F) :
    leviHalfModulus abv B m = 1 ↔ leviModulus abv B m = 1 := by
  simpa only [Jacquet.inverseHalfCharacter, MonoidHom.inv_apply, inv_eq_one,
    leviHalfModulus] using Jacquet.inverseHalfCharacter_eq_one (leviModulus abv B) m

variable [TopologicalSpace F] [IsTopologicalRing F] {abv}

theorem isOpen_ker_leviModulus (hopen : IsOpenNormOne abv) :
    IsOpen ((leviModulus abv B).ker : Set (B.Levi F)) := by
  have hle : (⨅ i : Fin B.length, (blockDeterminantAbs abv B i).ker) ≤
      (leviModulus abv B).ker := by
    intro m hm
    have h : ∀ i, determinantAbs abv (B.size i) (m i) = 1 := fun i =>
      Subgroup.mem_iInf.mp hm i
    rw [MonoidHom.mem_ker, leviModulus_apply]
    simp [h]
  have hopenI : IsOpen ((⨅ i : Fin B.length, (blockDeterminantAbs abv B i).ker :
      Subgroup (B.Levi F)) : Set (B.Levi F)) := by
    rw [Subgroup.coe_iInf]
    refine isOpen_iInter_of_finite fun i => ?_
    change IsOpen ((fun m : B.Levi F => m i) ⁻¹'
      ((determinantAbs abv (B.size i)).ker : Set (GeneralLinear (B.size i) F)))
    exact (isOpen_ker_determinantAbs hopen (B.size i)).preimage (continuous_apply i)
  exact Subgroup.isOpen_mono hle hopenI

theorem isOpen_ker_leviHalfModulus (hopen : IsOpenNormOne abv) :
    IsOpen ((leviHalfModulus abv B).ker : Set (B.Levi F)) := by
  have h : (leviHalfModulus abv B).ker = (leviModulus abv B).ker := by
    ext m
    exact leviHalfModulus_eq_one abv B m
  rw [h]
  exact isOpen_ker_leviModulus B hopen

/-- The normalizing character `δ_P^(1/2)` of the Library's normalized induction, for
an absolute value with open norm-one units. -/
def leviHalfCharacter (hopen : IsOpenNormOne abv) :
    Induction.SmoothCharacter ℂ (B.Levi F) :=
  ⟨leviHalfModulus abv B, isOpen_ker_leviHalfModulus B hopen⟩

@[simp]
theorem leviHalfCharacter_toMonoidHom (hopen : IsOpenNormOne abv) :
    (leviHalfCharacter B hopen).toMonoidHom = leviHalfModulus abv B := rfl

end Modulus

/-! ## The swapped two-block shape -/

section Shapes

variable (m n : ℕ) (hm : 0 < m) (hn : 0 < n)

/-- The ordered block sizes `(n, m)` of Shahidi's target `I(-s, π₂ ⊗ π₁)`, kept on the
same ambient rank `m + n` as the source. -/
abbrev swappedTwoBlocks : BlockShape (m + n) where
  length := 2
  size := ![n, m]
  positive := (twoBlocks n m hn hm).positive
  sum_eq := by simp [Nat.add_comm]

/-- The swapped shape is the Library rank transport of `twoBlocks n m` along
`n + m = m + n`; no reindexing of matrix coordinates is involved. -/
theorem swappedTwoBlocks_eq_rankCast :
    swappedTwoBlocks m n hm hn = (twoBlocks n m hn hm).rankCast (Nat.add_comm n m) := rfl

variable {m n hm hn}

@[simp] theorem swappedTwoBlocks_size_zero : (swappedTwoBlocks m n hm hn).size 0 = n := rfl

@[simp] theorem swappedTwoBlocks_size_one : (swappedTwoBlocks m n hm hn).size 1 = m := rfl

/-- The generic block modulus of the standard pair of blocks. -/
theorem leviModulus_twoBlocks {F : Type uF} [Field F] (abv : AbsoluteValue F ℝ)
    (g : (twoBlocks m n hm hn).Levi F) :
    leviModulus abv (twoBlocks m n hm hn) g =
      determinantAbs abv m (g 0) ^ n / determinantAbs abv n (g 1) ^ m := by
  rw [leviModulus_apply]
  simp only [Fin.prod_univ_two, Finset.prod_filter]
  norm_num [twoBlocks]
  rfl

/-- The generic block modulus of the swapped pair of blocks. -/
theorem leviModulus_swappedTwoBlocks {F : Type uF} [Field F] (abv : AbsoluteValue F ℝ)
    (g : (swappedTwoBlocks m n hm hn).Levi F) :
    leviModulus abv (swappedTwoBlocks m n hm hn) g =
      determinantAbs abv n (g 0) ^ m / determinantAbs abv m (g 1) ^ n := by
  rw [leviModulus_apply]
  simp only [Fin.prod_univ_two, Finset.prod_filter]
  norm_num [swappedTwoBlocks]
  rfl

end Shapes

/-! ## Two-factor carriers and families -/

section Pair

variable (V₁ V₂ : Type uV)

/-- The two factor spaces `V₁, V₂` as a family indexed by the two blocks; both live in
one common universe `uV`. -/
def pairCarrier : Fin 2 → Type uV := ![V₁, V₂]

variable {V₁ V₂}

instance pairCarrier.instAddCommGroup [AddCommGroup V₁] [AddCommGroup V₂] (i : Fin 2) :
    AddCommGroup (pairCarrier V₁ V₂ i) :=
  match i with
  | 0 => inferInstanceAs (AddCommGroup V₁)
  | 1 => inferInstanceAs (AddCommGroup V₂)

instance pairCarrier.instModule (R : Type uR) [Semiring R] [AddCommGroup V₁] [Module R V₁]
    [AddCommGroup V₂] [Module R V₂] (i : Fin 2) : Module R (pairCarrier V₁ V₂ i) :=
  match i with
  | 0 => inferInstanceAs (Module R V₁)
  | 1 => inferInstanceAs (Module R V₂)

variable [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]

/-- The pair `(v₁, v₂)` as a vector family. -/
def pairVector (v₁ : V₁) (v₂ : V₂) (i : Fin 2) : pairCarrier V₁ V₂ i :=
  match i with
  | 0 => v₁
  | 1 => v₂

/-- The pure tensor `v₁ ⊗ v₂` in the Library's block tensor carrier. -/
def pairTensor (v₁ : V₁) (v₂ : V₂) : PiTensorProduct ℂ (pairCarrier V₁ V₂) :=
  PiTensorProduct.tprod ℂ (pairVector v₁ v₂)

variable {F : Type uF} [CommRing F] {a b : ℕ}

/-- A representation of each of the two diagonal blocks `GL_a × GL_b`. -/
def pairFamily (ρ₁ : Representation ℂ (GeneralLinear a F) V₁)
    (ρ₂ : Representation ℂ (GeneralLinear b F) V₂) (i : Fin 2) :
    Representation ℂ (GeneralLinear (![a, b] i) F) (pairCarrier V₁ V₂ i) :=
  match i with
  | 0 => ρ₁
  | 1 => ρ₂

@[simp] theorem pairFamily_zero (ρ₁ : Representation ℂ (GeneralLinear a F) V₁)
    (ρ₂ : Representation ℂ (GeneralLinear b F) V₂) : pairFamily ρ₁ ρ₂ 0 = ρ₁ := rfl

@[simp] theorem pairFamily_one (ρ₁ : Representation ℂ (GeneralLinear a F) V₁)
    (ρ₂ : Representation ℂ (GeneralLinear b F) V₂) : pairFamily ρ₁ ρ₂ 1 = ρ₂ := rfl

variable (ha : 0 < a) (hb : 0 < b)

/-- The block tensor of a pair acts factorwise on pure tensors. -/
theorem blockTensor_pairTensor (ρ₁ : Representation ℂ (GeneralLinear a F) V₁)
    (ρ₂ : Representation ℂ (GeneralLinear b F) V₂) (g : (twoBlocks a b ha hb).Levi F)
    (v₁ : V₁) (v₂ : V₂) :
    (twoBlocks a b ha hb).blockTensor (pairFamily ρ₁ ρ₂) g (pairTensor v₁ v₂) =
      pairTensor (ρ₁ (g 0) v₁) (ρ₂ (g 1) v₂) := by
  rw [pairTensor, BlockShape.blockTensor_tprod, pairTensor]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Twisting the two factors by characters `χ₁, χ₂` multiplies the block tensor action by
the scalar `χ₁(g₁) χ₂(g₂)`. -/
theorem blockTensor_pairFamily_twist (χ₁ : GeneralLinear a F →* ℂˣ)
    (χ₂ : GeneralLinear b F →* ℂˣ) (ρ₁ : Representation ℂ (GeneralLinear a F) V₁)
    (ρ₂ : Representation ℂ (GeneralLinear b F) V₂) (g : (twoBlocks a b ha hb).Levi F) :
    (twoBlocks a b ha hb).blockTensor (pairFamily (twist χ₁ ρ₁) (twist χ₂ ρ₂)) g =
      ((χ₁ (g 0) : ℂ) * (χ₂ (g 1) : ℂ)) •
        (twoBlocks a b ha hb).blockTensor (pairFamily ρ₁ ρ₂) g := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply,
    LinearMap.smul_apply]
  erw [BlockShape.blockTensor_tprod, BlockShape.blockTensor_tprod]
  have h : (fun i => pairFamily (twist χ₁ ρ₁) (twist χ₂ ρ₂) i (g i) (v i)) =
      fun i => (![(χ₁ (g 0) : ℂ), (χ₂ (g 1) : ℂ)] i) • pairFamily ρ₁ ρ₂ i (g i) (v i) := by
    funext i
    fin_cases i <;> rfl
  refine (congrArg (PiTensorProduct.tprod ℂ) h).trans ?_
  rw [MultilinearMap.map_smul_univ, Fin.prod_univ_two]
  rfl

end Pair

/-! ## The swapped shape and `swapRank` -/

section SwapRank

variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (R : Type uR) [CommRing R]

/-- The coordinates of the swapped shape are those of `twoBlocks n m`, cast along
`n + m = m + n`. -/
theorem swappedTwoBlocks_index (i : Fin 2) (a : Fin (![n, m] i)) :
    (swappedTwoBlocks m n hm hn).index i a =
      Fin.cast (Nat.add_comm n m) ((twoBlocks n m hn hm).index i a) :=
  Fin.ext rfl

/-- `swapRank` carries the standard parabolic of type `(n, m)` on `GL_(n+m)` exactly onto
the parabolic of the swapped shape on `GL_(m+n)`. -/
theorem swapRank_mem_swappedTwoBlocks_parabolic_iff (g : GeneralLinear (n + m) R) :
    swapRank m n R g ∈ (swappedTwoBlocks m n hm hn).parabolic R ↔
      g ∈ (twoBlocks n m hn hm).parabolic R :=
  Iff.rfl

/-- The parabolic of the swapped shape is the `swapRank` image of the parabolic of
`twoBlocks n m`. -/
def swappedParabolicEquiv :
    (twoBlocks n m hn hm).parabolic R ≃* (swappedTwoBlocks m n hm hn).parabolic R where
  toFun g := ⟨swapRank m n R g, g.property⟩
  invFun g := ⟨(swapRank m n R).symm g, by
    rw [← swapRank_mem_swappedTwoBlocks_parabolic_iff hm hn R, MulEquiv.apply_symm_apply]
    exact g.property⟩
  left_inv g := Subtype.ext ((swapRank m n R).symm_apply_apply g)
  right_inv g := Subtype.ext ((swapRank m n R).apply_symm_apply g)
  map_mul' g h := Subtype.ext ((swapRank m n R).map_mul g h)

@[simp]
theorem swappedParabolicEquiv_coe (g : (twoBlocks n m hn hm).parabolic R) :
    (swappedParabolicEquiv hm hn R g : GeneralLinear (m + n) R) = swapRank m n R g := rfl

/-- The Levi projection of the swapped shape, after `swapRank`, is the Levi projection of
`twoBlocks n m`; both Levi groups are literally `GL_n × GL_m`. -/
@[simp]
theorem leviProjection_swappedParabolicEquiv (g : (twoBlocks n m hn hm).parabolic R) :
    (swappedTwoBlocks m n hm hn).leviProjection R (swappedParabolicEquiv hm hn R g) =
      (twoBlocks n m hn hm).leviProjection R g := by
  funext i
  apply Units.ext
  ext a b
  rfl

/-- The Levi embedding of the swapped shape is `swapRank` of the block sum. -/
theorem swappedTwoBlocks_leviEmbedding (l : (swappedTwoBlocks m n hm hn).Levi R) :
    (swappedTwoBlocks m n hm hn).leviEmbedding R l =
      swapRank m n R (GeneralLinear.blockSum (l 0, l 1)) := by
  refine Eq.trans ?_ (congrArg (swapRank m n R) (twoBlocks_leviEmbedding hn hm R l))
  apply Units.ext
  ext a b
  rfl

end SwapRank

/-! ## Determinant twists of a pair -/

section Twists

variable {F : Type uF} [Field F] (abv : AbsoluteValue F ℝ)

/-- The inducing pair `ρ₁ |det|^(t/2), ρ₂ |det|^(-t/2)` on `GL_a × GL_b`. -/
def twistedPair {a b : ℕ} (t : ℂ) {W₁ W₂ : Type uV} [AddCommGroup W₁] [Module ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] (ρ₁ : Representation ℂ (GeneralLinear a F) W₁)
    (ρ₂ : Representation ℂ (GeneralLinear b F) W₂) (i : Fin 2) :
    Representation ℂ (GeneralLinear (![a, b] i) F) (pairCarrier W₁ W₂ i) :=
  pairFamily (twist (determinantPower abv a (t / 2)) ρ₁)
    (twist (determinantPower abv b (-(t / 2))) ρ₂) i

end Twists

/-! ## The general two-block induction -/

section Induction

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable (abv : AbsoluteValue F ℝ) (hopen : IsOpenNormOne abv)
variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (s : ℂ)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (GeneralLinear m F) V₁)
  (π₂ : Representation ℂ (GeneralLinear n F) V₂)

/-- The carrier of `I(s, π₁ ⊗ π₂)`: smooth functions on `GL_(m+n)(F)` with values in
`V₁ ⊗ V₂`, covariant for the standard parabolic of type `(m, n)`. -/
abbrev SourceSpace : Type (max uF uV) :=
  Induction.SmoothFunctions ((twoBlocks m n hm hn).parabolic F)
    ((twoBlocks m n hm hn).inducingRepresentation
      (leviHalfCharacter (twoBlocks m n hm hn) hopen)
      ((twoBlocks m n hm hn).blockTensor (twistedPair abv s π₁ π₂)))

/-- Shahidi's `I(s, π₁ ⊗ π₂)`: the Library's normalized induction, from the standard
parabolic with Levi `GL_m × GL_n`, of `π₁ |det|^(s/2) ⊗ π₂ |det|^(-s/2)`. -/
def source : Representation ℂ (GeneralLinear (m + n) F) (SourceSpace abv hopen hm hn s π₁ π₂) :=
  (twoBlocks m n hm hn).productInducedOf (leviHalfCharacter (twoBlocks m n hm hn) hopen)
    (twistedPair abv s π₁ π₂)

/-- The value `f(g) ∈ V₁ ⊗ V₂` of a function in `I(s, π₁ ⊗ π₂)`. -/
def sourceEval (f : SourceSpace abv hopen hm hn s π₁ π₂) (g : GeneralLinear (m + n) F) :
    PiTensorProduct ℂ (pairCarrier V₁ V₂) :=
  Induction.eval _ _ f g

/-- The underlying functions, as a linear map. -/
def sourceFunction :
    SourceSpace abv hopen hm hn s π₁ π₂ →ₗ[ℂ]
      (GeneralLinear (m + n) F → PiTensorProduct ℂ (pairCarrier V₁ V₂)) :=
  (Submodule.subtype _).comp (Submodule.subtype _)

@[simp]
theorem sourceFunction_apply (f : SourceSpace abv hopen hm hn s π₁ π₂)
    (g : GeneralLinear (m + n) F) :
    sourceFunction abv hopen hm hn s π₁ π₂ f g = sourceEval abv hopen hm hn s π₁ π₂ f g := rfl

/-- `I(s, π₁ ⊗ π₂)` is literally the Library normalized induction of the block tensor. -/
theorem source_eq :
    source abv hopen hm hn s π₁ π₂ =
      (twoBlocks m n hm hn).normalizedInducedOf (leviHalfCharacter (twoBlocks m n hm hn) hopen)
        ((twoBlocks m n hm hn).blockTensor (twistedPair abv s π₁ π₂)) := rfl

/-- The group acts by right translation. -/
@[simp]
theorem source_apply (g : GeneralLinear (m + n) F) (f : SourceSpace abv hopen hm hn s π₁ π₂)
    (x : GeneralLinear (m + n) F) :
    sourceEval abv hopen hm hn s π₁ π₂ (source abv hopen hm hn s π₁ π₂ g f) x =
      sourceEval abv hopen hm hn s π₁ π₂ f (x * g) := rfl

theorem isSmooth_source : IsSmooth (source abv hopen hm hn s π₁ π₂) :=
  (twoBlocks m n hm hn).isSmooth_productInducedOf _ _

/-- Covariance of `I(s, π₁ ⊗ π₂)` with the explicit exponents: for `p` in the standard
parabolic with diagonal blocks `g₁ ∈ GL_m`, `g₂ ∈ GL_n`,
`f(p g) = |det g₁|^((s+n)/2) |det g₂|^(-(s+m)/2) (π₁(g₁) ⊗ π₂(g₂)) f(g)`. -/
theorem source_covariant (f : SourceSpace abv hopen hm hn s π₁ π₂)
    (p : (twoBlocks m n hm hn).parabolic F) (g : GeneralLinear (m + n) F) :
    sourceEval abv hopen hm hn s π₁ π₂ f ((p : GeneralLinear (m + n) F) * g) =
      ((((abv (Matrix.det ((twoBlocks m n hm hn).leviProjection F p 0).val) : ℝ) : ℂ) ^
            ((s + n) / 2)) *
          (((abv (Matrix.det ((twoBlocks m n hm hn).leviProjection F p 1).val) : ℝ) : ℂ) ^
            (-((s + m) / 2)))) •
        (twoBlocks m n hm hn).blockTensor (pairFamily π₁ π₂)
          ((twoBlocks m n hm hn).leviProjection F p) (sourceEval abv hopen hm hn s π₁ π₂ f g) := by
  rw [sourceEval, BlockShape.productInducedOf_covariant]
  change _ • (twoBlocks m n hm hn).blockTensor
      (pairFamily (twist (determinantPower abv m (s / 2)) π₁)
        (twist (determinantPower abv n (-(s / 2))) π₂)) _ _ = _
  rw [blockTensor_pairFamily_twist, LinearMap.smul_apply, smul_smul, sourceEval]
  congr 1
  rw [leviHalfCharacter_toMonoidHom, leviHalfModulus_apply, leviModulus_twoBlocks]
  refine (sqrt_mul_cpow_mul_cpow
    (determinantAbs abv m ((twoBlocks m n hm hn).leviProjection F p 0))
    (determinantAbs abv n ((twoBlocks m n hm hn).leviProjection F p 1)) m n
    (s / 2) (-(s / 2))).trans ?_
  rw [show s / 2 + (n : ℂ) / 2 = (s + n) / 2 by ring,
    show -(s / 2) - (m : ℂ) / 2 = -((s + m) / 2) by ring]
  rfl

/-- The carrier of `I(-s, π₂ ⊗ π₁)`: smooth functions on the same group `GL_(m+n)(F)`
with values in `V₂ ⊗ V₁`, covariant for the standard parabolic of type `(n, m)`. -/
abbrev TargetSpace : Type (max uF uV) :=
  Induction.SmoothFunctions ((swappedTwoBlocks m n hm hn).parabolic F)
    ((swappedTwoBlocks m n hm hn).inducingRepresentation
      (leviHalfCharacter (swappedTwoBlocks m n hm hn) hopen)
      ((swappedTwoBlocks m n hm hn).blockTensor (twistedPair abv (-s) π₂ π₁)))

/-- Shahidi's `I(-s, π₂ ⊗ π₁)` on `GL_(m+n)(F)`: the Library's normalized induction,
from the standard parabolic with Levi `GL_n × GL_m`, of
`π₂ |det|^(-s/2) ⊗ π₁ |det|^(s/2)`. -/
def target : Representation ℂ (GeneralLinear (m + n) F) (TargetSpace abv hopen hm hn s π₁ π₂) :=
  (swappedTwoBlocks m n hm hn).productInducedOf
    (leviHalfCharacter (swappedTwoBlocks m n hm hn) hopen) (twistedPair abv (-s) π₂ π₁)

/-- The value `f(g) ∈ V₂ ⊗ V₁` of a function in `I(-s, π₂ ⊗ π₁)`. -/
def targetEval (f : TargetSpace abv hopen hm hn s π₁ π₂) (g : GeneralLinear (m + n) F) :
    PiTensorProduct ℂ (pairCarrier V₂ V₁) :=
  Induction.eval _ _ f g

/-- The underlying functions, as a linear map. -/
def targetFunction :
    TargetSpace abv hopen hm hn s π₁ π₂ →ₗ[ℂ]
      (GeneralLinear (m + n) F → PiTensorProduct ℂ (pairCarrier V₂ V₁)) :=
  (Submodule.subtype _).comp (Submodule.subtype _)

@[simp]
theorem targetFunction_apply (f : TargetSpace abv hopen hm hn s π₁ π₂)
    (g : GeneralLinear (m + n) F) :
    targetFunction abv hopen hm hn s π₁ π₂ f g = targetEval abv hopen hm hn s π₁ π₂ f g := rfl

theorem target_eq :
    target abv hopen hm hn s π₁ π₂ =
      (swappedTwoBlocks m n hm hn).normalizedInducedOf
        (leviHalfCharacter (swappedTwoBlocks m n hm hn) hopen)
        ((swappedTwoBlocks m n hm hn).blockTensor (twistedPair abv (-s) π₂ π₁)) := rfl

@[simp]
theorem target_apply (g : GeneralLinear (m + n) F) (f : TargetSpace abv hopen hm hn s π₁ π₂)
    (x : GeneralLinear (m + n) F) :
    targetEval abv hopen hm hn s π₁ π₂ (target abv hopen hm hn s π₁ π₂ g f) x =
      targetEval abv hopen hm hn s π₁ π₂ f (x * g) := rfl

theorem isSmooth_target : IsSmooth (target abv hopen hm hn s π₁ π₂) :=
  (swappedTwoBlocks m n hm hn).isSmooth_productInducedOf _ _

/-- Covariance of `I(-s, π₂ ⊗ π₁)` with the explicit exponents: for `p` in the parabolic
of type `(n, m)` with diagonal blocks `g₁ ∈ GL_n`, `g₂ ∈ GL_m`,
`f(p g) = |det g₁|^((m-s)/2) |det g₂|^((s-n)/2) (π₂(g₁) ⊗ π₁(g₂)) f(g)`. -/
theorem target_covariant (f : TargetSpace abv hopen hm hn s π₁ π₂)
    (p : (swappedTwoBlocks m n hm hn).parabolic F) (g : GeneralLinear (m + n) F) :
    targetEval abv hopen hm hn s π₁ π₂ f ((p : GeneralLinear (m + n) F) * g) =
      ((((abv (Matrix.det ((swappedTwoBlocks m n hm hn).leviProjection F p 0).val) : ℝ) : ℂ) ^
            ((m - s) / 2)) *
          (((abv (Matrix.det ((swappedTwoBlocks m n hm hn).leviProjection F p 1).val) : ℝ) :
              ℂ) ^ ((s - n) / 2))) •
        (swappedTwoBlocks m n hm hn).blockTensor (pairFamily π₂ π₁)
          ((swappedTwoBlocks m n hm hn).leviProjection F p)
          (targetEval abv hopen hm hn s π₁ π₂ f g) := by
  rw [targetEval, BlockShape.productInducedOf_covariant]
  change _ • (twoBlocks n m hn hm).blockTensor
      (pairFamily (twist (determinantPower abv n (-s / 2)) π₂)
        (twist (determinantPower abv m (-(-s / 2))) π₁)) _ _ = _
  rw [blockTensor_pairFamily_twist, LinearMap.smul_apply, smul_smul, targetEval]
  congr 1
  rw [leviHalfCharacter_toMonoidHom, leviHalfModulus_apply, leviModulus_swappedTwoBlocks]
  refine (sqrt_mul_cpow_mul_cpow
    (determinantAbs abv n ((swappedTwoBlocks m n hm hn).leviProjection F p 0))
    (determinantAbs abv m ((swappedTwoBlocks m n hm hn).leviProjection F p 1)) n m
    (-s / 2) (-(-s / 2))).trans ?_
  rw [show -s / 2 + (m : ℂ) / 2 = (m - s) / 2 by ring,
    show -(-s / 2) - (n : ℂ) / 2 = (s - n) / 2 by ring]
  rfl

/-- The covariance of `I(-s, π₂ ⊗ π₁)` for the left action of `swapRank m n F p`, where
`p` ranges over the standard parabolic of type `(n, m)` on `GL_(n+m)(F)`. -/
theorem target_covariant_swapRank (f : TargetSpace abv hopen hm hn s π₁ π₂)
    (p : (twoBlocks n m hn hm).parabolic F) (g : GeneralLinear (m + n) F) :
    targetEval abv hopen hm hn s π₁ π₂ f (swapRank m n F p * g) =
      ((((abv (Matrix.det ((twoBlocks n m hn hm).leviProjection F p 0).val) : ℝ) : ℂ) ^
            ((m - s) / 2)) *
          (((abv (Matrix.det ((twoBlocks n m hn hm).leviProjection F p 1).val) : ℝ) : ℂ) ^
            ((s - n) / 2))) •
        (swappedTwoBlocks m n hm hn).blockTensor (pairFamily π₂ π₁)
          ((twoBlocks n m hn hm).leviProjection F p)
          (targetEval abv hopen hm hn s π₁ π₂ f g) := by
  have h := target_covariant abv hopen hm hn s π₁ π₂ f (swappedParabolicEquiv hm hn F p) g
  rw [leviProjection_swappedParabolicEquiv] at h
  exact h

end Induction

end Langlands.Shahidi

/-! ## The p-adic specialization -/

namespace Langlands.PadicField.TopologicalData

open Langlands.Shahidi GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The residue cardinality `q`, as a positive real number. -/
theorem residueCardinality_real_pos : (0 : ℝ) < T.residueCardinality := by
  exact_mod_cast Nat.zero_lt_one.trans T.residueCardinality_gt_one

/-- The Library's residue-normalized absolute value `|·|_F` (with `|ϖ| = q⁻¹`) as a
Mathlib absolute value. -/
def shahidiAbsoluteValue : AbsoluteValue F.Carrier ℝ where
  toFun := T.normalizedAbs
  map_mul' := T.normalizedAbs_mul
  nonneg' := T.normalizedAbs_nonneg
  eq_zero' := T.normalizedAbs_eq_zero_iff
  add_le' x y :=
    (T.normalizedAbs_add_le_max x y).trans
      (max_le (le_add_of_nonneg_right (T.normalizedAbs_nonneg y))
        (le_add_of_nonneg_left (T.normalizedAbs_nonneg x)))

@[simp]
theorem shahidiAbsoluteValue_apply (x : F.Carrier) :
    T.shahidiAbsoluteValue x = T.normalizedAbs x := rfl

/-! ### Comparison of the general layer with the normalized absolute value -/

section Comparison

variable {T} {abv : AbsoluteValue F.Carrier ℝ} (habv : ∀ x, abv x = T.normalizedAbs x)
include habv

theorem absUnits_eq_normalizedAbsUnits : absUnits abv = T.normalizedAbsUnits := by
  ext u
  exact habv u

theorem determinantAbs_eq_determinantNorm (n : ℕ) :
    determinantAbs abv n = T.determinantNorm n := by
  rw [determinantAbs, absUnits_eq_normalizedAbsUnits habv]
  rfl

/-- The normalized absolute value satisfies the smoothness hypothesis of the general
layer. -/
theorem isOpenNormOne_of_eq_normalizedAbs :
    letI := T.topology
    IsOpenNormOne abv := by
  let := T.topology
  change IsOpen ((absUnits abv).ker : Set F.Carrierˣ)
  rw [absUnits_eq_normalizedAbsUnits habv]
  exact T.isOpen_ker_normalizedAbsUnits

/-- The general block modulus is the Library's p-adic block modulus. -/
theorem leviModulus_eq_leviModulus {r : ℕ} (B : BlockShape r) :
    Shahidi.leviModulus abv B = T.leviModulus B := by
  refine MonoidHom.ext fun g => ?_
  rw [Shahidi.leviModulus_apply, T.leviModulus_apply]
  simp only [determinantAbs_eq_determinantNorm habv]

theorem leviHalfModulus_eq_leviHalfModulus {r : ℕ} (B : BlockShape r) :
    Shahidi.leviHalfModulus abv B = T.leviHalfModulus B := by
  rw [Shahidi.leviHalfModulus, leviModulus_eq_leviModulus habv]
  rfl

/-- The general normalizing character is the Library's p-adic `δ_P^(1/2)`. -/
theorem leviHalfCharacter_eq_leviHalfCharacter {r : ℕ} (B : BlockShape r) :
    letI := T.topology
    letI := T.isTopologicalRing
    Shahidi.leviHalfCharacter B (isOpenNormOne_of_eq_normalizedAbs habv) =
      T.leviHalfCharacter B := by
  let := T.topology
  let := T.isTopologicalRing
  unfold Shahidi.leviHalfCharacter TopologicalData.leviHalfCharacter
  congr 1
  exact leviHalfModulus_eq_leviHalfModulus habv B

end Comparison

/-! ### Complex determinant powers through unramified characters -/

/-- `g ↦ |det g|^t` for every complex `t`: the Library's unramified determinant character
at the nonzero complex number `q^(-t) = exp(-t log q)`. -/
def determinantComplexPower (n : ℕ) (t : ℂ) : GeneralLinear n F.Carrier →* ℂˣ :=
  T.determinantUnramifiedCharacter n
    (LocalFactor.spectralParameter T.residueCardinality T.residueCardinality_real_pos t)

theorem determinantComplexPower_def (n : ℕ) (t : ℂ) :
    T.determinantComplexPower n t =
      T.determinantUnramifiedCharacter n
        (LocalFactor.spectralParameter T.residueCardinality T.residueCardinality_real_pos t) :=
  rfl

/-- The unramified parametrization agrees with the complex power of the positive
normalized determinant absolute value. -/
theorem determinantComplexPower_apply (n : ℕ) (t : ℂ) (g : GeneralLinear n F.Carrier) :
    (T.determinantComplexPower n t g : ℂ) = (((T.determinantNorm n g : ℝ≥0) : ℝ) : ℂ) ^ t := by
  have hq : (0 : ℝ) < T.residueCardinality := T.residueCardinality_real_pos
  have hpos : (0 : ℝ) < (T.residueCardinality : ℝ) ^
      (-T.ord (GeneralLinear.determinant g : F.Carrier)) := zpow_pos hq _
  rw [determinantComplexPower, T.determinantUnramifiedCharacter_apply, Units.val_zpow_eq_zpow_val,
    T.determinantNorm_eq_residue_pow,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
    ← Complex.ofReal_log hpos.le, Real.log_zpow]
  change Complex.exp (-t * (Real.log T.residueCardinality : ℂ)) ^ _ = _
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem determinantComplexPower_eq_complexPower (n : ℕ) (t : ℂ) :
    T.determinantComplexPower n t = complexPower (T.determinantNorm n) t := by
  ext g
  exact T.determinantComplexPower_apply n t g

/-- The general determinant power for the normalized absolute value is the unramified
parametrization. -/
theorem determinantPower_eq_determinantComplexPower {abv : AbsoluteValue F.Carrier ℝ}
    (habv : ∀ x, abv x = T.normalizedAbs x) (n : ℕ) (t : ℂ) :
    determinantPower abv n t = T.determinantComplexPower n t := by
  rw [T.determinantComplexPower_eq_complexPower, determinantPower,
    determinantAbs_eq_determinantNorm habv]

theorem determinantComplexPower_add (n : ℕ) (s t : ℂ) :
    T.determinantComplexPower n (s + t) =
      T.determinantComplexPower n s * T.determinantComplexPower n t := by
  simp only [determinantComplexPower_eq_complexPower, complexPower_add]

theorem determinantComplexPower_neg (n : ℕ) (t : ℂ) :
    T.determinantComplexPower n (-t) = (T.determinantComplexPower n t)⁻¹ := by
  simp only [determinantComplexPower_eq_complexPower, complexPower_neg]

@[simp]
theorem determinantComplexPower_zero (n : ℕ) : T.determinantComplexPower n 0 = 1 := by
  simp only [determinantComplexPower_eq_complexPower, complexPower_zero]

/-- Real exponents recover the Library's real-power determinant characters. -/
theorem determinantComplexPower_ofReal (n : ℕ) (s : ℝ) :
    T.determinantComplexPower n (s : ℂ) = realPowerCharacter (T.determinantNorm n) s := by
  rw [determinantComplexPower_eq_complexPower, complexPower_ofReal]

theorem isOpen_ker_determinantComplexPower (n : ℕ) (t : ℂ) :
    letI := T.topology
    IsOpen ((T.determinantComplexPower n t).ker : Set (GeneralLinear n F.Carrier)) :=
  T.isOpen_ker_determinantUnramifiedCharacter n _

/-! ### The p-adic induced representations -/

/-- The p-adic block modulus of the swapped pair of blocks. -/
theorem leviModulus_swappedTwoBlocks {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (g : (swappedTwoBlocks m n hm hn).Levi F.Carrier) :
    T.leviModulus (swappedTwoBlocks m n hm hn) g =
      T.determinantNorm n (g 0) ^ m / T.determinantNorm m (g 1) ^ n := by
  rw [T.leviModulus_apply]
  simp only [Fin.prod_univ_two, Finset.prod_filter]
  norm_num [swappedTwoBlocks]
  rfl

/-- The inducing pair `ρ₁ |det|^(t/2), ρ₂ |det|^(-t/2)` on `GL_a(F) × GL_b(F)`. -/
def shahidiTwistedPair {a b : ℕ} (t : ℂ) {W₁ W₂ : Type uV} [AddCommGroup W₁] [Module ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] (ρ₁ : Representation ℂ (GeneralLinear a F.Carrier) W₁)
    (ρ₂ : Representation ℂ (GeneralLinear b F.Carrier) W₂) (i : Fin 2) :
    Representation ℂ (GeneralLinear (![a, b] i) F.Carrier) (pairCarrier W₁ W₂ i) :=
  pairFamily (twist (T.determinantComplexPower a (t / 2)) ρ₁)
    (twist (T.determinantComplexPower b (-(t / 2))) ρ₂) i

/-- The general inducing pair for the normalized absolute value is the p-adic one. -/
theorem twistedPair_eq_shahidiTwistedPair {abv : AbsoluteValue F.Carrier ℝ}
    (habv : ∀ x, abv x = T.normalizedAbs x) {a b : ℕ} (t : ℂ) {W₁ W₂ : Type uV}
    [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    (ρ₁ : Representation ℂ (GeneralLinear a F.Carrier) W₁)
    (ρ₂ : Representation ℂ (GeneralLinear b F.Carrier) W₂) :
    twistedPair abv t ρ₁ ρ₂ = T.shahidiTwistedPair t ρ₁ ρ₂ := by
  funext i
  simp only [twistedPair, shahidiTwistedPair,
    T.determinantPower_eq_determinantComplexPower habv]

variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (s : ℂ)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (GeneralLinear m F.Carrier) V₁)
  (π₂ : Representation ℂ (GeneralLinear n F.Carrier) V₂)

/-- The carrier of the p-adic `I(s, π₁ ⊗ π₂)`. -/
abbrev ShahidiSourceSpace : Type (max uF uV) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (m + n)
  Induction.SmoothFunctions ((twoBlocks m n hm hn).parabolic F.Carrier)
    (twist (T.parabolicHalfModulus (twoBlocks m n hm hn))
      (((twoBlocks m n hm hn).blockTensor (T.shahidiTwistedPair s π₁ π₂)).comp
        ((twoBlocks m n hm hn).leviProjection F.Carrier)))

/-- Shahidi's `I(s, π₁ ⊗ π₂)` over the p-adic field `F`: the Library's
`normalizedProductInduced` of `π₁ |det|^(s/2) ⊗ π₂ |det|^(-s/2)` from the standard
parabolic with Levi `GL_m × GL_n`. -/
def shahidiSource :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (m + n)
    Representation ℂ (GeneralLinear (m + n) F.Carrier) (T.ShahidiSourceSpace hm hn s π₁ π₂) :=
  T.normalizedProductInduced (twoBlocks m n hm hn) (T.shahidiTwistedPair s π₁ π₂)

/-- The value `f(g) ∈ V₁ ⊗ V₂`. -/
def shahidiSourceEval (f : T.ShahidiSourceSpace hm hn s π₁ π₂)
    (g : GeneralLinear (m + n) F.Carrier) : PiTensorProduct ℂ (pairCarrier V₁ V₂) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (m + n)
  Induction.eval _ _ f g

/-- The underlying functions, as a linear map. -/
def shahidiSourceFunction :
    T.ShahidiSourceSpace hm hn s π₁ π₂ →ₗ[ℂ]
      (GeneralLinear (m + n) F.Carrier → PiTensorProduct ℂ (pairCarrier V₁ V₂)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (m + n)
  (Submodule.subtype _).comp (Submodule.subtype _)

@[simp]
theorem shahidiSourceFunction_apply (f : T.ShahidiSourceSpace hm hn s π₁ π₂)
    (g : GeneralLinear (m + n) F.Carrier) :
    T.shahidiSourceFunction hm hn s π₁ π₂ f g = T.shahidiSourceEval hm hn s π₁ π₂ f g := rfl

theorem shahidiSource_eq :
    T.shahidiSource hm hn s π₁ π₂ =
      T.normalizedParabolicInduced (twoBlocks m n hm hn)
        ((twoBlocks m n hm hn).blockTensor (T.shahidiTwistedPair s π₁ π₂)) := rfl

/-- The group acts by right translation. -/
@[simp]
theorem shahidiSource_apply (g : GeneralLinear (m + n) F.Carrier)
    (f : T.ShahidiSourceSpace hm hn s π₁ π₂) (x : GeneralLinear (m + n) F.Carrier) :
    T.shahidiSourceEval hm hn s π₁ π₂ (T.shahidiSource hm hn s π₁ π₂ g f) x =
      T.shahidiSourceEval hm hn s π₁ π₂ f (x * g) := rfl

theorem isSmooth_shahidiSource :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (m + n)
    IsSmooth (T.shahidiSource hm hn s π₁ π₂) :=
  T.isSmooth_normalizedProductInduced _ _

/-- Covariance of the p-adic `I(s, π₁ ⊗ π₂)`: for `g` in the standard parabolic with
diagonal blocks `g₁ ∈ GL_m`, `g₂ ∈ GL_n`,
`f(g x) = |det g₁|^((s+n)/2) |det g₂|^(-(s+m)/2) (π₁(g₁) ⊗ π₂(g₂)) f(x)`. -/
theorem shahidiSource_covariant (f : T.ShahidiSourceSpace hm hn s π₁ π₂)
    (g : (twoBlocks m n hm hn).parabolic F.Carrier) (x : GeneralLinear (m + n) F.Carrier) :
    T.shahidiSourceEval hm hn s π₁ π₂ f ((g : GeneralLinear (m + n) F.Carrier) * x) =
      ((((T.normalizedAbs
              (Matrix.det ((twoBlocks m n hm hn).leviProjection F.Carrier g 0).val) : ℝ) : ℂ) ^
            ((s + n) / 2)) *
          (((T.normalizedAbs
              (Matrix.det ((twoBlocks m n hm hn).leviProjection F.Carrier g 1).val) : ℝ) : ℂ) ^
            (-((s + m) / 2)))) •
        (twoBlocks m n hm hn).blockTensor (pairFamily π₁ π₂)
          ((twoBlocks m n hm hn).leviProjection F.Carrier g)
          (T.shahidiSourceEval hm hn s π₁ π₂ f x) := by
  rw [shahidiSourceEval, T.normalizedProductInduced_covariant]
  change _ • (twoBlocks m n hm hn).blockTensor
      (pairFamily (twist (T.determinantComplexPower m (s / 2)) π₁)
        (twist (T.determinantComplexPower n (-(s / 2))) π₂)) _ _ = _
  rw [blockTensor_pairFamily_twist, LinearMap.smul_apply, smul_smul, shahidiSourceEval]
  congr 1
  rw [T.leviModulus_twoBlocks]
  erw [T.determinantComplexPower_apply, T.determinantComplexPower_apply]
  refine (sqrt_mul_cpow_mul_cpow
    (T.determinantNorm m ((twoBlocks m n hm hn).leviProjection F.Carrier g 0))
    (T.determinantNorm n ((twoBlocks m n hm hn).leviProjection F.Carrier g 1)) m n
    (s / 2) (-(s / 2))).trans ?_
  rw [show s / 2 + (n : ℂ) / 2 = (s + n) / 2 by ring,
    show -(s / 2) - (m : ℂ) / 2 = -((s + m) / 2) by ring]
  rfl

/-- The carrier of the p-adic `I(-s, π₂ ⊗ π₁)` on `GL_(m+n)(F)`. -/
abbrev ShahidiTargetSpace : Type (max uF uV) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (m + n)
  Induction.SmoothFunctions ((swappedTwoBlocks m n hm hn).parabolic F.Carrier)
    (twist (T.parabolicHalfModulus (swappedTwoBlocks m n hm hn))
      (((swappedTwoBlocks m n hm hn).blockTensor (T.shahidiTwistedPair (-s) π₂ π₁)).comp
        ((swappedTwoBlocks m n hm hn).leviProjection F.Carrier)))

/-- Shahidi's `I(-s, π₂ ⊗ π₁)` over the p-adic field `F`, on the same group
`GL_(m+n)(F)`: the Library's `normalizedProductInduced` of
`π₂ |det|^(-s/2) ⊗ π₁ |det|^(s/2)` from the standard parabolic with Levi `GL_n × GL_m`. -/
def shahidiTarget :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (m + n)
    Representation ℂ (GeneralLinear (m + n) F.Carrier) (T.ShahidiTargetSpace hm hn s π₁ π₂) :=
  T.normalizedProductInduced (swappedTwoBlocks m n hm hn) (T.shahidiTwistedPair (-s) π₂ π₁)

/-- The value `f(g) ∈ V₂ ⊗ V₁`. -/
def shahidiTargetEval (f : T.ShahidiTargetSpace hm hn s π₁ π₂)
    (g : GeneralLinear (m + n) F.Carrier) : PiTensorProduct ℂ (pairCarrier V₂ V₁) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (m + n)
  Induction.eval _ _ f g

/-- The underlying functions, as a linear map. -/
def shahidiTargetFunction :
    T.ShahidiTargetSpace hm hn s π₁ π₂ →ₗ[ℂ]
      (GeneralLinear (m + n) F.Carrier → PiTensorProduct ℂ (pairCarrier V₂ V₁)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (m + n)
  (Submodule.subtype _).comp (Submodule.subtype _)

@[simp]
theorem shahidiTargetFunction_apply (f : T.ShahidiTargetSpace hm hn s π₁ π₂)
    (g : GeneralLinear (m + n) F.Carrier) :
    T.shahidiTargetFunction hm hn s π₁ π₂ f g = T.shahidiTargetEval hm hn s π₁ π₂ f g := rfl

theorem shahidiTarget_eq :
    T.shahidiTarget hm hn s π₁ π₂ =
      T.normalizedParabolicInduced (swappedTwoBlocks m n hm hn)
        ((swappedTwoBlocks m n hm hn).blockTensor (T.shahidiTwistedPair (-s) π₂ π₁)) := rfl

@[simp]
theorem shahidiTarget_apply (g : GeneralLinear (m + n) F.Carrier)
    (f : T.ShahidiTargetSpace hm hn s π₁ π₂) (x : GeneralLinear (m + n) F.Carrier) :
    T.shahidiTargetEval hm hn s π₁ π₂ (T.shahidiTarget hm hn s π₁ π₂ g f) x =
      T.shahidiTargetEval hm hn s π₁ π₂ f (x * g) := rfl

theorem isSmooth_shahidiTarget :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (m + n)
    IsSmooth (T.shahidiTarget hm hn s π₁ π₂) :=
  T.isSmooth_normalizedProductInduced _ _

/-- Covariance of the p-adic `I(-s, π₂ ⊗ π₁)`: for `g` in the parabolic of type `(n, m)`
with diagonal blocks `g₁ ∈ GL_n`, `g₂ ∈ GL_m`,
`f(g x) = |det g₁|^((m-s)/2) |det g₂|^((s-n)/2) (π₂(g₁) ⊗ π₁(g₂)) f(x)`. -/
theorem shahidiTarget_covariant (f : T.ShahidiTargetSpace hm hn s π₁ π₂)
    (g : (swappedTwoBlocks m n hm hn).parabolic F.Carrier)
    (x : GeneralLinear (m + n) F.Carrier) :
    T.shahidiTargetEval hm hn s π₁ π₂ f ((g : GeneralLinear (m + n) F.Carrier) * x) =
      ((((T.normalizedAbs
              (Matrix.det ((swappedTwoBlocks m n hm hn).leviProjection F.Carrier g 0).val) :
              ℝ) : ℂ) ^ ((m - s) / 2)) *
          (((T.normalizedAbs
              (Matrix.det ((swappedTwoBlocks m n hm hn).leviProjection F.Carrier g 1).val) :
              ℝ) : ℂ) ^ ((s - n) / 2))) •
        (swappedTwoBlocks m n hm hn).blockTensor (pairFamily π₂ π₁)
          ((swappedTwoBlocks m n hm hn).leviProjection F.Carrier g)
          (T.shahidiTargetEval hm hn s π₁ π₂ f x) := by
  rw [shahidiTargetEval, T.normalizedProductInduced_covariant]
  change _ • (twoBlocks n m hn hm).blockTensor
      (pairFamily (twist (T.determinantComplexPower n (-s / 2)) π₂)
        (twist (T.determinantComplexPower m (-(-s / 2))) π₁)) _ _ = _
  rw [blockTensor_pairFamily_twist, LinearMap.smul_apply, smul_smul, shahidiTargetEval]
  congr 1
  rw [T.leviModulus_swappedTwoBlocks]
  erw [T.determinantComplexPower_apply, T.determinantComplexPower_apply]
  refine (sqrt_mul_cpow_mul_cpow
    (T.determinantNorm n ((swappedTwoBlocks m n hm hn).leviProjection F.Carrier g 0))
    (T.determinantNorm m ((swappedTwoBlocks m n hm hn).leviProjection F.Carrier g 1)) n m
    (-s / 2) (-(-s / 2))).trans ?_
  rw [show -s / 2 + (m : ℂ) / 2 = (m - s) / 2 by ring,
    show -(-s / 2) - (n : ℂ) / 2 = (s - n) / 2 by ring]
  rfl

/-- The covariance of the p-adic `I(-s, π₂ ⊗ π₁)` for the left action of
`swapRank m n F p`, `p` in the standard parabolic of type `(n, m)` on `GL_(n+m)(F)`. -/
theorem shahidiTarget_covariant_swapRank (f : T.ShahidiTargetSpace hm hn s π₁ π₂)
    (g : (twoBlocks n m hn hm).parabolic F.Carrier) (x : GeneralLinear (m + n) F.Carrier) :
    T.shahidiTargetEval hm hn s π₁ π₂ f (swapRank m n F.Carrier g * x) =
      ((((T.normalizedAbs
              (Matrix.det ((twoBlocks n m hn hm).leviProjection F.Carrier g 0).val) : ℝ) : ℂ) ^
            ((m - s) / 2)) *
          (((T.normalizedAbs
              (Matrix.det ((twoBlocks n m hn hm).leviProjection F.Carrier g 1).val) : ℝ) : ℂ) ^
            ((s - n) / 2))) •
        (swappedTwoBlocks m n hm hn).blockTensor (pairFamily π₂ π₁)
          ((twoBlocks n m hn hm).leviProjection F.Carrier g)
          (T.shahidiTargetEval hm hn s π₁ π₂ f x) := by
  have h := T.shahidiTarget_covariant hm hn s π₁ π₂ f
    (swappedParabolicEquiv hm hn F.Carrier g) x
  rw [leviProjection_swappedParabolicEquiv] at h
  exact h

end Langlands.PadicField.TopologicalData

/-! ## Canonical aliases -/

namespace Langlands.PadicField

open Langlands.Shahidi GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (s : ℂ)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (GeneralLinear m F.Carrier) V₁)
  (π₂ : Representation ℂ (GeneralLinear n F.Carrier) V₂)

/-- The canonical-realization carrier of `I(s, π₁ ⊗ π₂)`. -/
abbrev canonicalShahidiSourceSpace : Type (max uF uV) :=
  F.canonicalTopologicalData.ShahidiSourceSpace hm hn s π₁ π₂

/-- `I(s, π₁ ⊗ π₂)` for the canonical realization of `F`. -/
abbrev canonicalShahidiSource :=
  F.canonicalTopologicalData.shahidiSource hm hn s π₁ π₂

/-- The canonical-realization carrier of `I(-s, π₂ ⊗ π₁)`. -/
abbrev canonicalShahidiTargetSpace : Type (max uF uV) :=
  F.canonicalTopologicalData.ShahidiTargetSpace hm hn s π₁ π₂

/-- `I(-s, π₂ ⊗ π₁)` for the canonical realization of `F`. -/
abbrev canonicalShahidiTarget :=
  F.canonicalTopologicalData.shahidiTarget hm hn s π₁ π₂

end Langlands.PadicField
