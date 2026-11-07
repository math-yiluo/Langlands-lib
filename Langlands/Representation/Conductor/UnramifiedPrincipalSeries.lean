import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.Representation.Whittaker.Spherical
import Langlands.Group.GL.SingletonBlocks
import Langlands.Group.GL.TriangularParabolic
import Mathlib.Algebra.Group.Hom.Instances

/-!
# Normalized unramified principal series over nonarchimedean local fields
-/

noncomputable section

namespace Langlands.Conductor.UnramifiedPrincipalSeries

open Langlands.GeneralLinear Langlands.Induction
open scoped BigOperators

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F]

variable {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)

/-- The integer order determined by the supplied uniformizing element. -/
def ord (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ) (a : Fˣ) : ℤ :=
  (hϖ.2 (a : F) a.ne_zero).choose

theorem valuation_eq_pow_ord (a : Fˣ) : (ValuativeRel.valuation F) (a : F) = (ValuativeRel.valuation F) (ϖ : F) ^ ord hϖ a :=
  (hϖ.2 (a : F) a.ne_zero).choose_spec

theorem ord_eq_of_valuation {a : Fˣ} {m : ℤ}
    (h : (ValuativeRel.valuation F) (a : F) = (ValuativeRel.valuation F) (ϖ : F) ^ m) : ord hϖ a = m :=
  (zpow_right_strictAnti₀ (Iwasawa.valuation_pos (ValuativeRel.valuation F) ϖ) hϖ.1).injective
    ((valuation_eq_pow_ord hϖ a).symm.trans h)

@[simp] theorem ord_one : ord hϖ 1 = 0 :=
  ord_eq_of_valuation hϖ (by simp)

@[simp] theorem ord_mul (a b : Fˣ) : ord hϖ (a * b) = ord hϖ a + ord hϖ b :=
  ord_eq_of_valuation hϖ (by
    rw [Units.val_mul, map_mul, valuation_eq_pow_ord hϖ a, valuation_eq_pow_ord hϖ b,
      zpow_add₀ (Iwasawa.valuation_pos (ValuativeRel.valuation F) ϖ).ne'])

@[simp] theorem ord_uniformizer : ord hϖ ϖ = 1 :=
  ord_eq_of_valuation hϖ (by simp)

theorem ord_eq_zero_iff (a : Fˣ) : ord hϖ a = 0 ↔ (ValuativeRel.valuation F) (a : F) = 1 := by
  constructor
  · intro h
    exact valuation_eq_pow_ord hϖ a |>.trans (by simp [h])
  · intro h
    exact ord_eq_of_valuation hϖ (by simpa using h)

/-- The order as a homomorphism to the multiplicative copy of the integers. -/
def ordHom : Fˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (ord hϖ a)
  map_one' := congrArg Multiplicative.ofAdd (ord_one hϖ)
  map_mul' a b := congrArg Multiplicative.ofAdd (ord_mul hϖ a b)

@[simp] theorem ord_zpow (a : Fˣ) (m : ℤ) : ord hϖ (a ^ m) = m * ord hϖ a := by
  exact congrArg Multiplicative.toAdd ((ordHom hϖ).map_zpow a m)

/-- The unramified character with arbitrary complex unit value at the uniformizer. -/
def character (z : ℂˣ) : Fˣ →* ℂˣ :=
  (zpowersHom ℂˣ z).comp (ordHom hϖ)

@[simp] theorem character_apply (z : ℂˣ) (a : Fˣ) :
    character hϖ z a = z ^ ord hϖ a := rfl

@[simp] theorem character_uniformizer (z : ℂˣ) : character hϖ z ϖ = z := by
  simp

theorem character_unit (z : ℂˣ) {a : Fˣ} (ha : (ValuativeRel.valuation F) (a : F) = 1) :
    character hϖ z a = 1 := by
  simp [(ord_eq_zero_iff hϖ a).mpr ha]

theorem character_uniformizer_pow_mul (z : ℂˣ) (m : ℤ) {a : Fˣ}
    (ha : (ValuativeRel.valuation F) (a : F) = 1) : character hϖ z (ϖ ^ m * a) = z ^ m := by
  simp [(ord_eq_zero_iff hϖ a).mpr ha]

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isOpen_ker_ordHom : IsOpen ((ordHom hϖ).ker : Set Fˣ) := by
  have hs : IsOpen {x : F | (ValuativeRel.valuation F) x = 1} :=
    by simpa only [Valuation.restrict_eq_one_iff] using
      (Valuation.isOpen_sphere (v := ValuativeRel.valuation F) one_ne_zero)
  convert hs.preimage Units.continuous_val using 1
  ext a
  exact ord_eq_zero_iff hϖ a

theorem isOpen_ker_character (z : ℂˣ) :
    IsOpen ((character hϖ z).ker : Set Fˣ) := by
  apply Subgroup.isOpen_mono (H₁ := (ordHom hϖ).ker) ?_ (isOpen_ker_ordHom hϖ)
  intro a ha
  change (zpowersHom ℂˣ z) (ordHom hϖ a) = 1
  rw [show ordHom hϖ a = 1 from ha, map_one]

/-- The same actual character bundled with its open kernel. -/
def smoothCharacter (z : ℂˣ) : SmoothCharacter ℂ Fˣ :=
  ⟨character hϖ z, isOpen_ker_character hϖ z⟩

variable (n : ℕ)

/-- The Borel is the actual upper triangular subgroup of the matrix group. -/
abbrev Borel := upperTriangularSubgroup (n + 1) F

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem borel_eq_singleton_parabolic :
    upperTriangularSubgroup (n + 1) F = (BlockShape.singletons (n + 1)).parabolic F := by
  ext g
  exact (BlockShape.singletons_mem_parabolic_iff F g).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem diagonal_ne_zero (b : Borel (F := F) n) (i : Fin (n + 1)) :
    b.val i i ≠ 0 := by
  have hprod : (∏ j, b.val j j) ≠ 0 := by
    rw [← Matrix.det_of_isUpperTriangular b.property]
    exact Matrix.GeneralLinearGroup.det_ne_zero b.val
  exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)

/-- The actual diagonal-entry homomorphism on the upper Borel. -/
def diagonalUnit (i : Fin (n + 1)) : Borel (F := F) n →* Fˣ where
  toFun b := Units.mk0 (b.val i i) (diagonal_ne_zero n b i)
  map_one' := by
    apply Units.ext
    exact Matrix.one_apply_eq i
  map_mul' b c := by
    apply Units.ext
    exact Iwasawa.upperTriangular_mul_apply_self b.property c.property i

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem diagonalUnit_val (b : Borel (F := F) n) (i : Fin (n + 1)) :
    (diagonalUnit n i b : F) = b.val i i := rfl

/-- The unnormalized product of the scalar inducing characters on the actual Borel. -/
def inducingCharacter (z : Fin (n + 1) → ℂˣ) : Borel (F := F) n →* ℂˣ :=
  ∏ i, (character hϖ (z i)).comp (diagonalUnit n i)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem inducingCharacter_apply (z : Fin (n + 1) → ℂˣ) (b : Borel (F := F) n) :
    inducingCharacter hϖ n z b = ∏ i, z i ^ ord hϖ (diagonalUnit n i b) := by
  simp [inducingCharacter]

/-- The supplied residue cardinality is checked against the actual residue field. -/
def IsResidueCardinality (q : ℕ) : Prop :=
  q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer)

theorem residueCardinality_pos {q : ℕ} (hq : IsResidueCardinality (F := F) q) : 0 < q := by
  rw [hq]
  exact Nat.card_pos

/-- The positive square root of the actual residue cardinality, as a complex unit. -/
def sqrtResidueUnit {q : ℕ} (hq : IsResidueCardinality (F := F) q) : ℂˣ :=
  Units.mk0 ((Real.sqrt (q : ℝ) : ℝ) : ℂ) (by
    apply Complex.ofReal_ne_zero.mpr
    exact (Real.sqrt_pos.mpr (by exact_mod_cast residueCardinality_pos hq)).ne')

@[simp] theorem sqrtResidueUnit_val {q : ℕ} (hq : IsResidueCardinality (F := F) q) :
    (sqrtResidueUnit hq : ℂ) = ((Real.sqrt (q : ℝ) : ℝ) : ℂ) := rfl

/-- The exponent of `sqrt(q)` in the positive half modulus of the upper Borel. -/
def modulusExponent : Borel (F := F) n →* Multiplicative ℤ where
  toFun b := Multiplicative.ofAdd
    (-∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * ord hϖ (diagonalUnit n i b))
  map_one' := by
    change (-∑ i : Fin (n + 1),
      ((n : ℤ) - 2 * (i : ℤ)) * ord hϖ (diagonalUnit n i 1)) = 0
    simp
  map_mul' b c := by
    change (-∑ i : Fin (n + 1),
      ((n : ℤ) - 2 * (i : ℤ)) * ord hϖ (diagonalUnit n i (b * c))) =
      (-∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * ord hϖ (diagonalUnit n i b)) +
      (-∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * ord hϖ (diagonalUnit n i c))
    simp only [map_mul, ord_mul, mul_add, Finset.sum_add_distrib]
    omega

/-- The standard positive square-root modulus character, in valuation exponents. -/
def halfModulusCharacter {q : ℕ} (hq : IsResidueCardinality (F := F) q) :
    Borel (F := F) n →* ℂˣ :=
  (zpowersHom ℂˣ (sqrtResidueUnit hq)).comp (modulusExponent hϖ n)

theorem halfModulusCharacter_apply {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (b : Borel (F := F) n) :
    (halfModulusCharacter hϖ n hq b : ℂ) =
      ((Real.sqrt (q : ℝ) : ℝ) : ℂ) ^
        (-∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * ord hϖ (diagonalUnit n i b)) := by
  simp [halfModulusCharacter, modulusExponent, zpowersHom]

/-- Product of the positive half modulus and the unramified inducing characters. -/
def normalizedCharacter {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 1) → ℂˣ) : Borel (F := F) n →* ℂˣ :=
  halfModulusCharacter hϖ n hq * inducingCharacter hϖ n z

theorem normalizedCharacter_apply {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 1) → ℂˣ) (b : Borel (F := F) n) :
    (normalizedCharacter hϖ n hq z b : ℂ) =
      (halfModulusCharacter hϖ n hq b : ℂ) *
        ∏ i, (character hϖ (z i) (diagonalUnit n i b) : ℂ) := by
  simp [normalizedCharacter, inducingCharacter]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem ord_diagonalUnit_eq_zero_of_integral (b : Borel (F := F) n)
    (hb : b.val ∈ integralSubgroup (ValuativeRel.valuation F).integer n)
    (i : Fin (n + 1)) : ord hϖ (diagonalUnit n i b) = 0 := by
  apply (ord_eq_zero_iff hϖ _).mpr
  exact Iwasawa.valuation_diag_eq_one (ValuativeRel.valuation F) hb b.property i

theorem normalizedCharacter_eq_one_of_integral {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)
    (b : Borel (F := F) n)
    (hb : b.val ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
    normalizedCharacter hϖ n hq z b = 1 := by
  have hzero := ord_diagonalUnit_eq_zero_of_integral hϖ n b hb
  simp [normalizedCharacter, halfModulusCharacter, modulusExponent,
    inducingCharacter_apply, hzero, zpowersHom]

/-- The actual integral general linear group as an open subgroup for the given topology. -/
def integralOpenSubgroup : OpenSubgroup (Langlands.GeneralLinear (n + 1) F) :=
  ⟨integralSubgroup (ValuativeRel.valuation F).integer n,
    isOpen_integralSubgroup _ _ (Valuation.isOpen_integer (v := ValuativeRel.valuation F))⟩

theorem isOpen_ker_normalizedCharacter {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ) :
    IsOpen ((normalizedCharacter hϖ n hq z).ker : Set (Borel (F := F) n)) := by
  apply Subgroup.isOpen_mono
    (H₁ := (integralSubgroup (ValuativeRel.valuation F).integer n).comap
      (upperTriangularSubgroup (n + 1) F).subtype)
  · intro b hb
    exact normalizedCharacter_eq_one_of_integral hϖ n hq z b hb
  · exact (integralOpenSubgroup (F := F) n).isOpen.preimage continuous_subtype_val

/-- The normalized Borel character bundled with its proved smoothness. -/
def normalizedSmoothCharacter {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 1) → ℂˣ) : SmoothCharacter ℂ (Borel (F := F) n) :=
  ⟨normalizedCharacter hϖ n hq z, isOpen_ker_normalizedCharacter hϖ n hq z⟩

/-- Actual uniformly right-smooth functions with normalized upper-Borel covariance. -/
abbrev PrincipalSeries {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 1) → ℂˣ) :=
  SmoothFunctions (upperTriangularSubgroup (n + 1) F)
    (Langlands.characterRepresentation (normalizedCharacter hϖ n hq z))

/-- Right translation on the actual normalized induced function space. -/
def principalSeries {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 1) → ℂˣ) :
    Representation ℂ (Langlands.GeneralLinear (n + 1) F) (PrincipalSeries hϖ n hq z) :=
  smoothInduced _ (Langlands.characterRepresentation (normalizedCharacter hϖ n hq z))

/-- Evaluation of a principal-series function at an actual matrix. -/
def value {q : ℕ} {hq : IsResidueCardinality (F := F) q} {z : Fin (n + 1) → ℂˣ}
    (f : PrincipalSeries hϖ n hq z) (g : Langlands.GeneralLinear (n + 1) F) : ℂ :=
  f.val.val g

theorem covariance {q : ℕ} {hq : IsResidueCardinality (F := F) q}
    {z : Fin (n + 1) → ℂˣ} (f : PrincipalSeries hϖ n hq z)
    (b : Borel (F := F) n) (g : Langlands.GeneralLinear (n + 1) F) :
    value hϖ n f (b.val * g) =
      (halfModulusCharacter hϖ n hq b : ℂ) *
        (∏ i, (character hϖ (z i) (diagonalUnit n i b) : ℂ)) * value hϖ n f g := by
  rw [← normalizedCharacter_apply]
  exact f.val.property b g

@[simp] theorem rightTranslation {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 1) → ℂˣ) (g x : Langlands.GeneralLinear (n + 1) F)
    (f : PrincipalSeries hϖ n hq z) :
    value hϖ n (principalSeries hϖ n hq z g f) x = value hϖ n f (x * g) := rfl

theorem principalSeries_smooth {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 1) → ℂˣ) :
    IsSmooth (principalSeries hϖ n hq z) :=
  smoothInduced_smooth _ _

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The existing Iwasawa theorem with factors bundled in the actual subgroups. -/
theorem exists_borel_integral (g : Langlands.GeneralLinear (n + 1) F) :
    ∃ b : Borel (F := F) n,
      ∃ k : integralSubgroup (ValuativeRel.valuation F).integer n, g = b.val * k.val := by
  obtain ⟨b, hb, k, hk, h⟩ := Iwasawa.exists_upperTriangular_mul (ValuativeRel.valuation F) g
  exact ⟨⟨b, hb⟩, ⟨k, hk⟩, h⟩

/-- The upper-triangular factor of one chosen, proved Iwasawa decomposition. -/
def borelFactor (g : Langlands.GeneralLinear (n + 1) F) : Borel (F := F) n :=
  (exists_borel_integral n g).choose

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem exists_integral_borelFactor (g : Langlands.GeneralLinear (n + 1) F) :
    ∃ k : integralSubgroup (ValuativeRel.valuation F).integer n,
      g = (borelFactor n g).val * k.val :=
  (exists_borel_integral n g).choose_spec

theorem normalizedCharacter_factors_eq {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)
    (b c : Borel (F := F) n)
    (k l : integralSubgroup (ValuativeRel.valuation F).integer n)
    (h : b.val * k.val = c.val * l.val) :
    normalizedCharacter hϖ n hq z b = normalizedCharacter hϖ n hq z c := by
  have hmat : (c⁻¹ * b).val = l.val * k.val⁻¹ := by
    change c.val⁻¹ * b.val = l.val * k.val⁻¹
    calc
      c.val⁻¹ * b.val = c.val⁻¹ * (b.val * k.val) * k.val⁻¹ := by group
      _ = c.val⁻¹ * (c.val * l.val) * k.val⁻¹ := by rw [h]
      _ = l.val * k.val⁻¹ := by group
  have hmem : (c⁻¹ * b).val ∈ integralSubgroup (ValuativeRel.valuation F).integer n := by
    rw [hmat]
    exact mul_mem l.property (inv_mem k.property)
  have hc := normalizedCharacter_eq_one_of_integral hϖ n hq z (c⁻¹ * b) hmem
  rw [map_mul, map_inv] at hc
  exact (inv_mul_eq_one.mp hc).symm

/-- The scalar spherical function, defined using an actual Iwasawa factor. -/
def sphericalValue {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 1) → ℂˣ) (g : Langlands.GeneralLinear (n + 1) F) : ℂ :=
  (normalizedCharacter hϖ n hq z (borelFactor n g) : ℂ)

theorem sphericalValue_borel_mul_integral {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)
    (b : Borel (F := F) n)
    {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
    sphericalValue hϖ n hq z (b.val * k) = (normalizedCharacter hϖ n hq z b : ℂ) := by
  obtain ⟨l, hl⟩ := exists_integral_borelFactor n (b.val * k)
  exact congrArg Units.val (normalizedCharacter_factors_eq hϖ n hq z
    (borelFactor n (b.val * k)) b l ⟨k, hk⟩ hl.symm)

theorem sphericalValue_covariance {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)
    (b : Borel (F := F) n) (g : Langlands.GeneralLinear (n + 1) F) :
    sphericalValue hϖ n hq z (b.val * g) =
      (normalizedCharacter hϖ n hq z b : ℂ) * sphericalValue hϖ n hq z g := by
  obtain ⟨k, hk⟩ := exists_integral_borelFactor n g
  rw [hk, ← mul_assoc]
  change sphericalValue hϖ n hq z ((b * borelFactor n g).val * k.val) = _
  rw [sphericalValue_borel_mul_integral hϖ n hq z _ k.property,
    sphericalValue_borel_mul_integral hϖ n hq z _ k.property, map_mul, Units.val_mul]

theorem sphericalValue_mul_integral {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)
    (g : Langlands.GeneralLinear (n + 1) F) {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
    sphericalValue hϖ n hq z (g * k) = sphericalValue hϖ n hq z g := by
  obtain ⟨l, hl⟩ := exists_integral_borelFactor n g
  rw [hl, mul_assoc,
    sphericalValue_borel_mul_integral hϖ n hq z _ (mul_mem l.property hk),
    sphericalValue_borel_mul_integral hϖ n hq z _ l.property]

/-- The normalized spherical section in the actual smooth induced carrier. -/
def sphericalSection {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 1) → ℂˣ) : PrincipalSeries hϖ n hq z :=
  smoothFunctionOf _ _ (sphericalValue hϖ n hq z)
    (sphericalValue_covariance hϖ n hq z) (integralOpenSubgroup n)
    (fun k g => sphericalValue_mul_integral hϖ n hq z g k.property)

@[simp] theorem sphericalSection_value {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    value hϖ n (sphericalSection hϖ n hq z) g = sphericalValue hϖ n hq z g := rfl

theorem sphericalSection_borel_mul_integral {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)
    (b : Borel (F := F) n) {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
    value hϖ n (sphericalSection hϖ n hq z) (b.val * k) =
      (normalizedCharacter hϖ n hq z b : ℂ) :=
  sphericalValue_borel_mul_integral hϖ n hq z b hk

theorem sphericalSection_covariance {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)
    (b : Borel (F := F) n) (g : Langlands.GeneralLinear (n + 1) F) :
    value hϖ n (sphericalSection hϖ n hq z) (b.val * g) =
      (halfModulusCharacter hϖ n hq b : ℂ) *
        (∏ i, (character hϖ (z i) (diagonalUnit n i b) : ℂ)) *
          value hϖ n (sphericalSection hϖ n hq z) g :=
  covariance hϖ n (sphericalSection hϖ n hq z) b g

@[simp] theorem sphericalSection_one {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ) :
    value hϖ n (sphericalSection hϖ n hq z) 1 = 1 := by
  have h := sphericalValue_borel_mul_integral hϖ n hq z 1
    (one_mem (integralSubgroup (ValuativeRel.valuation F).integer n))
  simpa using h

theorem sphericalSection_integral {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)
    {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
    value hϖ n (sphericalSection hϖ n hq z) k = 1 := by
  simpa using sphericalSection_borel_mul_integral hϖ n hq z 1 hk

theorem sphericalSection_mul_integral {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)
    (g : Langlands.GeneralLinear (n + 1) F) {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
    value hϖ n (sphericalSection hϖ n hq z) (g * k) =
      value hϖ n (sphericalSection hϖ n hq z) g :=
  sphericalValue_mul_integral hϖ n hq z g hk

theorem sphericalSection_fixed {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)
    {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
    principalSeries hϖ n hq z k (sphericalSection hϖ n hq z) =
      sphericalSection hϖ n hq z := by
  apply Subtype.ext
  apply Subtype.ext
  exact funext (fun g => sphericalSection_mul_integral hϖ n hq z g hk)

theorem sphericalSection_ne_zero {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ) :
    sphericalSection hϖ n hq z ≠ 0 := by
  intro h
  have hval := sphericalSection_one hϖ n hq z
  rw [h] at hval
  exact zero_ne_one hval

/-- Diagonal uniformizer powers regarded as an element of the actual Borel. -/
def torusBorel (ϖ : Fˣ) (lam : Fin (n + 1) → ℤ) : Borel (F := F) n :=
  ⟨Iwasawa.torus ϖ lam, by
    change (Matrix.diagonal fun i => ((ϖ ^ lam i : Fˣ) : F)).IsUpperTriangular
    intro i j hij
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem torusBorel_val (ϖ : Fˣ) (lam : Fin (n + 1) → ℤ) :
    (torusBorel n ϖ lam).val = Iwasawa.torus ϖ lam := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp] theorem diagonalUnit_torusBorel (ϖ : Fˣ) (lam : Fin (n + 1) → ℤ)
    (i : Fin (n + 1)) : diagonalUnit n i (torusBorel n ϖ lam) = ϖ ^ lam i := by
  apply Units.ext
  exact Matrix.diagonal_apply_eq _ i

theorem halfModulusCharacter_torus {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (lam : Fin (n + 1) → ℤ) :
    (halfModulusCharacter hϖ n hq (torusBorel n ϖ lam) : ℂ) =
      Spherical.halfModulus q lam := by
  rw [halfModulusCharacter_apply]
  simp [Spherical.halfModulus]

theorem sphericalSection_torus {q : ℕ}
    (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)
    (lam : Fin (n + 1) → ℤ) :
    value hϖ n (sphericalSection hϖ n hq z) (Iwasawa.torus ϖ lam) =
      Spherical.halfModulus q lam * ∏ i, (z i : ℂ) ^ lam i := by
  calc
    value hϖ n (sphericalSection hϖ n hq z) (Iwasawa.torus ϖ lam) =
        (normalizedCharacter hϖ n hq z (torusBorel n ϖ lam) : ℂ) := by
      simpa using sphericalValue_borel_mul_integral hϖ n hq z (torusBorel n ϖ lam)
        (one_mem (integralSubgroup (ValuativeRel.valuation F).integer n))
    _ = Spherical.halfModulus q lam * ∏ i, (z i : ℂ) ^ lam i := by
      rw [normalizedCharacter_apply, halfModulusCharacter_torus]
      simp

end Langlands.Conductor.UnramifiedPrincipalSeries
