import Langlands.ClassField.Global.LocalUnitPowers
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Upper bounds for the indices of local `d`-th powers -/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial IsLocalRing
open scoped NumberField

section GroupIndex

variable {G : Type*} [CommGroup G]

/-- If an endomorphism `f` maps `A` onto a finite-index subgroup `B ≤ A` and has finite kernel,
then the index of its range is at most `(A : B) · |ker f|`. -/
theorem index_range_le_relIndex_mul_card_ker (f : G →* G) (A B : Subgroup G)
    (hAB : A.map f = B) (hBA : B ≤ A) [B.FiniteIndex] [Finite f.ker] :
    f.range.index ≤ B.relIndex A * Nat.card f.ker := by
  have h1 : B.index = (A ⊔ f.ker).index * f.range.index := by
    rw [← hAB]
    exact Subgroup.index_map A f
  have h2 : B.relIndex A * A.index = B.index := Subgroup.relIndex_mul_index hBA
  have h3 : A.relIndex (A ⊔ f.ker) * (A ⊔ f.ker).index = A.index :=
    Subgroup.relIndex_mul_index le_sup_left
  have h4 : A.relIndex (A ⊔ f.ker) = A.relIndex f.ker := Subgroup.relIndex_sup_left _ _
  have h5 : A.relIndex f.ker ≤ Nat.card f.ker :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
  have hne : (A ⊔ f.ker).index ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    exact Subgroup.FiniteIndex.index_ne_zero h1
  have key : (A ⊔ f.ker).index * f.range.index =
      (A ⊔ f.ker).index * (B.relIndex A * A.relIndex f.ker) := by
    rw [← h1, ← h2, ← h3, h4]
    ring
  rw [Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) key]
  exact Nat.mul_le_mul_left _ h5

end GroupIndex

section Hensel

/-- The binomial expansion of `(1 + d c w) ^ d` with `d = e + 1`: the factor `d ^ 2 c` can be
extracted from every term of positive degree. -/
theorem one_add_mul_mul_pow_eq {R : Type*} [CommRing R] (e : ℕ) (c w : R) :
    (1 + ((e + 1 : ℕ) : R) * c * w) ^ (e + 1) =
      1 + ((e + 1 : ℕ) : R) ^ 2 * c * (w + c * (w ^ 2 * ∑ k ∈ Finset.range e,
        (((e + 1).choose (k + 2) : ℕ) : R) * ((e + 1 : ℕ) : R) ^ k * c ^ k * w ^ k)) := by
  rw [show (1 + ((e + 1 : ℕ) : R) * c * w) = 1 + ((e + 1 : ℕ) : R) * (c * w) by ring,
    one_add_mul_pow_eq e (c * w)]
  have hs : ∑ k ∈ Finset.range e, (((e + 1).choose (k + 2) : ℕ) : R) * ((e + 1 : ℕ) : R) ^ k *
      (c * w) ^ k = ∑ k ∈ Finset.range e,
        (((e + 1).choose (k + 2) : ℕ) : R) * ((e + 1 : ℕ) : R) ^ k * c ^ k * w ^ k :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [hs]
  ring

variable {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]

/-- In an `I`-adically complete ring, every element of `1 + d ^ 2 c R` with `c ∈ I` is the
`d`-th power of an element of `1 + d c R`. -/
theorem exists_one_add_mul_mul_pow_eq (d : ℕ) (hd : d ≠ 0) (c : R) (hc : c ∈ I) (t : R) :
    ∃ z : R, (1 + (d : R) * c * z) ^ d = 1 + (d : R) ^ 2 * c * t := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  let Q : R[X] := X ^ 2 * ∑ k ∈ Finset.range e,
    C ((((e + 1).choose (k + 2) : ℕ) : R) * ((e + 1 : ℕ) : R) ^ k * c ^ k) * X ^ k
  let f : R[X] := X + C c * Q - C t
  have hQ : ∀ z : R, Q.eval z = z ^ 2 * ∑ k ∈ Finset.range e,
      (((e + 1).choose (k + 2) : ℕ) : R) * ((e + 1 : ℕ) : R) ^ k * c ^ k * z ^ k := by
    intro z
    simp only [Q, eval_mul, eval_pow, eval_X, eval_finsetSum, eval_C]
  have h₁ : f.eval t ∈ I := by
    simp only [f, eval_sub, eval_add, eval_X, eval_mul, eval_C, add_sub_cancel_left]
    exact I.mul_mem_right _ hc
  have h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval t)) := by
    have hder : f.derivative.eval t = 1 + c * Q.derivative.eval t := by
      simp only [f, derivative_sub, derivative_add, derivative_X, derivative_C_mul, derivative_C,
        sub_zero, eval_add, eval_one, eval_mul, eval_C]
    have hc0 : Ideal.Quotient.mk I c = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hc
    rw [hder, map_add, map_one, map_mul, hc0, zero_mul, add_zero]
    exact isUnit_one
  obtain ⟨z, hz, -⟩ := exists_isRoot_of_isAdicComplete I f t h₁ h₂
  have hz' : z + c * Q.eval z = t := by
    have := hz.eq_zero
    simp only [f, eval_sub, eval_add, eval_X, eval_mul, eval_C] at this
    exact sub_eq_zero.mp this
  refine ⟨z, ?_⟩
  rw [one_add_mul_mul_pow_eq e c z, ← hz', hQ]

end Hensel

section IntegerUnits

variable {K : Type u} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "O" => adicCompletionIntegers K v

/-- The units of `O_v` congruent to `1` modulo an ideal `I`. -/
def integerCongruenceUnits (I : Ideal O) : Subgroup Oˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker

theorem mem_integerCongruenceUnits_iff (I : Ideal O) (x : Oˣ) :
    x ∈ integerCongruenceUnits v I ↔ (x : O) - 1 ∈ I := by
  rw [integerCongruenceUnits, MonoidHom.mem_ker, Units.ext_iff, ← Ideal.Quotient.eq]
  rfl

theorem finite_quotient_of_ne_bot (I : Ideal O) (hI : I ≠ ⊥) : Finite (O ⧸ I) := by
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal O
    (IsPrincipalIdealRing.principal _) I hI
  exact IsLocalRing.finite_quotient_iff.mpr ⟨n, hn.ge⟩

theorem integerCongruenceUnits_finiteIndex (I : Ideal O) (hI : I ≠ ⊥) :
    (integerCongruenceUnits v I).FiniteIndex := by
  have := finite_quotient_of_ne_bot v I hI
  exact Subgroup.finiteIndex_ker _

theorem natCast_ne_zero_adicCompletionIntegers (d : ℕ) (hd : d ≠ 0) : (d : O) ≠ 0 := by
  intro h
  have hK : ((d : O) : v.adicCompletion K) = 0 := by rw [h]; rfl
  rw [show ((d : O) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) d by simp] at hK
  exact (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hd) hK

end IntegerUnits

section CongruenceFiltration

variable {K : Type u} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "O" => adicCompletionIntegers K v

/-- For `c ∈ 𝔪`, the `d`-th power map sends `1 + d c O` onto `1 + d ^ 2 c O`. -/
theorem map_pow_integerCongruenceUnits (d : ℕ) (hd : d ≠ 0) (c : O)
    (hc : c ∈ maximalIdeal O) :
    (integerCongruenceUnits v (Ideal.span {(d : O) * c})).map (powMonoidHom d) =
      integerCongruenceUnits v (Ideal.span {(d : O) ^ 2 * c}) := by
  have := isAdicComplete_adicCompletionIntegers v
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_integerCongruenceUnits_iff] at hx
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hx
    rw [mem_integerCongruenceUnits_iff]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have hx' : (x : O) = 1 + ((e + 1 : ℕ) : O) * c * z := by
      rw [← sub_eq_iff_eq_add', ← hz]; ring
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, hx', one_add_mul_mul_pow_eq e c z,
      add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · intro hy
    rw [mem_integerCongruenceUnits_iff] at hy
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hy
    obtain ⟨z, hz⟩ := exists_one_add_mul_mul_pow_eq (maximalIdeal O) d hd c hc t
    have hzy : (1 + (d : O) * c * z) ^ d = y := by
      rw [hz]; linear_combination ht
    have hu : IsUnit (1 + (d : O) * c * z) := by
      rw [← isUnit_pow_iff hd, hzy]
      exact y.isUnit
    refine ⟨hu.unit, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_integerCongruenceUnits_iff, IsUnit.unit_spec,
        add_sub_cancel_left]
      exact Ideal.mem_span_singleton'.mpr ⟨z, by ring⟩
    · apply Units.ext
      rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, IsUnit.unit_spec, hzy]

/-- The coefficient `z` of `x = 1 + d c z` in the congruence subgroup `1 + d c O`. -/
def congruenceCoeff (d : ℕ) (c : O)
    (x : integerCongruenceUnits v (Ideal.span {(d : O) * c})) : O :=
  Classical.choose (Ideal.mem_span_singleton'.mp
    ((mem_integerCongruenceUnits_iff v _ (x : Oˣ)).mp x.2))

theorem congruenceCoeff_spec (d : ℕ) (c : O)
    (x : integerCongruenceUnits v (Ideal.span {(d : O) * c})) :
    congruenceCoeff v d c x * ((d : O) * c) = ((x : Oˣ) : O) - 1 :=
  Classical.choose_spec (Ideal.mem_span_singleton'.mp
    ((mem_integerCongruenceUnits_iff v _ (x : Oˣ)).mp x.2))

/-- The homomorphism `1 + d c z ↦ z mod d` from `1 + d c O` to `O / d O`. -/
def congruenceCoeffHom (d : ℕ) (c : O) (hdc : (d : O) * c ≠ 0) :
    integerCongruenceUnits v (Ideal.span {(d : O) * c}) →*
      Multiplicative (O ⧸ Ideal.span {(d : O)}) where
  toFun x := Multiplicative.ofAdd (Ideal.Quotient.mk _ (congruenceCoeff v d c x))
  map_one' := by
    have h := congruenceCoeff_spec v d c 1
    rw [OneMemClass.coe_one, Units.val_one, sub_self] at h
    rw [(mul_eq_zero.mp h).resolve_right hdc, map_zero, ofAdd_zero]
  map_mul' x y := by
    have hx := congruenceCoeff_spec v d c x
    have hy := congruenceCoeff_spec v d c y
    have hxy := congruenceCoeff_spec v d c (x * y)
    have key : congruenceCoeff v d c (x * y) = congruenceCoeff v d c x + congruenceCoeff v d c y +
        (d : O) * (c * congruenceCoeff v d c x * congruenceCoeff v d c y) := by
      apply mul_right_cancel₀ hdc
      rw [hxy, Subgroup.coe_mul, Units.val_mul, ← sub_add_cancel ((x : Oˣ) : O) 1,
        ← sub_add_cancel ((y : Oˣ) : O) 1, ← hx, ← hy]
      ring
    have h0 : Ideal.Quotient.mk (Ideal.span {(d : O)})
        ((d : O) * (c * congruenceCoeff v d c x * congruenceCoeff v d c y)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    show Multiplicative.ofAdd (Ideal.Quotient.mk _ (congruenceCoeff v d c (x * y))) =
      Multiplicative.ofAdd (Ideal.Quotient.mk _ (congruenceCoeff v d c x)) *
        Multiplicative.ofAdd (Ideal.Quotient.mk _ (congruenceCoeff v d c y))
    rw [← ofAdd_add, key, map_add (Ideal.Quotient.mk (Ideal.span {(d : O)})), h0, add_zero,
      map_add (Ideal.Quotient.mk (Ideal.span {(d : O)}))]

theorem finite_quotient_natCast (d : ℕ) (hd : d ≠ 0) : Finite (O ⧸ Ideal.span {(d : O)}) :=
  finite_quotient_of_ne_bot v _ (by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact natCast_ne_zero_adicCompletionIntegers v d hd)

/-- The index of `1 + d ^ 2 c O` in `1 + d c O` is at most `|O / d O|`. -/
theorem relIndex_integerCongruenceUnits_le (d : ℕ) (hd : d ≠ 0) (c : O) (hc0 : c ≠ 0) :
    (integerCongruenceUnits v (Ideal.span {(d : O) ^ 2 * c})).relIndex
        (integerCongruenceUnits v (Ideal.span {(d : O) * c})) ≤
      Nat.card (O ⧸ Ideal.span {(d : O)}) := by
  have hd0 := natCast_ne_zero_adicCompletionIntegers v d hd
  have hdc : (d : O) * c ≠ 0 := mul_ne_zero hd0 hc0
  have := finite_quotient_natCast v d hd
  set φ := congruenceCoeffHom v d c hdc
  have hker : φ.ker ≤ (integerCongruenceUnits v (Ideal.span {(d : O) ^ 2 * c})).subgroupOf
      (integerCongruenceUnits v (Ideal.span {(d : O) * c})) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, mem_integerCongruenceUnits_iff, ← congruenceCoeff_spec v d c x]
    have h0 : Ideal.Quotient.mk (Ideal.span {(d : O)}) (congruenceCoeff v d c x) = 0 := by
      have := MonoidHom.mem_ker.mp hx
      exact this
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    exact Ideal.mem_span_singleton'.mpr ⟨s, by rw [← hs]; ring⟩
  have hpos : 0 < φ.ker.index := by
    rw [Subgroup.index_ker]
    exact Nat.card_pos
  calc _ = ((integerCongruenceUnits v (Ideal.span {(d : O) ^ 2 * c})).subgroupOf
        (integerCongruenceUnits v (Ideal.span {(d : O) * c}))).index := rfl
    _ ≤ φ.ker.index := Nat.le_of_dvd hpos (Subgroup.index_dvd_of_le hker)
    _ = Nat.card φ.range := Subgroup.index_ker φ
    _ ≤ Nat.card (Multiplicative (O ⧸ Ideal.span {(d : O)})) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = Nat.card (O ⧸ Ideal.span {(d : O)}) := rfl

/-- The kernel of `x ↦ x ^ d` on `O_vˣ` is the group of `d`-th roots of unity. -/
theorem ker_powMonoidHom_integerUnits (d : ℕ) :
    (powMonoidHom d : Oˣ →* Oˣ).ker = rootsOfUnity d O := by
  ext x
  rw [MonoidHom.mem_ker, mem_rootsOfUnity, powMonoidHom_apply]

/-- The `d`-th powers of `O_vˣ` have index at most `d · |O_v / d O_v|`. -/
theorem index_integerUnitPowers_le (d : ℕ) (hd : d ≠ 0) :
    (powMonoidHom d : Oˣ →* Oˣ).range.index ≤ d * Nat.card (O ⧸ Ideal.span {(d : O)}) := by
  have : NeZero d := ⟨hd⟩
  obtain ⟨c, hc⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hcm : c ∈ maximalIdeal O := (mem_maximalIdeal c).mpr hc.not_isUnit
  have hc0 : c ≠ 0 := hc.ne_zero
  have hd0 := natCast_ne_zero_adicCompletionIntegers v d hd
  have hBA : integerCongruenceUnits v (Ideal.span {(d : O) ^ 2 * c}) ≤
      integerCongruenceUnits v (Ideal.span {(d : O) * c}) := by
    intro x hx
    rw [mem_integerCongruenceUnits_iff] at hx ⊢
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hx
    exact Ideal.mem_span_singleton'.mpr ⟨s * d, by rw [← hs]; ring⟩
  have := integerCongruenceUnits_finiteIndex v (Ideal.span {(d : O) ^ 2 * c}) (by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero (pow_ne_zero 2 hd0) hc0)
  have : Finite (powMonoidHom d : Oˣ →* Oˣ).ker := by
    rw [ker_powMonoidHom_integerUnits]
    infer_instance
  have h := index_range_le_relIndex_mul_card_ker (powMonoidHom d : Oˣ →* Oˣ) _ _
    (map_pow_integerCongruenceUnits v d hd c hcm) hBA
  have hcard : Nat.card (powMonoidHom d : Oˣ →* Oˣ).ker ≤ d := by
    rw [ker_powMonoidHom_integerUnits]
    exact card_rootsOfUnity O d
  calc _ ≤ _ := h
    _ ≤ Nat.card (O ⧸ Ideal.span {(d : O)}) * d :=
        Nat.mul_le_mul (relIndex_integerCongruenceUnits_le v d hd c hc0) hcard
    _ = _ := mul_comm _ _

end CongruenceFiltration

section Transfer

variable {K : Type u} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "O" => adicCompletionIntegers K v

theorem localUnitsToIntegerUnits_injective : Function.Injective (localUnitsToIntegerUnits v) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  have := congrArg (fun u : Oˣ => ((u : O) : v.adicCompletion K)) h
  simpa using this

theorem localUnitsToIntegerUnits_surjective :
    Function.Surjective (localUnitsToIntegerUnits v) := by
  intro x
  have hx : Valued.v ((x : O) : v.adicCompletion K) = 1 :=
    adicCompletionIntegers.isUnit_iff_valued_eq_one.mp x.isUnit
  have h0 : ((x : O) : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact zero_ne_one hx
  refine ⟨⟨Units.mk0 _ h0, (mem_localUnits_iff v _).mpr hx⟩, ?_⟩
  apply Units.ext
  apply Subtype.ext
  rfl

theorem localUnitPowers_eq_comap (d : ℕ) :
    localUnitPowers v d =
      (powMonoidHom d : Oˣ →* Oˣ).range.comap (localUnitsToIntegerUnits v) := by
  ext u
  rw [Subgroup.mem_comap, MonoidHom.mem_range, mem_localUnitPowers_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨localUnitsToIntegerUnits v y, by rw [powMonoidHom_apply, map_pow]⟩
  · rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := localUnitsToIntegerUnits_surjective v z
    refine ⟨y, localUnitsToIntegerUnits_injective v ?_⟩
    rw [map_pow, ← hz, powMonoidHom_apply]

/-- The `d`-th powers of the valuation units have index at most `d · |O_v / d O_v|`. -/
theorem index_localUnitPowers_le (d : ℕ) (hd : d ≠ 0) :
    (localUnitPowers v d).index ≤ d * Nat.card (O ⧸ Ideal.span {(d : O)}) := by
  rw [localUnitPowers_eq_comap,
    Subgroup.index_comap_of_surjective _ (localUnitsToIntegerUnits_surjective v)]
  exact index_integerUnitPowers_le v d hd

end Transfer

section LocalPowers

variable {K : Type u} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "O" => adicCompletionIntegers K v

/-- The `d`-th powers in `K_vˣ`. -/
def localPowers (d : ℕ) : Subgroup (v.adicCompletion K)ˣ :=
  (powMonoidHom d : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range

theorem mem_localPowers_iff (d : ℕ) (x : (v.adicCompletion K)ˣ) :
    x ∈ localPowers v d ↔ ∃ y : (v.adicCompletion K)ˣ, y ^ d = x :=
  Iff.rfl

/-- The valuation exponent modulo `d`. -/
def exponentMod (d : ℕ) : (v.adicCompletion K)ˣ →* Multiplicative (ZMod d) :=
  (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod d))).comp (unitsExponent v)

theorem ker_exponentMod_le (d : ℕ) :
    (exponentMod v d).ker ≤ localPowers v d ⊔ localUnits v := by
  intro x hx
  have hx' : ((Multiplicative.toAdd (unitsExponent v x) : ℤ) : ZMod d) = 0 := by
    have := MonoidHom.mem_ker.mp hx
    exact congrArg Multiplicative.toAdd this
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp hx'
  obtain ⟨π, hπ⟩ := exists_unitsExponent_eq_neg_one v
  have hdecomp : x = (π ^ (-k)) ^ d * (x * π ^ ((d : ℤ) * k)) := by
    rw [← zpow_natCast, ← zpow_mul, mul_left_comm, ← zpow_add, neg_mul, mul_comm (d : ℤ) k,
      neg_add_cancel, zpow_zero, mul_one]
  rw [hdecomp]
  refine Subgroup.mul_mem_sup ⟨π ^ (-k), rfl⟩ ?_
  rw [localUnits, MonoidHom.mem_ker, map_mul, map_zpow]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_zpow, hπ, hk, toAdd_one, smul_eq_mul]
  ring

theorem index_sup_localUnits_le (d : ℕ) (hd : d ≠ 0) :
    (localPowers v d ⊔ localUnits v).index ≤ d ∧ (localPowers v d ⊔ localUnits v).index ≠ 0 := by
  have : NeZero d := ⟨hd⟩
  have hdvd := Subgroup.index_dvd_of_le (ker_exponentMod_le v d)
  have hcard : (exponentMod v d).ker.index ≤ d := by
    rw [Subgroup.index_ker]
    calc Nat.card (exponentMod v d).range ≤ Nat.card (Multiplicative (ZMod d)) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = d := Nat.card_zmod d
  have hpos : 0 < (exponentMod v d).ker.index := by
    rw [Subgroup.index_ker]
    exact Nat.card_pos
  exact ⟨(Nat.le_of_dvd hpos hdvd).trans hcard, Nat.pos_iff_ne_zero.mp (Nat.pos_of_dvd_of_pos hdvd hpos)⟩

theorem localUnitPowers_le_subgroupOf (d : ℕ) :
    localUnitPowers v d ≤ (localPowers v d).subgroupOf (localUnits v) := by
  rintro u ⟨y, rfl⟩
  rw [Subgroup.mem_subgroupOf]
  exact ⟨(y : (v.adicCompletion K)ˣ), rfl⟩

/-- The index of the `d`-th powers in `K_vˣ` is at most `d` times that of the `d`-th powers of
the valuation units, and it is finite. -/
theorem index_localPowers_le_mul (d : ℕ) (hd : d ≠ 0) :
    (localPowers v d).index ≤ d * (localUnitPowers v d).index ∧ (localPowers v d).index ≠ 0 := by
  have := localUnitPowers_finiteIndex v d hd
  have h1 : (localPowers v d).relIndex (localPowers v d ⊔ localUnits v) *
      (localPowers v d ⊔ localUnits v).index = (localPowers v d).index :=
    Subgroup.relIndex_mul_index le_sup_left
  have h2 : (localPowers v d).relIndex (localPowers v d ⊔ localUnits v) =
      (localPowers v d).relIndex (localUnits v) := Subgroup.relIndex_sup_left _ _
  have h3 : (localPowers v d).relIndex (localUnits v) ∣ (localUnitPowers v d).index :=
    Subgroup.index_dvd_of_le (localUnitPowers_le_subgroupOf v d)
  have hpos : 0 < (localUnitPowers v d).index := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)
  have h4 := index_sup_localUnits_le v d hd
  rw [h2] at h1
  rw [← h1]
  refine ⟨?_, mul_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.pos_of_dvd_of_pos h3 hpos)) h4.2⟩
  calc _ ≤ (localUnitPowers v d).index * d := Nat.mul_le_mul (Nat.le_of_dvd hpos h3) h4.1
    _ = _ := mul_comm _ _

theorem localPowers_finiteIndex (d : ℕ) (hd : d ≠ 0) : (localPowers v d).FiniteIndex :=
  ⟨(index_localPowers_le_mul v d hd).2⟩

/-- The `d`-th powers have index at most `d ^ 2 · |O_v / d O_v|` in `K_vˣ`. -/
theorem index_localPowers_le (d : ℕ) (hd : d ≠ 0) :
    (localPowers v d).index ≤ d ^ 2 * Nat.card (O ⧸ Ideal.span {(d : O)}) := by
  calc _ ≤ d * (localUnitPowers v d).index := (index_localPowers_le_mul v d hd).1
    _ ≤ d * (d * Nat.card (O ⧸ Ideal.span {(d : O)})) :=
        Nat.mul_le_mul_left _ (index_localUnitPowers_le v d hd)
    _ = _ := by ring

end LocalPowers

section ResidueNorm

variable {K : Type u} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "O" => adicCompletionIntegers K v

theorem valued_algebraMap_adicCompletion (r : 𝓞 K) :
    Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) r) = v.intValuation r := by
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K)]
  simp only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]

theorem algebraMap_integers_apply' (r : 𝓞 K) :
    algebraMap O (v.adicCompletion K) (algebraMap (𝓞 K) O r) =
      algebraMap (𝓞 K) (v.adicCompletion K) r :=
  rfl

theorem valued_algebraMap_integers (r : 𝓞 K) :
    Valued.v (algebraMap O (v.adicCompletion K) (algebraMap (𝓞 K) O r)) = v.intValuation r := by
  rw [algebraMap_integers_apply']
  exact valued_algebraMap_adicCompletion v r

/-- The algebraic integers whose image in `O_v` is divisible by the image of `b`. -/
def residueIdeal (b : 𝓞 K) : Ideal (𝓞 K) :=
  (Ideal.span {algebraMap (𝓞 K) O b}).comap (algebraMap (𝓞 K) O)

theorem mem_residueIdeal_iff (b r : 𝓞 K) :
    r ∈ residueIdeal v b ↔ v.intValuation r ≤ v.intValuation b := by
  rw [residueIdeal, Ideal.mem_comap, Ideal.mem_span_singleton,
    (adicCompletionIntegers.integers K v).dvd_iff_le, valued_algebraMap_integers,
    valued_algebraMap_integers]

theorem residueIdeal_eq_pow (b : 𝓞 K) (hb : b ≠ 0) :
    residueIdeal v b = v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {b}) := by
  ext r
  rw [mem_residueIdeal_iff, v.intValuation_eq_exp_neg_multiplicity hb]
  exact v.intValuation_le_pow_iff_mem r _

/-- Every element of `O_v` is congruent modulo `b` to an algebraic integer. -/
theorem exists_valued_sub_lt (x : O) (b : 𝓞 K) (hb : b ≠ 0) :
    ∃ a : 𝓞 K, Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) a - (x : v.adicCompletion K)) <
      v.intValuation b := by
  have hβ : v.intValuation b ≠ 0 := v.intValuation_ne_zero b hb
  have hβ' : algebraMap (𝓞 K) (v.adicCompletion K) b ≠ 0 := by
    intro h
    rw [← valued_algebraMap_adicCompletion, h, map_zero] at hβ
    exact hβ rfl
  obtain ⟨y, hy⟩ := (v.denseRange_algebraMap K).exists_dist_lt (x : v.adicCompletion K)
    (norm_pos_iff.mpr hβ')
  rw [dist_eq_norm] at hy
  have hxy : Valued.v ((x : v.adicCompletion K) - algebraMap K (v.adicCompletion K) y) <
      v.intValuation b := by
    rw [← valued_algebraMap_adicCompletion]
    exact Valued.toNormedField.norm_lt_iff.mp hy
  have hx1 : Valued.v (x : v.adicCompletion K) ≤ 1 := x.2
  have hy1 : Valued.v (algebraMap K (v.adicCompletion K) y) ≤ 1 := by
    have h := Valuation.map_sub_le (v := Valued.v) hx1
      (hxy.le.trans (v.intValuation_le_one b))
    rwa [sub_sub_cancel] at h
  have hyv : v.valuation K y ≤ 1 := by
    simpa only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, valuedAdicCompletion_eq_valuation'] using hy1
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer (K := K) hyv (Units.mk0 _ hβ)
  refine ⟨a, ?_⟩
  have ha' : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) a -
      algebraMap K (v.adicCompletion K) y) < v.intValuation b := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K), ← map_sub]
    simpa only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, valuedAdicCompletion_eq_valuation', Units.val_mk0] using ha
  have e : algebraMap (𝓞 K) (v.adicCompletion K) a - (x : v.adicCompletion K) =
      (algebraMap (𝓞 K) (v.adicCompletion K) a - algebraMap K (v.adicCompletion K) y) +
        -((x : v.adicCompletion K) - algebraMap K (v.adicCompletion K) y) := by ring
  rw [e]
  exact Valuation.map_add_lt _ ha' (by rw [Valuation.map_neg]; exact hxy)

theorem algebraMap_quotient_surjective (b : 𝓞 K) (hb : b ≠ 0) :
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {algebraMap (𝓞 K) O b})).comp
      (algebraMap (𝓞 K) O)) := by
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨a, ha⟩ := exists_valued_sub_lt v x b hb
  refine ⟨a, ?_⟩
  rw [RingHom.comp_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton,
    (adicCompletionIntegers.integers K v).dvd_iff_le, valued_algebraMap_integers, map_sub,
    algebraMap_integers_apply']
  exact ha.le

/-- `|O_v / b O_v|` is the absolute norm of the `v`-part of `b`. -/
theorem card_quotient_eq_absNorm (b : 𝓞 K) (hb : b ≠ 0) :
    Nat.card (O ⧸ Ideal.span {algebraMap (𝓞 K) O b}) = Ideal.absNorm (residueIdeal v b) := by
  have hker : RingHom.ker ((Ideal.Quotient.mk (Ideal.span {algebraMap (𝓞 K) O b})).comp
      (algebraMap (𝓞 K) O)) = residueIdeal v b := by
    ext r
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    rfl
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact Nat.card_congr
    (RingHom.quotientKerEquivOfSurjective (algebraMap_quotient_surjective v b hb)).toEquiv.symm

/-- `∏_{v ∈ S} |O_v / b O_v| ≤ |N(b)|`. -/
theorem prod_card_quotient_le (S : Finset (HeightOneSpectrum (𝓞 K))) (b : 𝓞 K) (hb : b ≠ 0) :
    ∏ v ∈ S, Nat.card (v.adicCompletionIntegers K ⧸
      Ideal.span {algebraMap (𝓞 K) (v.adicCompletionIntegers K) b}) ≤
        (Algebra.norm ℤ b).natAbs := by
  rw [Finset.prod_congr rfl fun v _ => card_quotient_eq_absNorm v b hb, ← map_prod,
    Ideal.prod_eq_iInf_of_pairwise_isCoprime, ← Ideal.absNorm_span_singleton]
  · refine Nat.le_of_dvd ?_ (Ideal.absNorm_dvd_absNorm_of_le ?_)
    · rw [Ideal.absNorm_span_singleton]
      exact Int.natAbs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hb)
    · rw [Ideal.span_singleton_le_iff_mem]
      refine Ideal.mem_iInf.mpr fun v => Ideal.mem_iInf.mpr fun _ => ?_
      exact Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _)
  · intro v _ w _ hvw
    rw [Function.onFun, residueIdeal_eq_pow v b hb, residueIdeal_eq_pow w b hb]
    exact isCoprime_pow_of_ne v w hvw _ _

/-- `∏_{v ∈ S} |O_v / d O_v| ≤ d ^ [K : ℚ]`. -/
theorem prod_card_quotient_natCast_le (S : Finset (HeightOneSpectrum (𝓞 K))) (d : ℕ)
    (hd : d ≠ 0) :
    ∏ v ∈ S, Nat.card (v.adicCompletionIntegers K ⧸
      Ideal.span {(d : v.adicCompletionIntegers K)}) ≤ d ^ Module.finrank ℚ K := by
  have h := prod_card_quotient_le S (d : 𝓞 K) (Nat.cast_ne_zero.mpr hd)
  simp only [map_natCast] at h
  rwa [show ((d : 𝓞 K)) = algebraMap ℤ (𝓞 K) (d : ℤ) by simp, Algebra.norm_algebraMap,
    RingOfIntegers.rank, Int.natAbs_pow, Int.natAbs_natCast] at h

end ResidueNorm

section Infinite

variable {K : Type u} [Field K] (w : InfinitePlace K)

/-- At a complex place every unit of the completion is a `d`-th power. -/
theorem infiniteUnitPowers_eq_top_of_isComplex (hw : w.IsComplex) (d : ℕ) (hd : d ≠ 0) :
    infiniteUnitPowers w d = ⊤ := by
  let φ := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (φ (x : w.Completion)) (Nat.pos_of_ne_zero hd)
  have hz0 : φ.symm z ≠ 0 := by
    intro h
    rw [RingEquiv.symm_apply_eq, map_zero] at h
    rw [h, zero_pow hd] at hz
    exact x.ne_zero (φ.injective (by rw [← hz, map_zero]))
  refine ⟨Units.mk0 _ hz0, ?_⟩
  apply Units.ext
  apply φ.injective
  simp [powMonoidHom, hz]

/-- At a real place the `d`-th powers have index at most `2`. -/
theorem index_infiniteUnitPowers_le_two (hw : w.IsReal) (d : ℕ) (hd : d ≠ 0) :
    (infiniteUnitPowers w d).index ≤ 2 := by
  let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have key : ∀ y : (w.Completion)ˣ, 0 < φ (y : w.Completion) → y ∈ infiniteUnitPowers w d := by
    intro y hy
    have hs : φ.symm (φ (y : w.Completion) ^ ((d : ℝ)⁻¹)) ≠ 0 := by
      simp [(Real.rpow_pos_of_pos hy _).ne']
    refine ⟨Units.mk0 _ hs, ?_⟩
    apply Units.ext
    apply φ.injective
    simp [powMonoidHom, Real.rpow_inv_natCast_pow hy.le hd]
  have hsq : ∀ x : (w.Completion)ˣ, x ∈ infiniteUnitPowers w d ∨ -x ∈ infiniteUnitPowers w d := by
    intro x
    have hx : φ (x : w.Completion) ≠ 0 := by simp
    rcases hx.lt_or_gt with h | h
    · right
      apply key
      simpa using h
    · left
      exact key x h
  have hsurj : Function.Surjective (fun b : Bool =>
      if b then (QuotientGroup.mk 1 : (w.Completion)ˣ ⧸ infiniteUnitPowers w d)
      else QuotientGroup.mk (-1)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rcases hsq x with h | h
      · refine ⟨true, ?_⟩
        simp only [ite_true]
        rw [QuotientGroup.eq]
        simpa using h
      · refine ⟨false, ?_⟩
        simp only [Bool.false_eq_true, ite_false]
        rw [QuotientGroup.eq]
        simpa using h
  calc (infiniteUnitPowers w d).index = Nat.card ((w.Completion)ˣ ⧸ infiniteUnitPowers w d) := rfl
    _ ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
    _ = 2 := by simp

/-- The `d`-th powers have index at most `d` at a real place (for `2 ≤ d`) and `1` at a complex
place. -/
theorem index_infiniteUnitPowers_le_ite (d : ℕ) (hd : 2 ≤ d) [Decidable w.IsReal] :
    (infiniteUnitPowers w d).index ≤ if w.IsReal then d else 1 := by
  split_ifs with hw
  · exact (index_infiniteUnitPowers_le_two w hw d (by omega)).trans hd
  · rw [infiniteUnitPowers_eq_top_of_isComplex w (InfinitePlace.not_isReal_iff_isComplex.mp hw) d
      (by omega), Subgroup.index_top]

open scoped Classical in
/-- The product over the infinite places of the indices of `d`-th powers is at most
`d ^ r₁`. -/
theorem prod_index_infiniteUnitPowers_le [NumberField K] (d : ℕ) (hd : 2 ≤ d) :
    ∏ w : InfinitePlace K, (infiniteUnitPowers w d).index ≤ d ^ InfinitePlace.nrRealPlaces K := by
  calc ∏ w : InfinitePlace K, (infiniteUnitPowers w d).index
      ≤ ∏ w : InfinitePlace K, (if w.IsReal then d else 1) :=
        Finset.prod_le_prod fun w _ => index_infiniteUnitPowers_le_ite w d hd
    _ = d ^ InfinitePlace.nrRealPlaces K := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
          InfinitePlace.nrRealPlaces, Fintype.card_subtype]

end Infinite

section Product

variable {K : Type u} [Field K] [NumberField K]

/-- The product of the indices of `d`-th powers over a finite set `S` of finite places and all
infinite places is at most `d ^ (2 (|S| + |S_∞|))`. -/
theorem prod_index_localPowers_le (S : Finset (HeightOneSpectrum (𝓞 K))) (d : ℕ) (hd : 2 ≤ d) :
    (∏ v ∈ S, (localPowers v d).index) * ∏ w : InfinitePlace K, (infiniteUnitPowers w d).index ≤
      d ^ (2 * (S.card + Fintype.card (InfinitePlace K))) := by
  have hd0 : d ≠ 0 := by omega
  have hfin : ∏ v ∈ S, (localPowers v d).index ≤ d ^ (2 * S.card) * d ^ Module.finrank ℚ K :=
    calc ∏ v ∈ S, (localPowers v d).index
        ≤ ∏ v ∈ S, d ^ 2 * Nat.card (v.adicCompletionIntegers K ⧸
          Ideal.span {(d : v.adicCompletionIntegers K)}) :=
          Finset.prod_le_prod fun v _ => index_localPowers_le v d hd0
      _ = d ^ (2 * S.card) * ∏ v ∈ S, Nat.card (v.adicCompletionIntegers K ⧸
          Ideal.span {(d : v.adicCompletionIntegers K)}) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul]
      _ ≤ _ := Nat.mul_le_mul_left _ (prod_card_quotient_natCast_le S d hd0)
  calc _ ≤ d ^ (2 * S.card) * d ^ Module.finrank ℚ K * d ^ InfinitePlace.nrRealPlaces K :=
        Nat.mul_le_mul hfin (prod_index_infiniteUnitPowers_le d hd)
    _ = _ := by
        rw [← pow_add, ← pow_add, ← InfinitePlace.card_add_two_mul_card_eq_rank,
          InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
        congr 1
        ring

end Product

end Langlands.ClassField.Global
