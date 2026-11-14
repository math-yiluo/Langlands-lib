import Langlands.Group.GL.PrincipalLevelDominance
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Exponents.UnrestrictedCompressedLatticeBoundProof
import Langlands.Representation.Whittaker.Spherical

/-!
# Exponential bounds for Whittaker coefficients on the dominant torus

Let `π` be an admissible representation of `GL_(m+1)(F)` over a nonarchimedean local
field, `ℓ` a standard Whittaker functional for a character `ψ` trivial on the integers,
and `K` a positive principal congruence subgroup. For an antitone exponent `μ`, the
compression of `ϖ^μ` to the `K`-fixed vectors is multiplicative and does not change the
Whittaker coefficient. Finite dimensionality of the `K`-fixed vectors then gives an
exponential bound for `ℓ (π (ϖ^μ) v)` in the size of `μ`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.GeneralLinear.Iwasawa
open Langlands.HarmonicAnalysis

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F]

/-! ### The Borel Iwahori factorization of a positive principal level -/

section Factor

variable {m : ℕ}

/-- The upper unipotent radical of the singleton block shape. -/
abbrev borelUpper (F : Type uF) [Field F] (m : ℕ) : Subgroup (GeneralLinear (m + 1) F) :=
  (BlockShape.singletons (m + 1)).unipotentSubgroup F

/-- The diagonal Levi of the singleton block shape. -/
abbrev borelLevi (F : Type uF) [Field F] (m : ℕ) : Subgroup (GeneralLinear (m + 1) F) :=
  (BlockShape.singletons (m + 1)).leviSubgroup F

/-- The lower unipotent radical of the singleton block shape. -/
abbrev borelLower (F : Type uF) [Field F] (m : ℕ) : Subgroup (GeneralLinear (m + 1) F) :=
  (BlockShape.singletons (m + 1)).oppositeUnipotentSubgroup F

/-- Every element of a positive principal level is lower times diagonal times upper. -/
theorem principalLevel_borel_factor {a : ℕ} (ha : 0 < a) :
    ∀ k ∈ principalLevelSubgroup F m a,
      ∃ l ∈ principalLevelSubgroup F m a ⊓ borelLower F m,
        ∃ d ∈ principalLevelSubgroup F m a ⊓ borelLevi F m,
          ∃ u ∈ principalLevelSubgroup F m a ⊓ borelUpper F m, k = l * d * u := by
  intro k hk
  obtain ⟨⟨l, d, u⟩, hldu⟩ :=
    BlockShape.principalLevelSubgroup_iwahoriProduct_surjective F m
      (BlockShape.singletons (m + 1)) a ha ⟨k, hk⟩
  have hval := congrArg Subtype.val hldu
  rw [BlockShape.iwahoriProduct_val] at hval
  exact ⟨l.val, l.property, d.val, d.property, u.val, u.property, hval.symm⟩

omit [ValuativeRel F] in
/-- Torus elements commute with the diagonal Levi. -/
theorem torus_commute_borelLevi (ϖ : Fˣ) (μ : Fin (m + 1) → ℤ) {d : GeneralLinear (m + 1) F}
    (hd : d ∈ borelLevi F m) : torus ϖ μ * d = d * torus ϖ μ := by
  obtain ⟨d₀, rfl⟩ := hd
  rw [torus_eq_blockScalar]
  change (BlockShape.singletons (m + 1)).leviEmbedding F
      ((BlockShape.singletons (m + 1)).blockScalarLevi F _) * _ =
    _ * (BlockShape.singletons (m + 1)).leviEmbedding F
      ((BlockShape.singletons (m + 1)).blockScalarLevi F _)
  rw [← map_mul, ← map_mul, BlockShape.blockScalarLevi_commute]

variable {ϖ : Fˣ} (hϖ : ValuativeRel.valuation F (ϖ : F) ≤ 1)

include hϖ in
/-- An antitone torus element conjugates the upper part of a principal level into it. -/
theorem torus_upper_conj_mem {a : ℕ} {μ : Fin (m + 1) → ℤ} (hμ : Antitone μ)
    {u : GeneralLinear (m + 1) F} (hu : u ∈ principalLevelSubgroup F m a ⊓ borelUpper F m) :
    torus ϖ μ * u * (torus ϖ μ)⁻¹ ∈ principalLevelSubgroup F m a := by
  rw [torus_eq_blockScalar]
  exact principal_upper_conj (BlockShape.singletons (m + 1)) _ _ _
    (ratio_mem_integer hϖ hμ) hu.2 hu.1

include hϖ in
/-- The inverse of an antitone torus element conjugates the lower part into the level. -/
theorem torus_lower_conj_mem {a : ℕ} {μ : Fin (m + 1) → ℤ} (hμ : Antitone μ)
    {l : GeneralLinear (m + 1) F} (hl : l ∈ principalLevelSubgroup F m a ⊓ borelLower F m) :
    (torus ϖ μ)⁻¹ * l * torus ϖ μ ∈ principalLevelSubgroup F m a := by
  rw [torus_eq_blockScalar]
  exact principal_lower_inv_conj (BlockShape.singletons (m + 1)) _ _ _
    (ratio_mem_integer hϖ hμ) hl.2 hl.1

/-- Conjugation by a torus element fixes the diagonal part of a principal level. -/
theorem torus_levi_conj_mem {a : ℕ} (μ : Fin (m + 1) → ℤ)
    {d : GeneralLinear (m + 1) F} (hd : d ∈ principalLevelSubgroup F m a ⊓ borelLevi F m) :
    (torus ϖ μ)⁻¹ * d * torus ϖ μ ∈ principalLevelSubgroup F m a := by
  rw [mul_assoc, ← torus_commute_borelLevi ϖ μ hd.2, ← mul_assoc, inv_mul_cancel, one_mul]
  exact hd.1

end Factor


/-! ### Generators of the antitone cone -/

section Lattice

variable (m : ℕ)

/-- Generators of the monoid of antitone exponents: the indicator of the first `i + 1`
coordinates, and the constant `-1`. -/
def dominantGenerator : Fin (m + 1) ⊕ Unit → Fin (m + 1) → ℤ
  | .inl i => fun j => if j ≤ i then 1 else 0
  | .inr _ => fun _ => -1

theorem dominantGenerator_antitone (i : Fin (m + 1) ⊕ Unit) :
    Antitone (dominantGenerator m i) := by
  cases i with
  | inl i =>
    intro j j' hjj'
    simp only [dominantGenerator]
    by_cases h' : j' ≤ i
    · rw [ite_eq_left h', ite_eq_left (le_trans hjj' h')]
    · rw [ite_eq_right h']
      split_ifs <;> norm_num
  | inr _ => intro _ _ _; simp [dominantGenerator]

/-- The antitone exponent with coordinates `n` in the generators. -/
def latticeExponent (n : Fin (m + 1) ⊕ Unit → ℕ) : Fin (m + 1) → ℤ :=
  ∑ i, (n i : ℤ) • dominantGenerator m i

theorem latticeExponent_add (n n' : Fin (m + 1) ⊕ Unit → ℕ) :
    latticeExponent m (n + n') = latticeExponent m n + latticeExponent m n' := by
  simp only [latticeExponent, Pi.add_apply, Nat.cast_add, add_smul, Finset.sum_add_distrib]

theorem latticeExponent_antitone (n : Fin (m + 1) ⊕ Unit → ℕ) :
    Antitone (latticeExponent m n) := by
  intro j j' h
  simp only [latticeExponent, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (dominantGenerator_antitone m i h) (by positivity)

/-- The gap `μ_i - μ_(i+1)`, with `μ_(m+1) = 0`. -/
def exponentGap (μ : Fin (m + 1) → ℤ) (i : Fin (m + 1)) : ℤ :=
  μ i - if h : i.val + 1 < m + 1 then μ ⟨i.val + 1, h⟩ else 0

theorem sum_exponentGap (μ : Fin (m + 1) → ℤ) (j : Fin (m + 1)) :
    ∑ i, (if j ≤ i then exponentGap m μ i else 0) = μ j := by
  induction j using Fin.reverseInduction with
  | last =>
    rw [Finset.sum_eq_single (Fin.last m)]
    · simp [exponentGap]
    · intro b _ hb
      rw [ite_eq_right]
      exact fun h => hb (le_antisymm (Fin.le_last b) h)
    · simp
  | cast j ih =>
    have hsplit : ∀ i : Fin (m + 1),
        (if j.castSucc ≤ i then exponentGap m μ i else 0) =
          (if j.castSucc = i then exponentGap m μ i else 0) +
            (if j.succ ≤ i then exponentGap m μ i else 0) := by
      intro i
      by_cases h1 : j.castSucc = i
      · subst h1
        have : ¬ j.succ ≤ j.castSucc := not_le.mpr (Fin.castSucc_lt_succ (i := j))
        simp [this]
      · have hiff : j.castSucc ≤ i ↔ j.succ ≤ i := by
          rw [← Fin.castSucc_lt_iff_succ_le]
          exact ⟨fun h => lt_of_le_of_ne h h1, le_of_lt⟩
        simp only [hiff, h1, ite_false, zero_add]
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib,
      Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), ih]
    have hlt : j.castSucc.val + 1 < m + 1 := by simp
    simp only [exponentGap, dite_eq_left hlt]
    have he : (⟨j.castSucc.val + 1, hlt⟩ : Fin (m + 1)) = j.succ := by
      ext
      simp
    rw [he]
    ring

/-- Coordinates of an antitone exponent in the generators. -/
def dominantCoordinates (μ : Fin (m + 1) → ℤ) : Fin (m + 1) ⊕ Unit → ℕ
  | .inl i => (exponentGap m μ i).toNat
  | .inr _ => (-μ (Fin.last m)).toNat

theorem exponentGap_nonneg {μ : Fin (m + 1) → ℤ} (hμ : Antitone μ) {i : Fin (m + 1)}
    (hi : i ≠ Fin.last m) : 0 ≤ exponentGap m μ i := by
  have hlt : i.val + 1 < m + 1 := by
    have := Fin.val_lt_last hi
    omega
  simp only [exponentGap, dite_eq_left hlt, sub_nonneg]
  exact hμ (Fin.mk_le_mk.mpr (Nat.le_succ i.val))

theorem latticeExponent_dominantCoordinates {μ : Fin (m + 1) → ℤ} (hμ : Antitone μ) :
    latticeExponent m (dominantCoordinates m μ) = μ := by
  funext j
  have hgap : ∀ i : Fin (m + 1), ((exponentGap m μ i).toNat : ℤ) =
      exponentGap m μ i + if i = Fin.last m then ((-μ (Fin.last m)).toNat : ℤ) else 0 := by
    intro i
    by_cases hi : i = Fin.last m
    · subst hi
      have hg : exponentGap m μ (Fin.last m) = μ (Fin.last m) := by
        simp [exponentGap]
      rw [ite_eq_left rfl, hg]
      have := Int.toNat_sub_toNat_neg (μ (Fin.last m))
      omega
    · rw [ite_eq_right hi, add_zero, Int.toNat_of_nonneg (exponentGap_nonneg m hμ hi)]
  simp only [latticeExponent, Finset.sum_apply, Fintype.sum_sum_type, Pi.smul_apply,
    smul_eq_mul, dominantCoordinates, dominantGenerator, Finset.univ_unique,
    Finset.sum_singleton]
  have hrw : ∀ i : Fin (m + 1), ((exponentGap m μ i).toNat : ℤ) * (if j ≤ i then 1 else 0) =
      (if j ≤ i then exponentGap m μ i else 0) +
        (if i = Fin.last m then ((-μ (Fin.last m)).toNat : ℤ) else 0) := by
    intro i
    rw [hgap i]
    by_cases hji : j ≤ i
    · rw [ite_eq_left hji, ite_eq_left hji, mul_one]
    · have hi : i ≠ Fin.last m := fun h => hji (h ▸ Fin.le_last j)
      rw [ite_eq_right hji, ite_eq_right hji, ite_eq_right hi, mul_zero, zero_add]
  rw [Finset.sum_congr rfl (fun i _ => hrw i), Finset.sum_add_distrib, sum_exponentGap,
    Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]
  ring

theorem sum_dominantCoordinates_le (μ : Fin (m + 1) → ℤ) :
    ∑ i, dominantCoordinates m μ i ≤ (2 * m + 4) * ∑ j, (μ j).natAbs := by
  set S := ∑ j, (μ j).natAbs
  have hj : ∀ j, (μ j).natAbs ≤ S := fun j =>
    Finset.single_le_sum (f := fun j => (μ j).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  have hcoord : ∀ i, dominantCoordinates m μ i ≤ 2 * S := by
    intro i
    cases i with
    | inl i =>
      simp only [dominantCoordinates]
      have h1 : (exponentGap m μ i).toNat ≤ (exponentGap m μ i).natAbs := by omega
      have h2 : (exponentGap m μ i).natAbs ≤ (μ i).natAbs + S := by
        simp only [exponentGap]
        split_ifs with h
        · have := hj ⟨i.val + 1, h⟩
          have := Int.natAbs_sub_le (μ i) (μ ⟨i.val + 1, h⟩)
          omega
        · simp
      have := hj i
      omega
    | inr _ =>
      simp only [dominantCoordinates]
      have := hj (Fin.last m)
      omega
  calc
    ∑ i, dominantCoordinates m μ i ≤ ∑ _i : Fin (m + 1) ⊕ Unit, 2 * S :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = (2 * m + 4) * S := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
        Fintype.card_unit, smul_eq_mul]
      ring

end Lattice

/-! ### Compression by antitone torus elements -/

section Compression

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] {m : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GeneralLinear (m + 1) F) V) (hπ : IsSmooth π)
variable {ϖ : Fˣ} (hϖ : ValuativeRel.valuation F (ϖ : F) ≤ 1)
variable {a : ℕ} (ha : 0 < a)

include hϖ ha in
/-- Compression by antitone torus elements is multiplicative. -/
theorem compressedAction_torus_add {μ ν : Fin (m + 1) → ℤ} (hμ : Antitone μ)
    (hν : Antitone ν) :
    Jacquet.compressedAction π hπ (principalLevelOpenSubgroup F m a)
        (isCompact_principalLevelOpenSubgroup F m a) (torus ϖ (μ + ν)) =
      Jacquet.compressedAction π hπ (principalLevelOpenSubgroup F m a)
          (isCompact_principalLevelOpenSubgroup F m a) (torus ϖ μ) *
        Jacquet.compressedAction π hπ (principalLevelOpenSubgroup F m a)
          (isCompact_principalLevelOpenSubgroup F m a) (torus ϖ ν) := by
  rw [torus_add]
  exact Jacquet.compressedAction_mul_of_factor π hπ (principalLevelOpenSubgroup F m a)
    (isCompact_principalLevelOpenSubgroup F m a) (borelUpper F m) (borelLevi F m)
    (borelLower F m) (principalLevel_borel_factor ha) _ _
    (fun u hu => torus_upper_conj_mem hϖ hμ hu) (fun l hl => torus_lower_conj_mem hϖ hν hl)
    (fun d hd => torus_levi_conj_mem ν hd)

variable {ψ : UnitaryAdditiveCharacter F}
variable (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)

include hϖ ha hψ in
/-- A standard Whittaker functional does not see the compression of an antitone torus
element: `ℓ (e_K π(ϖ^μ) v) = ℓ (π(ϖ^μ) v)` for `K`-fixed `v`. -/
theorem whittaker_compressedAction_torus (ℓ : glFunctionals ψ m π) {μ : Fin (m + 1) → ℤ}
    (hμ : Antitone μ) (v : fixedVectors π (principalLevelOpenSubgroup F m a).toSubgroup) :
    ℓ.val (Jacquet.compressedAction π hπ (principalLevelOpenSubgroup F m a)
        (isCompact_principalLevelOpenSubgroup F m a) (torus ϖ μ) v : V) =
      ℓ.val (π (torus ϖ μ) v.val) := by
  rw [Jacquet.compressedAction_apply]
  apply Jacquet.map_averageMap_of_forall_eq π hπ _ _ ℓ.val
  intro k
  obtain ⟨u, hu, hk⟩ := Jacquet.exists_upper_translate π (principalLevelOpenSubgroup F m a)
    (borelUpper F m) (borelLevi F m) (borelLower F m) (principalLevel_borel_factor ha)
    (torus ϖ μ) (fun l hl => torus_lower_conj_mem hϖ hμ hl)
    (fun d hd => torus_levi_conj_mem μ hd) v.val v.property k.val k.property
  rw [hk]
  have huN : u ∈ upperUnipotent (m + 1) F := by
    rw [← BlockShape.singletons_unipotentSubgroup]
    exact hu.2
  have huK : u ∈ integralSubgroup (ValuativeRel.valuation F).integer m := by
    have := rankPrincipalLevel_le_integralRange F (m + 1) a hu.1
    exact this
  have hθ := isIntegrallyTrivial_standardCharacter hψ m ⟨u, huN⟩ huK
  rw [ℓ.property ⟨u, huN⟩, hθ, Units.val_one, one_mul]

include hϖ ha hψ in
/-- **Exponential torus bound.** For an admissible `π`, a standard Whittaker functional
`ℓ`, and the principal level `K` of positive level `a`, there is a base `A ≥ 1` such that
every `K`-fixed vector `v` satisfies `‖ℓ (π (ϖ^μ) v)‖ ≤ C A^(∑ |μ_j|)` for all antitone
`μ`, with `C` depending on `v`. -/
theorem whittaker_torus_bound (hπ' : IsAdmissible π) (ℓ : glFunctionals ψ m π) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ v ∈ fixedVectors π (principalLevelOpenSubgroup F m a).toSubgroup,
        ∃ C : ℝ, 0 < C ∧ ∀ μ : Fin (m + 1) → ℤ, Antitone μ →
          ‖ℓ.val (π (torus ϖ μ) v)‖ ≤ C * A ^ (∑ j, (μ j).natAbs) := by
  let K := principalLevelOpenSubgroup F m a
  let hK := isCompact_principalLevelOpenSubgroup F m a
  let W := fixedVectors π K.toSubgroup
  have : FiniteDimensional ℂ W := hπ'.2 K
  let f : (Fin (m + 1) ⊕ Unit → ℕ) → Module.End ℂ W := fun n =>
    Jacquet.compressedAction π hπ'.1 K hK (torus ϖ (latticeExponent m n))
  have hadd : ∀ x y, f (x + y) = f x * f y := by
    intro x y
    simp only [f]
    rw [latticeExponent_add]
    exact compressedAction_torus_add π hπ'.1 hϖ ha (latticeExponent_antitone m x)
      (latticeExponent_antitone m y)
  obtain ⟨b, hb, hbound⟩ := UnrestrictedLatticeBound.exists_apply_le_prod f hadd
  let B : ℝ := ∑ i, b i
  have hbB : ∀ i, b i ≤ B := fun i =>
    Finset.single_le_sum (f := b) (fun j _ => (le_of_lt (lt_trans zero_lt_one (hb j))))
      (Finset.mem_univ i)
  have hB : 1 ≤ B := le_trans (le_of_lt (hb (.inr ()))) (hbB _)
  refine ⟨B ^ (2 * m + 4), one_le_pow₀ hB, fun v hv => ?_⟩
  obtain ⟨C, hC, hCb⟩ := hbound ⟨v, hv⟩ (ℓ.val.comp W.subtype)
  refine ⟨C, hC, fun μ hμ => ?_⟩
  have h1 := hCb (dominantCoordinates m μ)
  change ‖ℓ.val (Jacquet.compressedAction π hπ'.1 K hK
    (torus ϖ (latticeExponent m (dominantCoordinates m μ))) ⟨v, hv⟩ : V)‖ ≤ _ at h1
  rw [whittaker_compressedAction_torus π hπ'.1 hϖ ha hψ ℓ (latticeExponent_antitone m _),
    latticeExponent_dominantCoordinates m hμ] at h1
  refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hC.le)
  calc
    ∏ i, b i ^ dominantCoordinates m μ i ≤ ∏ i, B ^ dominantCoordinates m μ i := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact pow_nonneg (le_of_lt (lt_trans zero_lt_one (hb i))) _
      · intro i _
        exact pow_le_pow_left₀ (le_of_lt (lt_trans zero_lt_one (hb i))) (hbB i) _
    _ = B ^ (∑ i, dominantCoordinates m μ i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ B ^ ((2 * m + 4) * ∑ j, (μ j).natAbs) :=
      pow_le_pow_right₀ hB (sum_dominantCoordinates_le m μ)
    _ = (B ^ (2 * m + 4)) ^ (∑ j, (μ j).natAbs) := pow_mul _ _ _

include hϖ ha hψ in
/-- The torus bound holds uniformly on a finite set of `K`-fixed vectors. -/
theorem whittaker_torus_bound_finite (hπ' : IsAdmissible π) (ℓ : glFunctionals ψ m π)
    {S : Set V} (hS : S.Finite)
    (hSK : S ⊆ fixedVectors π (principalLevelOpenSubgroup F m a).toSubgroup) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ C : ℝ, 0 < C ∧ ∀ v ∈ S, ∀ μ : Fin (m + 1) → ℤ, Antitone μ →
      ‖ℓ.val (π (torus ϖ μ) v)‖ ≤ C * A ^ (∑ j, (μ j).natAbs) := by
  classical
  obtain ⟨A, hA, hbound⟩ := whittaker_torus_bound π hϖ ha hψ hπ' ℓ
  choose! C hC hCb using hbound
  refine ⟨A, hA, 1 + ∑ v ∈ hS.toFinset, C v, ?_, fun v hv μ hμ => ?_⟩
  · have : 0 ≤ ∑ v ∈ hS.toFinset, C v :=
      Finset.sum_nonneg fun w hw => (hC w (hSK ((Set.Finite.mem_toFinset hS).mp hw))).le
    linarith
  · refine le_trans (hCb v (hSK hv) μ hμ) (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hle : C v ≤ ∑ w ∈ hS.toFinset, C w :=
      Finset.single_le_sum (f := C)
        (fun w hw => (hC w (hSK ((Set.Finite.mem_toFinset hS).mp hw))).le)
        ((Set.Finite.mem_toFinset hS).mpr hv)
    linarith

end Compression

end Langlands.Conductor
