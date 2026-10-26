import Langlands.Representation.RankinSelberg.UnequalRankIwasawaSupportStatement
import Langlands.LocalField.Normalization.Proof
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace Langlands.RankinSelberg

open scoped BigOperators

universe uF u

private theorem suffix_minor_mul {K : Type u} [CommRing K] {m : ℕ}
    (t : Fin m) (U A : Matrix (Fin m) (Fin m) K)
    (hU : U.IsUpperTriangular) (c : {i : Fin m // t ≤ i} → Fin m) :
    Matrix.det ((U * A).submatrix Subtype.val c) =
      (∏ i : {i : Fin m // t ≤ i}, U i i) *
        Matrix.det (A.submatrix Subtype.val c) := by
  classical
  have hm : (U * A).submatrix Subtype.val c =
      (U.submatrix Subtype.val Subtype.val :
        Matrix {i : Fin m // t ≤ i} {i : Fin m // t ≤ i} K) *
        A.submatrix Subtype.val c := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    apply Finset.sum_congr_set {q : Fin m | t ≤ q}
    · intro q hq
      rfl
    · intro q hq
      rw [hU (lt_of_lt_of_le (lt_of_not_ge hq) i.property), zero_mul]
  have hsub : (U.submatrix Subtype.val Subtype.val :
      Matrix {i : Fin m // t ≤ i} {i : Fin m // t ≤ i} K).IsUpperTriangular := by
    intro i j hij
    exact hU hij
  rw [hm, Matrix.det_mul, Matrix.det_of_isUpperTriangular hsub]
  rfl

private theorem det_mem_subring {K : Type u} [CommRing K] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (O : Subring K) (A : Matrix ι ι K)
    (hA : ∀ i j, A i j ∈ O) : A.det ∈ O := by
  let B : Matrix ι ι O := fun i j => ⟨A i j, hA i j⟩
  have he : (B.map O.subtype) = A := rfl
  rw [← he]
  change (O.subtype.mapMatrix B).det ∈ O
  rw [← O.subtype.map_det]
  exact (B.det).property

private theorem unequalRankMatrix_identity_columns {K : Type u} [Field K]
    {n : ℕ} (j k : ℕ) (g : Langlands.GeneralLinear (n + 1) K)
    (x : Matrix (Fin j) (Fin (n + 1)) K)
    (a b : Fin (n + (j + k + 1) + 1))
    (ha : n + 1 ≤ a.val) (hb : n + 1 ≤ b.val) :
    unequalRankMatrix j k g x a b = if a = b then 1 else 0 := by
  rw [unequalRankMatrix_val]
  simp [appendIdentity_entry, rectangularEntries, not_lt.mpr ha, not_lt.mpr hb]

private theorem unequalRankMatrix_rectangular_entry {K : Type u} [Field K]
    {n : ℕ} (j k : ℕ) (g : Langlands.GeneralLinear (n + 1) K)
    (x : Matrix (Fin j) (Fin (n + 1)) K) (t : Fin j) (c : Fin (n + 1)) :
    unequalRankMatrix j k g x ⟨n + 1 + t.val, by omega⟩
      ⟨c.val, by omega⟩ = x t c := by
  rw [unequalRankMatrix_val]
  simp [appendIdentity_entry, rectangularEntries, Fin.ext_iff,
    show ¬n + 1 + t.val < n + 1 by omega,
    show n + 1 ≤ n + 1 + t.val ∧ n + 1 + t.val < n + 1 + j by omega,
    show n + 1 + t.val ≠ c.val by omega, show c.val ≤ n by omega]

private theorem unequalRankMatrix_entry_minor {K : Type u} [Field K]
    {n : ℕ} (j k : ℕ) (g : Langlands.GeneralLinear (n + 1) K)
    (x : Matrix (Fin j) (Fin (n + 1)) K) (t : Fin j) (c : Fin (n + 1)) :
    let t' : Fin (n + (j + k + 1) + 1) := ⟨n + 1 + t.val, by omega⟩
    let S := {i : Fin (n + (j + k + 1) + 1) // t' ≤ i}
    let cols : S → Fin (n + (j + k + 1) + 1) :=
      fun i => if i.val = t' then ⟨c.val, by omega⟩ else i.val
    Matrix.det ((unequalRankMatrix j k g x).val.submatrix Subtype.val cols) = x t c := by
  classical
  dsimp only
  let t' : Fin (n + (j + k + 1) + 1) := ⟨n + 1 + t.val, by omega⟩
  let S := {i : Fin (n + (j + k + 1) + 1) // t' ≤ i}
  let t₀ : S := ⟨t', le_rfl⟩
  let cols : S → Fin (n + (j + k + 1) + 1) :=
    fun i => if i.val = t' then ⟨c.val, by omega⟩ else i.val
  let B : Matrix S S K := (unequalRankMatrix j k g x).val.submatrix Subtype.val cols
  change B.det = x t c
  have hd (i : S) (hi : i ≠ t₀) : B i i = 1 := by
    have hne : i.val ≠ t' := by intro h; exact hi (Subtype.ext h)
    change unequalRankMatrix j k g x i.val (cols i) = 1
    rw [show cols i = i.val by simp [cols, hne]]
    rw [unequalRankMatrix_identity_columns j k g x i.val i.val (by
      have := i.property; change n + 1 + t.val ≤ i.val.val at this; omega) (by
      have := i.property; change n + 1 + t.val ≤ i.val.val at this; omega)]
    simp
  have hB : B.IsLowerTriangular := by
    intro i l hil
    have hne : l.val ≠ t' := by
      intro h
      have := i.property
      have : l ≤ i := by change l.val ≤ i.val; simpa [h] using this
      exact (not_le_of_gt hil) this
    change unequalRankMatrix j k g x i.val (cols l) = 0
    rw [show cols l = l.val by simp [cols, hne]]
    rw [unequalRankMatrix_identity_columns j k g x i.val l.val (by
      have := i.property; change n + 1 + t.val ≤ i.val.val at this; omega) (by
      have := l.property; change n + 1 + t.val ≤ l.val.val at this; omega)]
    exact ite_eq_right (fun h => (ne_of_lt hil) (Subtype.ext h.symm))
  rw [Matrix.det_of_isLowerTriangular B hB]
  rw [Finset.prod_eq_single t₀ (fun i _ hi => hd i hi) (by simp)]
  change unequalRankMatrix j k g x t' (cols t₀) = x t c
  simp only [cols, t₀, ite_eq_left rfl]
  exact unequalRankMatrix_rectangular_entry j k g x t c

private theorem unequalRankMatrix_last_row {K : Type u} [Field K]
    {n : ℕ} (j k : ℕ) (g : Langlands.GeneralLinear (n + 1) K)
    (x : Matrix (Fin j) (Fin (n + 1)) K)
    (b : Fin (n + (j + k + 1) + 1)) :
    unequalRankMatrix j k g x (Fin.last (n + (j + k + 1))) b =
      if Fin.last (n + (j + k + 1)) = b then 1 else 0 := by
  rw [unequalRankMatrix_val]
  simp [appendIdentity_entry, rectangularEntries, Fin.val_last,
    show ¬n + (j + k + 1) < n + 1 by omega,
    show ¬n + (j + k + 1) < n + 1 + j by omega]

private theorem normalizedAbs_prod {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {ι : Type*}
    (s : Finset ι) (f : ι → F.Carrier) :
    T.normalizedAbs (∏ i ∈ s, f i) = ∏ i ∈ s, T.normalizedAbs (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [T.normalizedAbs_one]
  | @insert a s ha ih => simp [ha, T.normalizedAbs_mul, ih]

private theorem diagonal_abs_last {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    letI := T.valuativeRel
    ∀ (r : ℕ) (M u : Langlands.GeneralLinear (r + 1) F.Carrier)
      (a : Fin (r + 1) → F.Carrierˣ) (κ : Langlands.GeneralLinear (r + 1) F.Carrier),
      (∀ b, M (Fin.last r) b = if Fin.last r = b then 1 else 0) →
      u ∈ GeneralLinear.upperUnipotent (r + 1) F.Carrier →
      κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r →
      M = u * GeneralLinear.Iwasawa.diagonalUnits a * κ →
      T.normalizedAbs (a (Fin.last r) : F.Carrier) = 1 := by
  let := T.valuativeRel
  intro r M u a κ hM hu hκ he
  have hrow (b : Fin (r + 1)) :
      (u * GeneralLinear.Iwasawa.diagonalUnits a) (Fin.last r) b =
        if Fin.last r = b then (a (Fin.last r) : F.Carrier) else 0 := by
    change (u.val * (GeneralLinear.Iwasawa.diagonalUnits a).val) (Fin.last r) b = _
    rw [GeneralLinear.Iwasawa.diagonalUnits_val, Matrix.mul_diagonal]
    by_cases h : Fin.last r = b
    · subst b
      rw [hu.2 (Fin.last r)]
      simp
    · have hb : b < Fin.last r := lt_of_le_of_ne (Fin.le_last b) (Ne.symm h)
      have hz : u.val (Fin.last r) b = 0 := hu.1 hb
      rw [hz, zero_mul]
      simp [h]
  have he' : M * κ⁻¹ = u * GeneralLinear.Iwasawa.diagonalUnits a := by
    rw [he, mul_assoc, mul_inv_cancel, mul_one]
  have ha : (a (Fin.last r) : F.Carrier) = κ⁻¹ (Fin.last r) (Fin.last r) := by
    have h := congrArg (fun z : Langlands.GeneralLinear (r + 1) F.Carrier =>
      z (Fin.last r) (Fin.last r)) he'
    change (M.val * (κ⁻¹).val) (Fin.last r) (Fin.last r) = _ at h
    rw [Matrix.mul_apply, hrow] at h
    simpa [hM] using h.symm
  have hκ' := (Conductor.mem_integralSubgroup _ _ κ).mp hκ
  have ha_le : T.normalizedAbs (a (Fin.last r) : F.Carrier) ≤ 1 := by
    rw [ha]
    exact (T.normalizedAbs_le_one_iff_mem_integers _).mpr (hκ'.2 _ _)
  have hentry : (1 : F.Carrier) = (a (Fin.last r) : F.Carrier) * κ (Fin.last r) (Fin.last r) := by
    have h := congrArg (fun z : Langlands.GeneralLinear (r + 1) F.Carrier =>
      z (Fin.last r) (Fin.last r)) he
    change M (Fin.last r) (Fin.last r) =
      ((u * GeneralLinear.Iwasawa.diagonalUnits a).val * κ.val) (Fin.last r) (Fin.last r) at h
    rw [Matrix.mul_apply] at h
    simp_rw [hrow] at h
    simpa [hM] using h
  have hκle : T.normalizedAbs (κ (Fin.last r) (Fin.last r)) ≤ 1 :=
    (T.normalizedAbs_le_one_iff_mem_integers _).mpr (hκ'.1 _ _)
  have hge : 1 ≤ T.normalizedAbs (a (Fin.last r) : F.Carrier) := by
    calc
      1 = T.normalizedAbs (a (Fin.last r) : F.Carrier) *
          T.normalizedAbs (κ (Fin.last r) (Fin.last r)) := by
        rw [← T.normalizedAbs_mul, ← hentry, T.normalizedAbs_one]
      _ ≤ T.normalizedAbs (a (Fin.last r) : F.Carrier) * 1 :=
        mul_le_mul_of_nonneg_left hκle (T.normalizedAbs_nonneg _)
      _ = _ := mul_one _
  exact le_antisymm ha_le hge

private theorem diagonal_abs_bound {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (r : ℕ)
    (a : Fin (r + 1) → F.Carrierˣ) (B : ℝ) (hB : 1 ≤ B)
    (hlast : T.normalizedAbs (a (Fin.last r) : F.Carrier) = 1)
    (hroot : ∀ i : Fin r,
      T.normalizedAbs ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier) ≤ B) :
    ∀ i, T.normalizedAbs (a i : F.Carrier) ≤ B ^ r := by
  have hprecise (i : Fin (r + 1)) :
      T.normalizedAbs (a i : F.Carrier) ≤ B ^ (r - i.val) := by
    induction i using Fin.reverseInduction with
    | last => simp [hlast]
    | @cast i ih =>
      have he : T.normalizedAbs (a i.castSucc : F.Carrier) =
          T.normalizedAbs ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier) *
            T.normalizedAbs (a i.succ : F.Carrier) := by
        rw [← T.normalizedAbs_mul, ← Units.val_mul, div_mul_cancel]
      rw [he]
      calc
        _ ≤ B * B ^ (r - i.succ.val) :=
          mul_le_mul (hroot i) ih (T.normalizedAbs_nonneg _) (zero_le_one.trans hB)
        _ = B ^ (r - i.castSucc.val) := by
          rw [← pow_succ']
          congr 1
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega
  intro i
  exact (hprecise i).trans (pow_le_pow_right₀ hB (Nat.sub_le _ _))

private theorem iwasawa_suffix_minor_bound {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    letI := T.valuativeRel
    ∀ (r : ℕ) (u : Langlands.GeneralLinear (r + 1) F.Carrier)
      (a : Fin (r + 1) → F.Carrierˣ) (κ : Langlands.GeneralLinear (r + 1) F.Carrier),
      u ∈ GeneralLinear.upperUnipotent (r + 1) F.Carrier →
      κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r →
      ∀ (t : Fin (r + 1)) (c : {i : Fin (r + 1) // t ≤ i} → Fin (r + 1)),
      T.normalizedAbs (Matrix.det ((u * GeneralLinear.Iwasawa.diagonalUnits a * κ).val.submatrix
        Subtype.val c)) ≤ ∏ i : {i : Fin (r + 1) // t ≤ i}, T.normalizedAbs (a i : F.Carrier) := by
  classical
  let := T.valuativeRel
  intro r u a κ hu hκ t c
  have htri : (u * GeneralLinear.Iwasawa.diagonalUnits a).val.IsUpperTriangular := by
    intro i j hij
    change (u.val * (GeneralLinear.Iwasawa.diagonalUnits a).val) i j = 0
    rw [GeneralLinear.Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, hu.1 hij, zero_mul]
  have hdiag (i : Fin (r + 1)) :
      (u * GeneralLinear.Iwasawa.diagonalUnits a) i i = (a i : F.Carrier) := by
    change (u.val * (GeneralLinear.Iwasawa.diagonalUnits a).val) i i = _
    rw [GeneralLinear.Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, hu.2 i, one_mul]
  have hdet : (κ.val.submatrix Subtype.val c).det ∈ T.Integers :=
    det_mem_subring T.Integers _ fun i l =>
      ((Conductor.mem_integralSubgroup _ _ κ).mp hκ).1 i (c l)
  have hle := (T.normalizedAbs_le_one_iff_mem_integers _).mpr hdet
  change T.normalizedAbs (Matrix.det (((u * GeneralLinear.Iwasawa.diagonalUnits a).val * κ.val).submatrix
    Subtype.val c)) ≤ _
  rw [suffix_minor_mul t _ _ htri c]
  simp_rw [hdiag]
  rw [T.normalizedAbs_mul, normalizedAbs_prod F T]
  exact (mul_le_mul_of_nonneg_left hle (Finset.prod_nonneg fun i _ => T.normalizedAbs_nonneg _)).trans_eq
    (mul_one _)

private theorem exists_compact_abs_bound {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (B : ℝ) (hB : 1 ≤ B) :
    letI := T.topology
    ∃ D : Set F.Carrier, IsCompact D ∧
      ∀ z, T.normalizedAbs z ≤ B → z ∈ D := by
  rw [T.topology_eq_canonicalNormTopology]
  let := F.canonicalNormedField
  let := F.canonicalNormedAlgebra
  let := FiniteDimensional.proper (Padic p) F.Carrier
  refine ⟨Metric.closedBall 0 B, isCompact_closedBall 0 B, ?_⟩
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have hn : Module.finrank (Padic p) F.Carrier ≠ 0 :=
    (PadicField.TopologicalData.extensionDegree_pos (F := F)).ne'
  apply le_of_pow_le_pow_left₀ hn (zero_le_one.trans hB)
  calc
    ‖z‖ ^ Module.finrank (Padic p) F.Carrier = T.normalizedAbs z :=
      (T.normalizedAbs_eq_canonicalNorm_pow_degree z).symm
    _ ≤ B := hz
    _ ≤ B ^ Module.finrank (Padic p) F.Carrier := le_self_pow₀ hB hn

/-- Bounded adjacent Iwasawa ratios force a uniform compact rectangular support. -/
theorem unequalRankIwasawaSupport {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n j k : ℕ) :
    UnequalRankIwasawaSupportStatement F T n j k := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let r := n + (j + k + 1)
  intro R _hR
  let B : ℝ := max 1 R
  have hB : 1 ≤ B := le_max_left _ _
  obtain ⟨D, hD, hcontain⟩ :=
    exists_compact_abs_bound F T ((B ^ r) ^ (r + 1)) (one_le_pow₀ (one_le_pow₀ hB))
  refine ⟨{x | ∀ t c, x t c ∈ D}, ?_, ?_⟩
  · exact isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => hD
  · intro g x u a κ hu hκ he hroot
    have hlast : T.normalizedAbs (a (Fin.last r) : F.Carrier) = 1 :=
      diagonal_abs_last F T r (unequalRankMatrix j k g x) u a κ
        (unequalRankMatrix_last_row j k g x) hu hκ he
    have habound : ∀ i, T.normalizedAbs (a i : F.Carrier) ≤ B ^ r :=
      diagonal_abs_bound F T r a B hB hlast fun i =>
        (hroot i).trans (le_max_right _ _)
    intro t c
    apply hcontain
    let t' : Fin (r + 1) := ⟨n + 1 + t.val, by dsimp [r]; omega⟩
    let S := {i : Fin (r + 1) // t' ≤ i}
    let cols : S → Fin (r + 1) :=
      fun i => if i.val = t' then ⟨c.val, by dsimp [r]; omega⟩ else i.val
    have hentry : Matrix.det ((unequalRankMatrix j k g x).val.submatrix Subtype.val cols) =
        x t c := unequalRankMatrix_entry_minor j k g x t c
    have hminor := iwasawa_suffix_minor_bound F T r u a κ hu hκ t' cols
    rw [← he, hentry] at hminor
    calc
      T.normalizedAbs (x t c) ≤ ∏ i : S, T.normalizedAbs (a i : F.Carrier) := hminor
      _ ≤ ∏ _i : S, B ^ r :=
        Finset.prod_le_prod₀ (fun i _ => T.normalizedAbs_nonneg _) (fun i _ => habound i)
      _ = (B ^ r) ^ Fintype.card S := by simp
      _ ≤ (B ^ r) ^ (r + 1) := by
        apply pow_le_pow_right₀ (one_le_pow₀ hB)
        simpa [S] using Fintype.card_subtype_le (fun i : Fin (r + 1) => t' ≤ i)

end Langlands.RankinSelberg
