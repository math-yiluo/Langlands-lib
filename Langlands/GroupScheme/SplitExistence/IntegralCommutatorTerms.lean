import Langlands.GroupScheme.SplitExistence.ToChevalleyData
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-! # Integral monomial parameters in the Chevalley commutator

The two polynomial variables are the outer `X` and the inner `X`. The bidegree
`(i, j)` in a universal root commutator can only move weights by `iα + jβ`.
-/

noncomputable section

universe u

open Matrix Polynomial Finset

local notation "s₀" => (Polynomial.X : ℤ[X][X])
local notation "t₀" => (Polynomial.C (Polynomial.X : ℤ[X]) : ℤ[X][X])

namespace Langlands.GroupScheme.SplitExistence

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y}

/-- One integral monomial parameter in the commutator of the roots `α` and `β`. -/
structure CommutatorTerm (P : RootDatum J X Y) (α β : J) where
  root : J
  i : ℕ
  j : ℕ
  coefficient : ℤ
  i_pos : 0 < i
  j_pos : 0 < j
  root_eq : P.root root = i • P.root α + j • P.root β

namespace CommutatorTerm

variable {α β : J}

/-- The parameter `c s^i t^j` in a commutative ring. -/
def parameter (q : CommutatorTerm P α β) {R : Type*} [CommRing R] (s t : R) : R :=
  (q.coefficient : R) * s ^ q.i * t ^ q.j

private theorem parameter_generic (q : CommutatorTerm P α β) :
    q.parameter s₀ t₀ = monomial q.i (monomial q.j q.coefficient) := by
  simp only [parameter, ← Polynomial.C_eq_intCast, ← map_pow]
  rw [mul_right_comm, ← map_mul, C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial]
  simp

end CommutatorTerm

namespace LieRootData

variable (D : LieRootData P)

/-- A coefficient of bidegree `(i, j)` can occur only at weight difference `iα + jβ`. -/
private def WeightGraded (α β : J) (M : Matrix (Fin D.n) (Fin D.n) ℤ[X][X]) : Prop :=
  ∀ c d i j, ((M c d).coeff i).coeff j ≠ 0 → D.wt c - D.wt d = i • P.root α + j • P.root β

private theorem WeightGraded.mul {D : LieRootData P} {α β : J}
    {A B : Matrix (Fin D.n) (Fin D.n) ℤ[X][X]}
    (hA : D.WeightGraded α β A) (hB : D.WeightGraded α β B) :
    D.WeightGraded α β (A * B) := by
  intro c d i j hn
  rw [Matrix.mul_apply, finsetSum_coeff, finsetSum_coeff] at hn
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  rw [coeff_mul, finsetSum_coeff] at he
  obtain ⟨p, hp, hp'⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  rw [coeff_mul] at hp'
  obtain ⟨q, hq, hq'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp'
  rw [← Finset.mem_antidiagonal.mp hp, ← Finset.mem_antidiagonal.mp hq, add_nsmul, add_nsmul,
    ← sub_add_sub_cancel (D.wt c) (D.wt e) (D.wt d),
    hA _ _ _ _ (left_ne_zero_of_mul hq'), hB _ _ _ _ (right_ne_zero_of_mul hq')]
  abel

private theorem weightGraded_divExp {α β r : J} {a b : ℕ}
    (hr : P.root r = a • P.root α + b • P.root β) (z : ℤ) :
    D.WeightGraded α β (divExp (D.e r) (monomial a (monomial b z))) := by
  intro c d i j hn
  rw [D.divExp_eq, Matrix.sum_apply, finsetSum_coeff, finsetSum_coeff] at hn
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  simp only [Matrix.smul_apply, smul_eq_mul, em, Matrix.map_apply, eq_intCast] at hk
  rw [← Polynomial.C_eq_intCast (R := ℤ[X]), coeff_mul_C,
    ← Polynomial.C_eq_intCast (R := ℤ), coeff_mul_C, monomial_pow] at hk
  by_cases hi : a * k = i
  · rw [hi, coeff_monomial_same, monomial_pow] at hk
    by_cases hj : b * k = j
    · rw [hj, coeff_monomial_same] at hk
      have he := right_ne_zero_of_mul hk
      have hw := sub_eq_iff_eq_add'.mpr (D.e_weight r k c d he)
      rw [hw, ← hi, ← hj, hr, nsmul_add, smul_smul, smul_smul, Nat.mul_comm k a, Nat.mul_comm k b]
    · rw [coeff_monomial_of_ne _ (Ne.symm hj), zero_mul] at hk
      exact (hk rfl).elim
  · rw [coeff_monomial_of_ne _ (Ne.symm hi), coeff_zero, zero_mul] at hk
    exact (hk rfl).elim

/-- In an ordered integral polynomial product with the expected weight shifts, recover the
monomial at the first root and peel off its inverse to recover the remaining factors. -/
private theorem exists_terms_of_weightGraded (h : X →+ ℤ) {α β : J}
    (hα : 0 < h (P.root α)) (hβ : 0 < h (P.root β))
    (hinj : Function.Injective (fun p : ℕ × ℕ => p.1 • P.root α + p.2 • P.root β)) :
    ∀ L : List (J × ℤ[X][X]), (∀ p ∈ L, p.1 ∈ commRoots P α β) →
      L.Pairwise (fun p q => p.1 ≠ q.1 ∧ h (P.root p.1) ≤ h (P.root q.1)) →
      D.WeightGraded α β (L.map fun p => divExp (D.e p.1) p.2).prod →
      ∃ T : List (CommutatorTerm P α β),
        T.map (fun p => (p.root, p.parameter s₀ t₀)) = L := by
  intro L
  induction L with
  | nil => exact fun _ _ _ => ⟨[], rfl⟩
  | cons p L ih =>
    obtain ⟨r, f⟩ := p
    intro hL horder hgraded
    have hroot := hL _ (List.mem_cons_self ..)
    have hpos := commRoots_pos h hα hβ hroot
    obtain ⟨i, j, hi, hj, hr⟩ := hroot
    rw [List.pairwise_cons] at horder
    rw [List.map_cons, List.prod_cons] at hgraded
    have hentry : ∃ c d, D.e r 1 c d ≠ 0 := by
      by_contra! hz
      have hz' : D.e r 1 = 0 := Matrix.ext fun c d => by simpa using hz c d
      exact D.e_one_map_ne_zero r 2 Nat.prime_two (by simp [hz'])
    obtain ⟨c, d, he⟩ := hentry
    have hw := D.e_weight r 1 c d he
    rw [one_smul] at hw
    have hfirst := D.prod_cons_apply h hpos f L horder.1 hw
    have hdegree (a b : ℕ) (hf : (f.coeff a).coeff b ≠ 0) : (a, b) = (i, j) := by
      apply hinj
      have hn : (((divExp (D.e r) f * (L.map fun p => divExp (D.e p.1) p.2).prod) c d).coeff a).coeff b ≠ 0 := by
        rw [hfirst]
        change ((f * ((D.e r 1 c d : ℤ) : ℤ[X][X])).coeff a).coeff b ≠ 0
        rw [← Polynomial.C_eq_intCast, ← Polynomial.C_eq_intCast, coeff_mul_C, coeff_mul_C]
        exact mul_ne_zero hf he
      have hshift := hgraded c d a b hn
      rw [hw, add_sub_cancel_left, hr] at hshift
      exact hshift.symm
    let z := (f.coeff i).coeff j
    have hf : f = monomial i (monomial j z) := by
      apply Polynomial.ext
      intro a
      apply Polynomial.ext
      intro b
      by_cases hab : (a, b) = (i, j)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
        simp [z]
      · have hab' : (f.coeff a).coeff b = 0 := by
          by_contra hn
          exact hab (hdegree a b hn)
        rw [hab']
        by_cases ha : i = a
        · have hb : j ≠ b := fun e => hab (Prod.ext ha.symm e.symm)
          rw [ha, coeff_monomial_same, coeff_monomial_of_ne _ hb.symm]
        · rw [coeff_monomial_of_ne _ (Ne.symm ha), coeff_zero]
    have hneg : D.WeightGraded α β (divExp (D.e r) (-f)) := by
      rw [hf, ← map_neg, ← map_neg]
      exact D.weightGraded_divExp hr (-z)
    have htail := hneg.mul hgraded
    rw [← Matrix.mul_assoc, D.divExp_neg_mul_divExp, Matrix.one_mul] at htail
    obtain ⟨T, hT⟩ := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) horder.2 htail
    let term : CommutatorTerm P α β := ⟨r, i, j, z, by omega, by omega, hr⟩
    refine ⟨term :: T, ?_⟩
    rw [List.map_cons, hT, term.parameter_generic, ← hf]

private theorem rootCombination_injective [P.IsReduced] {α β : J}
    (hne : α ≠ β) (hopp : P.root α ≠ -P.root β) :
    Function.Injective (fun p : ℕ × ℕ => p.1 • P.root α + p.2 • P.root β) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ hab
  have hlin := LinearIndependent.pair_iff.mp (RootPairing.IsReduced.linearIndependent P hne hopp)
  have hzero : ((a : ℤ) - c) • P.root α + ((b : ℤ) - d) • P.root β = 0 := by
    rw [sub_smul, sub_smul, sub_add_sub_comm, sub_eq_zero]
    simpa only [natCast_zsmul] using hab
  obtain ⟨hac, hbd⟩ := hlin _ _ hzero
  exact Prod.ext (by omega) (by omega)

private theorem weightGraded_commutator (α β : J) :
    D.WeightGraded α β
      (divExp (D.e α) s₀ * divExp (D.e β) t₀ * divExp (D.e α) (-s₀) * divExp (D.e β) (-t₀)) := by
  have ha : P.root α = (1 : ℕ) • P.root α + (0 : ℕ) • P.root β := by simp
  have hb : P.root β = (0 : ℕ) • P.root α + (1 : ℕ) • P.root β := by simp
  have hs : monomial 1 (monomial 0 (1 : ℤ)) = s₀ := by
    rw [monomial_zero_left, map_one, monomial_one_one_eq_X]
  have ht : monomial 0 (monomial 1 (1 : ℤ)) = t₀ := by
    rw [monomial_zero_left, monomial_one_one_eq_X]
  have h1 := D.weightGraded_divExp ha 1
  have h2 := D.weightGraded_divExp hb 1
  have h3 := D.weightGraded_divExp ha (-1)
  have h4 := D.weightGraded_divExp hb (-1)
  rw [hs] at h1
  rw [ht] at h2
  rw [map_neg, map_neg, hs] at h3
  rw [map_neg, map_neg, ht] at h4
  exact ((h1.mul h2).mul h3).mul h4

/-- The ordered commutator factors over `ℤ[t][s]`, with integral monomial parameters. -/
theorem exists_list_commutator_terms [Finite J] [P.IsReduced] (h : X →+ ℤ) {α β : J}
    (hα : 0 < h (P.root α)) (hβ : 0 < h (P.root β))
    (hne : α ≠ β) (hopp : P.root α ≠ -P.root β) :
    ∃ T : List (CommutatorTerm P α β),
      T.Pairwise (fun p q => p.root ≠ q.root ∧ h (P.root p.root) ≤ h (P.root q.root)) ∧
      divExp (D.e α) s₀ * divExp (D.e β) t₀ * divExp (D.e α) (-s₀) * divExp (D.e β) (-t₀) =
        (T.map fun p => divExp (D.e p.root) (p.parameter s₀ t₀)).prod := by
  obtain ⟨L, hL, horder, heq⟩ := D.exists_list_commutator_int h hα hβ
  have hgraded := D.weightGraded_commutator α β
  rw [heq] at hgraded
  obtain ⟨T, rfl⟩ := D.exists_terms_of_weightGraded h hα hβ
    (rootCombination_injective hne hopp) L hL horder hgraded
  exact ⟨T, List.pairwise_map.mp horder, by simpa only [List.map_map, Function.comp_def] using heq⟩

end LieRootData

/-- An ordered integral list together with its universal matrix identity. -/
structure IntegralCommutator (D : LieRootData P) (α β : J) where
  height : X →+ ℤ
  height_pos_left : 0 < height (P.root α)
  height_pos_right : 0 < height (P.root β)
  terms : List (CommutatorTerm P α β)
  ordered : terms.Pairwise (fun p q => p.root ≠ q.root ∧
    height (P.root p.root) ≤ height (P.root q.root))
  matrix_identity :
    divExp (D.e α) s₀ * divExp (D.e β) t₀ * divExp (D.e α) (-s₀) * divExp (D.e β) (-t₀) =
      (terms.map fun p => divExp (D.e p.root) (p.parameter s₀ t₀)).prod

namespace IntegralCommutator

variable {D : LieRootData P} {α β : J}

/-- Evaluate the universal commutator identity in a commutative ring. -/
theorem specialize (E : IntegralCommutator D α β) {R : Type*} [CommRing R] (s t : R) :
    divExp (D.e α) s * divExp (D.e β) t * divExp (D.e α) (-s) * divExp (D.e β) (-t) =
      (E.terms.map fun p => divExp (D.e p.root) (p.parameter s t)).prod := by
  let φ : ℤ[X][X] →+* R := eval₂RingHom (eval₂RingHom (Int.castRingHom R) t) s
  have hs : φ s₀ = s := by simp [φ]
  have ht : φ t₀ = t := by simp [φ]
  have hdiv (r : J) (f : ℤ[X][X]) :
      φ.mapMatrix (divExp (D.e r) f) = divExp (D.e r) (φ f) :=
    divExp_map φ f
  simpa only [map_mul, map_list_prod, List.map_map, Function.comp_def, hdiv,
    CommutatorTerm.parameter, map_intCast, map_pow, map_neg, hs, ht] using
    congrArg (fun M => φ.mapMatrix M) E.matrix_identity

end IntegralCommutator

private theorem exists_positive_height [Finite J] [P.IsReduced] {α β : J}
    (hne : α ≠ β) (hopp : P.root α ≠ -P.root β) :
    ∃ h : X →+ ℤ, 0 < h (P.root α) ∧ 0 < h (P.root β) := by
  have : Module.IsReflexive ℤ X := .of_isPerfPair P.toLinearMap
  have hlt : P.coxeterWeightIn ℤ α β < 4 :=
    lt_of_le_of_ne (P.coxeterWeightIn_le_four ℤ α β) (P.coxeterWeightIn_ne_four ℤ hne hopp)
  have hc := P.algebraMap_coxeterWeightIn ℤ α β
  rw [Algebra.algebraMap_self, RingHom.id_apply, RootPairing.coxeterWeight] at hc
  rw [hc] at hlt
  let h : X →+ ℤ := (2 - P.pairing α β) • (P.toLinearMap.flip (P.coroot α)).toAddMonoidHom +
    (2 - P.pairing β α) • (P.toLinearMap.flip (P.coroot β)).toAddMonoidHom
  have hv (r : J) : h (P.root r) =
      (2 - P.pairing α β) * P.pairing r α + (2 - P.pairing β α) * P.pairing r β := by
    simp [h, RootPairing.root_coroot_eq_pairing]
  refine ⟨h, ?_, ?_⟩
  · rw [hv, RootPairing.pairing_same]
    linarith
  · rw [hv, RootPairing.pairing_same]
    linarith

namespace ChevalleyLieData

variable {b : P.Base} (D : ChevalleyLieData P b) [Finite J] [P.IsReduced]

/-- The field-independent ordered expansion for a nonopposite pair of roots. -/
def commutatorExpansion (α β : J) (hopp : P.root α ≠ -P.root β) :
    IntegralCommutator D.toLieRootData α β := by
  classical
  by_cases heq : α = β
  · subst β
    let h := (P.toLinearMap.flip (P.coroot α)).toAddMonoidHom
    have hpos : 0 < h (P.root α) := by
      change 0 < P.toLinearMap (P.root α) (P.coroot α)
      rw [P.root_coroot_two]
      norm_num
    refine ⟨h, hpos, hpos, [], List.Pairwise.nil, ?_⟩
    have hd := D.toLieRootData.isDividedPowerFamily α
    simp only [List.map_nil, List.prod_nil, divExp_mul hd]
    rw [show s₀ + t₀ + -s₀ + -t₀ = 0 by abel, divExp_zero hd]
  · have h := exists_positive_height heq hopp
    have hh := D.toLieRootData.exists_list_commutator_terms
      h.choose h.choose_spec.1 h.choose_spec.2 heq hopp
    exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, hh.choose, hh.choose_spec.1, hh.choose_spec.2⟩

@[simp]
theorem commutatorExpansion_same (α : J) (hopp : P.root α ≠ -P.root α) :
    (D.commutatorExpansion α α hopp).terms = [] := by
  simp [commutatorExpansion]

end ChevalleyLieData

end Langlands.GroupScheme.SplitExistence
