import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Projective
import Mathlib.Tactic

/-! # A finite subset model for the Koszul differential -/

universe u v

namespace Langlands.CommutativeAlgebra

open scoped BigOperators

variable {R : Type u} [CommRing R]
variable {ι : Type v} [LinearOrder ι]

/-- The sign of adjoining a generator before the larger generators. -/
def koszulSign (R : Type u) [CommRing R] (s : Finset ι) (i : ι) : R :=
  (-1) ^ (s.filter (· < i)).card

lemma koszulSign_insert_of_lt (s : Finset ι) {i j : ι}
    (hi : i ∉ s) (hij : i < j) :
    koszulSign R (insert i s) j = -koszulSign R s j := by
  unfold koszulSign
  simp only [Finset.filter_insert, hij, ↓reduceIte]
  rw [Finset.card_insert_of_notMem (fun h ↦ hi (Finset.mem_filter.mp h).1), pow_succ]
  simp

lemma koszulSign_insert_of_not_lt (s : Finset ι) {i j : ι}
    (hij : ¬ i < j) :
    koszulSign R (insert i s) j = koszulSign R s j := by
  simp [koszulSign, Finset.filter_insert, hij]

/-- The coefficient for adjoining one index to a subset. -/
def koszulCoefficient (a : ι → R) (s : Finset ι) (i : ι) : R :=
  if i ∈ s then 0 else koszulSign R s i * a i

lemma koszulCoefficient_pair (a : ι → R) (s : Finset ι) (i j : ι) :
    koszulCoefficient a s i * koszulCoefficient a (insert i s) j +
      koszulCoefficient a s j * koszulCoefficient a (insert j s) i = 0 := by
  by_cases hi : i ∈ s
  · simp [koszulCoefficient, hi, Finset.mem_insert_of_mem hi]
  by_cases hj : j ∈ s
  · simp [koszulCoefficient, hj, Finset.mem_insert_of_mem hj]
  by_cases hij : i = j
  · subst j
    simp [koszulCoefficient]
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · simp only [koszulCoefficient, hi, hj, Finset.mem_insert, hij, Ne.symm hij,
      or_false, ↓reduceIte, koszulSign_insert_of_lt s hi hij',
      koszulSign_insert_of_not_lt s (not_lt_of_gt hij')]
    ring
  · simp only [koszulCoefficient, hi, hj, Finset.mem_insert, hij, Ne.symm hij,
      or_false, ↓reduceIte, koszulSign_insert_of_lt s hj hji',
      koszulSign_insert_of_not_lt s (not_lt_of_gt hji')]
    ring

variable [Fintype ι]

/-- The Koszul differential on the full space of subset coordinates. -/
noncomputable def koszulAmbientDifferential (a : ι → R) :
    (Finset ι → R) →ₗ[R] (Finset ι → R) where
  toFun x s := ∑ i, koszulCoefficient a s i * x (insert i s)
  map_add' x y := by
    ext s
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    ext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma koszulAmbientDifferential_sq (a : ι → R) :
    (koszulAmbientDifferential a).comp (koszulAmbientDifferential a) = 0 := by
  apply LinearMap.ext
  intro x
  funext s
  change (∑ i, koszulCoefficient a s i *
    ∑ j, koszulCoefficient a (insert i s) j * x (insert j (insert i s))) = 0
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [← Finset.sum_product']
  apply Finset.sum_involution (fun p _ ↦ Prod.swap p)
  · intro p _
    rcases p with ⟨i, j⟩
    dsimp
    rw [Finset.insert_comm j i s, ← add_mul, koszulCoefficient_pair, zero_mul]
  · intro p _ hp hfix
    have heq : p.1 = p.2 := congrArg Prod.snd hfix
    apply hp
    rcases p with ⟨i, j⟩
    dsimp at heq ⊢
    subst j
    simp [koszulCoefficient]
  · intro p _
    simp
  · intro p _
    exact Prod.swap_swap p

/-- The free module on subsets of the specified cardinality. -/
abbrev FiniteKoszulModule (R : Type u) (ι : Type v) (n : ℕ) :=
  {s : Finset ι // s.card = n} → R

/-- Extend a homogeneous coordinate vector by zero to all subset coordinates. -/
noncomputable def koszulExtend (n : ℕ) :
    FiniteKoszulModule R ι n →ₗ[R] (Finset ι → R) where
  toFun x s := if hs : s.card = n then x ⟨s, hs⟩ else 0
  map_add' x y := by
    ext s
    by_cases hs : s.card = n <;> simp [hs]
  map_smul' r x := by
    ext s
    by_cases hs : s.card = n <;> simp [hs]

/-- Restrict an ambient vector to one degree. -/
def koszulRestrict (n : ℕ) :
    (Finset ι → R) →ₗ[R] FiniteKoszulModule R ι n where
  toFun x s := x s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [LinearOrder ι] [Fintype ι] in
lemma koszulRestrict_extend (n : ℕ) (x : FiniteKoszulModule R ι n) :
    koszulRestrict n (koszulExtend n x) = x := by
  ext s
  simp [koszulRestrict, koszulExtend, s.property]

omit [LinearOrder ι] [Fintype ι] in
lemma koszulExtend_injective (n : ℕ) :
    Function.Injective (koszulExtend (R := R) (ι := ι) n) :=
  Function.LeftInverse.injective (koszulRestrict_extend n)

/-- The Koszul differential from degree `n+1` to degree `n`. -/
noncomputable def finiteKoszulDifferential (a : ι → R) (n : ℕ) :
    FiniteKoszulModule R ι (n + 1) →ₗ[R] FiniteKoszulModule R ι n :=
  (koszulRestrict n).comp ((koszulAmbientDifferential a).comp (koszulExtend (n + 1)))

lemma koszulExtend_differential (a : ι → R) (n : ℕ)
    (x : FiniteKoszulModule R ι (n + 1)) :
    koszulExtend n (finiteKoszulDifferential a n x) =
      koszulAmbientDifferential a (koszulExtend (n + 1) x) := by
  funext s
  by_cases hs : s.card = n
  · simp [koszulExtend, finiteKoszulDifferential, koszulRestrict, hs]
  · simp only [koszulExtend, LinearMap.coe_mk, AddHom.coe_mk, hs, ↓reduceDIte]
    symm
    change (∑ i, koszulCoefficient a s i *
      koszulExtend (n + 1) x (insert i s)) = 0
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ s
    · simp [koszulCoefficient, hi]
    · have hcard : (insert i s).card ≠ n + 1 := by
        rw [Finset.card_insert_of_notMem hi]
        omega
      simp [koszulExtend, hcard]

lemma finiteKoszulDifferential_sq (a : ι → R) (n : ℕ) :
    (finiteKoszulDifferential a n).comp (finiteKoszulDifferential a (n + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply koszulExtend_injective n
  change koszulExtend n (finiteKoszulDifferential a n
    (finiteKoszulDifferential a (n + 1) x)) = koszulExtend n 0
  rw [koszulExtend_differential, koszulExtend_differential, map_zero]
  exact LinearMap.congr_fun (koszulAmbientDifferential_sq a) _

end Langlands.CommutativeAlgebra
