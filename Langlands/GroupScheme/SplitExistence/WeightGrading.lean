import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The weight grading of square matrices

Fix weights `wt : ι → X` of the basis vectors of `R^ι`, with values in an additive group `X`.
A square matrix `A` *maps weights by* `f : X → X` if every nonzero entry `A c d` has
`wt c = f (wt d)`, and it is *homogeneous of weight* `μ` if every nonzero entry `A c d` has
`wt c = wt d + μ`. Homogeneous matrices are closed under linear combinations, products add
weights, conjugation by weight-permuting matrices transports weights, and the diagonal matrix
of an additive character of the weights acts on a homogeneous matrix by a scalar under the
commutator. The projection `wtProj μ` keeps the entries of weight `μ`.
-/

noncomputable section

open Matrix

namespace Langlands.GroupScheme.SplitExistence

variable {ι X R : Type*} [AddCommGroup X] (wt : ι → X)

/-- The matrix `A` maps weights by `f`: every nonzero entry `A c d` has `wt c = f (wt d)`. -/
def MapsWt [Zero R] (f : X → X) (A : Matrix ι ι R) : Prop :=
  ∀ c d, A c d ≠ 0 → wt c = f (wt d)

/-- The matrix `A` is homogeneous of weight `μ`: every nonzero entry `A c d` has
`wt c = wt d + μ`. -/
def IsWtHom [Zero R] (μ : X) (A : Matrix ι ι R) : Prop :=
  ∀ c d, A c d ≠ 0 → wt c = wt d + μ

variable {wt}

section Basic

variable [Ring R]

omit [AddCommGroup X] in
theorem MapsWt.mul [Fintype ι] {f g : X → X} {A B : Matrix ι ι R} (hA : MapsWt wt f A)
    (hB : MapsWt wt g B) : MapsWt wt (f ∘ g) (A * B) := by
  intro c d h
  rw [mul_apply] at h
  obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [hA c m (left_ne_zero_of_mul hm), hB m d (right_ne_zero_of_mul hm)]
  rfl

omit [AddCommGroup X] in
theorem MapsWt.one [DecidableEq ι] : MapsWt wt id (1 : Matrix ι ι R) := by
  intro c d h
  by_cases hcd : c = d
  · rw [hcd]; rfl
  · exact absurd (one_apply_ne hcd) h

theorem IsWtHom.zero (μ : X) : IsWtHom wt μ (0 : Matrix ι ι R) :=
  fun _ _ h => absurd rfl h

theorem IsWtHom.add {μ : X} {A B : Matrix ι ι R} (hA : IsWtHom wt μ A) (hB : IsWtHom wt μ B) :
    IsWtHom wt μ (A + B) := by
  intro c d h
  rw [add_apply] at h
  by_cases hc : A c d = 0
  · rw [hc, zero_add] at h
    exact hB c d h
  · exact hA c d hc

theorem IsWtHom.neg {μ : X} {A : Matrix ι ι R} (hA : IsWtHom wt μ A) :
    IsWtHom wt μ (-A) := by
  intro c d h
  rw [neg_apply, neg_ne_zero] at h
  exact hA c d h

theorem IsWtHom.sub {μ : X} {A B : Matrix ι ι R} (hA : IsWtHom wt μ A) (hB : IsWtHom wt μ B) :
    IsWtHom wt μ (A - B) := by
  rw [sub_eq_add_neg]
  exact hA.add hB.neg

theorem IsWtHom.smul {S : Type*} [SMulZeroClass S R] {μ : X} {A : Matrix ι ι R}
    (hA : IsWtHom wt μ A) (s : S) : IsWtHom wt μ (s • A) := by
  intro c d h
  rw [smul_apply] at h
  by_cases hc : A c d = 0
  · rw [hc, smul_zero] at h
    exact absurd rfl h
  · exact hA c d hc

theorem IsWtHom.sum {κ : Type*} {s : Finset κ} {μ : X} {A : κ → Matrix ι ι R}
    (hA : ∀ k ∈ s, IsWtHom wt μ (A k)) : IsWtHom wt μ (∑ k ∈ s, A k) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact IsWtHom.zero μ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hA a (Finset.mem_insert_self a s)).add
      (ih fun k hk => hA k (Finset.mem_insert_of_mem hk))

theorem IsWtHom.mapsWt {μ : X} {A : Matrix ι ι R} (hA : IsWtHom wt μ A) :
    MapsWt wt (· + μ) A :=
  hA

theorem MapsWt.isWtHom {μ : X} {A : Matrix ι ι R} (hA : MapsWt wt (· + μ) A) :
    IsWtHom wt μ A :=
  hA

theorem IsWtHom.mul [Fintype ι] {μ ν : X} {A B : Matrix ι ι R} (hA : IsWtHom wt μ A)
    (hB : IsWtHom wt ν B) : IsWtHom wt (ν + μ) (A * B) := by
  intro c d h
  rw [hA.mapsWt.mul hB.mapsWt c d h]
  exact add_assoc _ _ _

theorem IsWtHom.mul' [Fintype ι] {μ ν : X} {A B : Matrix ι ι R} (hA : IsWtHom wt μ A)
    (hB : IsWtHom wt ν B) : IsWtHom wt (μ + ν) (A * B) := by
  rw [add_comm]
  exact hA.mul hB

theorem IsWtHom.commutator [Fintype ι] {μ ν : X} {A B : Matrix ι ι R} (hA : IsWtHom wt μ A)
    (hB : IsWtHom wt ν B) : IsWtHom wt (μ + ν) (A * B - B * A) :=
  (hA.mul' hB).sub (hB.mul hA)

/-- Conjugation by matrices mapping weights by mutually inverse additive maps transports the
weight of a homogeneous matrix. -/
theorem IsWtHom.conj [Fintype ι] {f : X →+ X} {f' : X → X} (hff' : ∀ x, f (f' x) = x)
    {g g' : Matrix ι ι R} (hg : MapsWt wt f g) (hg' : MapsWt wt f' g') {μ : X}
    {A : Matrix ι ι R} (hA : IsWtHom wt μ A) : IsWtHom wt (f μ) (g * A * g') := by
  intro c d h
  rw [(hg.mul hA.mapsWt).mul hg' c d h]
  simp only [Function.comp_apply, map_add, hff']

/-- A nonzero matrix has at most one weight. -/
theorem IsWtHom.eq_of_ne_zero {μ ν : X} {A : Matrix ι ι R} (hμ : IsWtHom wt μ A)
    (hν : IsWtHom wt ν A) (hA : A ≠ 0) : μ = ν := by
  obtain ⟨c, d, h⟩ : ∃ c d, A c d ≠ 0 := by
    by_contra! h'
    exact hA (Matrix.ext h')
  have h1 := hμ c d h
  rw [hν c d h] at h1
  exact (add_left_cancel h1).symm

theorem IsWtHom.map {S : Type*} [Ring S] {μ : X} {A : Matrix ι ι R} (hA : IsWtHom wt μ A)
    (φ : R →+* S) : IsWtHom wt μ (A.map φ) := by
  intro c d h
  refine hA c d fun h' => h ?_
  rw [map_apply, h', map_zero]

theorem IsWtHom.of_map {S : Type*} [Ring S] {μ : X} {A : Matrix ι ι R} {φ : R →+* S}
    (hφ : Function.Injective φ) (hA : IsWtHom wt μ (A.map φ)) : IsWtHom wt μ A := by
  intro c d h
  refine hA c d ?_
  rw [map_apply]
  exact (map_ne_zero_iff φ hφ).2 h

omit [AddCommGroup X] in
theorem MapsWt.map {S : Type*} [Ring S] {f : X → X} {A : Matrix ι ι R} (hA : MapsWt wt f A)
    (φ : R →+* S) : MapsWt wt f (A.map φ) := by
  intro c d h
  refine hA c d fun h' => h ?_
  rw [map_apply, h', map_zero]

omit [AddCommGroup X] in
theorem MapsWt.of_map {S : Type*} [Ring S] {f : X → X} {A : Matrix ι ι R} {φ : R →+* S}
    (hφ : Function.Injective φ) (hA : MapsWt wt f (A.map φ)) : MapsWt wt f A := by
  intro c d h
  refine hA c d ?_
  rw [map_apply]
  exact (map_ne_zero_iff φ hφ).2 h

/-- The commutator with the diagonal matrix of an additive character of the weights acts on a
homogeneous matrix of weight `μ` by the value of the character at `μ`. -/
theorem IsWtHom.diagonal_commutator {R : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {μ : X}
    {A : Matrix ι ι R}
    (hA : IsWtHom wt μ A) (χ : X →+ R) :
    diagonal (fun c => χ (wt c)) * A - A * diagonal (fun c => χ (wt c)) = χ μ • A := by
  ext c d
  rw [sub_apply, diagonal_mul, mul_diagonal, smul_apply, smul_eq_mul]
  by_cases h : A c d = 0
  · rw [h]; simp
  · rw [hA c d h, map_add]
    ring

end Basic

section Proj

variable [DecidableEq X] [Ring R]

variable (wt) in
/-- The component of weight `μ` of a matrix: the entries `(c, d)` with `wt c = wt d + μ`. -/
def wtProj (μ : X) : Matrix ι ι R →+ Matrix ι ι R where
  toFun A := of fun c d => if wt c = wt d + μ then A c d else 0
  map_zero' := by ext c d; simp
  map_add' A B := by ext c d; simp only [of_apply, add_apply]; split_ifs <;> simp

variable (wt) in
theorem wtProj_apply (μ : X) (A : Matrix ι ι R) (c d : ι) :
    wtProj wt μ A c d = if wt c = wt d + μ then A c d else 0 := rfl

variable (wt) in
theorem wtProj_smul {S : Type*} [SMulZeroClass S R] (μ : X) (s : S) (A : Matrix ι ι R) :
    wtProj wt μ (s • A) = s • wtProj wt μ A := by
  ext c d
  simp only [wtProj_apply, smul_apply]
  split_ifs <;> simp

variable (wt) in
theorem isWtHom_wtProj (μ : X) (A : Matrix ι ι R) : IsWtHom wt μ (wtProj wt μ A) := by
  intro c d h
  by_contra h'
  simp [wtProj_apply, h'] at h

theorem IsWtHom.wtProj_self {μ : X} {A : Matrix ι ι R} (hA : IsWtHom wt μ A) :
    wtProj wt μ A = A := by
  ext c d
  rw [wtProj_apply]
  split_ifs with h
  · rfl
  · by_contra h'
    exact h (hA c d fun e => h' e.symm)

theorem IsWtHom.wtProj_ne {μ ν : X} {A : Matrix ι ι R} (hA : IsWtHom wt ν A) (h : μ ≠ ν) :
    wtProj wt μ A = 0 := by
  ext c d
  rw [wtProj_apply, zero_apply]
  split_ifs with h'
  · by_contra h''
    exact h (add_left_cancel (h'.symm.trans (hA c d h'')))
  · rfl

end Proj

end Langlands.GroupScheme.SplitExistence
