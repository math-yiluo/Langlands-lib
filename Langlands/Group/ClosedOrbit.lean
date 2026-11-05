import Langlands.Algebra.CanonicalReynolds
import Langlands.Group.MinimalVector
import Langlands.Group.AlgebraicMatrixPowers
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.CharZero.Infinite

/-! # Closed orbits whose stabilizer is a prescribed matrix group -/

noncomputable section

universe u

namespace Langlands.Group.ClosedOrbit

open Matrix MvPolynomial
open Langlands.Algebra.CanonicalReynolds
open Langlands.GroupScheme.GeneralLinear (Coordinate values)
open scoped Kronecker

variable {𝕜 : Type u} [RCLike 𝕜] {n : Type} [Fintype n] [DecidableEq n]

section Coordinates

variable (n) in
/-- Coordinates for a pair of square matrices: the entries of the first and of the second. -/
abbrev Index : Type := (n × n) ⊕ (n × n)

/-- The first matrix of a coordinate vector. -/
def fst (z : Index n → 𝕜) : Matrix n n 𝕜 := Matrix.of fun i j => z (Sum.inl (i, j))

/-- The second matrix of a coordinate vector. -/
def snd (z : Index n → 𝕜) : Matrix n n 𝕜 := Matrix.of fun i j => z (Sum.inr (i, j))

omit [RCLike 𝕜] [Fintype n] [DecidableEq n] in
theorem ext_fst_snd {z z' : Index n → 𝕜} (h₁ : fst z = fst z') (h₂ : snd z = snd z') :
    z = z' := by
  funext κ
  rcases κ with ⟨i, j⟩ | ⟨i, j⟩
  · exact congrFun (congrFun h₁ i) j
  · exact congrFun (congrFun h₂ i) j

/-- The coordinate vector of an invertible matrix: its entries and those of its inverse. -/
def point (g : GL n 𝕜) : Index n → 𝕜 :=
  Sum.elim (fun p => (g : Matrix n n 𝕜) p.1 p.2) (fun p => ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜) p.1 p.2)

@[simp] theorem fst_point (g : GL n 𝕜) : fst (point g) = (g : Matrix n n 𝕜) := rfl

@[simp] theorem snd_point (g : GL n 𝕜) : snd (point g) = ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜) :=
  rfl

/-- The invertible matrix with coordinate vector `z`, when `fst z * snd z = 1`. -/
def unitOf (z : Index n → 𝕜) (hz : fst z * snd z = 1) : GL n 𝕜 :=
  ⟨fst z, snd z, hz, mul_eq_one_comm.2 hz⟩

theorem point_unitOf (z : Index n → 𝕜) (hz : fst z * snd z = 1) : point (unitOf z hz) = z :=
  ext_fst_snd rfl rfl

/-- Left translation `(X, Y) ↦ (g X, Y g⁻¹)` in coordinates. -/
def leftMatrix (g : GL n 𝕜) : Matrix (Index n) (Index n) 𝕜 :=
  fromBlocks ((g : Matrix n n 𝕜) ⊗ₖ (1 : Matrix n n 𝕜)) 0 0
    ((1 : Matrix n n 𝕜) ⊗ₖ ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜)ᵀ)

/-- Right translation `(X, Y) ↦ (X h, h⁻¹ Y)` in coordinates. -/
def rightMatrix (h : GL n 𝕜) : Matrix (Index n) (Index n) 𝕜 :=
  fromBlocks ((1 : Matrix n n 𝕜) ⊗ₖ (h : Matrix n n 𝕜)ᵀ) 0 0
    (((h⁻¹ : GL n 𝕜) : Matrix n n 𝕜) ⊗ₖ (1 : Matrix n n 𝕜))

theorem kronecker_one_mulVec_apply (A : Matrix n n 𝕜) (v : n × n → 𝕜) (i j : n) :
    ((A ⊗ₖ (1 : Matrix n n 𝕜)) *ᵥ v) (i, j) = ∑ k, A i k * v (k, j) := by
  simp [mulVec, dotProduct, Fintype.sum_prod_type, one_apply]

theorem one_kronecker_mulVec_apply (B : Matrix n n 𝕜) (v : n × n → 𝕜) (i j : n) :
    (((1 : Matrix n n 𝕜) ⊗ₖ B) *ᵥ v) (i, j) = ∑ l, B j l * v (i, l) := by
  simp [mulVec, dotProduct, Fintype.sum_prod_type, one_apply]

theorem fst_leftMatrix_mulVec (g : GL n 𝕜) (z : Index n → 𝕜) :
    fst (leftMatrix g *ᵥ z) = (g : Matrix n n 𝕜) * fst z := by
  ext i j
  simp [fst, leftMatrix, fromBlocks_mulVec, kronecker_one_mulVec_apply, mul_apply]

theorem snd_leftMatrix_mulVec (g : GL n 𝕜) (z : Index n → 𝕜) :
    snd (leftMatrix g *ᵥ z) = snd z * ((g⁻¹ : GL n 𝕜) : Matrix n n 𝕜) := by
  ext i j
  simp [snd, leftMatrix, fromBlocks_mulVec, one_kronecker_mulVec_apply, mul_apply, mul_comm]

theorem fst_rightMatrix_mulVec (h : GL n 𝕜) (z : Index n → 𝕜) :
    fst (rightMatrix h *ᵥ z) = fst z * (h : Matrix n n 𝕜) := by
  ext i j
  simp [fst, rightMatrix, fromBlocks_mulVec, one_kronecker_mulVec_apply, mul_apply, mul_comm]

theorem snd_rightMatrix_mulVec (h : GL n 𝕜) (z : Index n → 𝕜) :
    snd (rightMatrix h *ᵥ z) = ((h⁻¹ : GL n 𝕜) : Matrix n n 𝕜) * snd z := by
  ext i j
  simp [snd, rightMatrix, fromBlocks_mulVec, kronecker_one_mulVec_apply, mul_apply]

theorem leftMatrix_mulVec_point (g x : GL n 𝕜) : leftMatrix g *ᵥ point x = point (g * x) := by
  apply ext_fst_snd
  · rw [fst_leftMatrix_mulVec, fst_point, fst_point, Units.val_mul]
  · rw [snd_leftMatrix_mulVec, snd_point, snd_point, _root_.mul_inv_rev, Units.val_mul]

theorem rightMatrix_mulVec_point (h x : GL n 𝕜) : rightMatrix h *ᵥ point x = point (x * h) := by
  apply ext_fst_snd
  · rw [fst_rightMatrix_mulVec, fst_point, fst_point, Units.val_mul]
  · rw [snd_rightMatrix_mulVec, snd_point, snd_point, _root_.mul_inv_rev, Units.val_mul]

theorem leftMatrix_mulVec_mulVec (g g' : GL n 𝕜) (z : Index n → 𝕜) :
    leftMatrix g *ᵥ (leftMatrix g' *ᵥ z) = leftMatrix (g * g') *ᵥ z := by
  apply ext_fst_snd
  · rw [fst_leftMatrix_mulVec, fst_leftMatrix_mulVec, fst_leftMatrix_mulVec, Units.val_mul,
      Matrix.mul_assoc]
  · rw [snd_leftMatrix_mulVec, snd_leftMatrix_mulVec, snd_leftMatrix_mulVec, _root_.mul_inv_rev,
      Units.val_mul, Matrix.mul_assoc]

theorem rightMatrix_mulVec_mulVec (h h' : GL n 𝕜) (z : Index n → 𝕜) :
    rightMatrix h' *ᵥ (rightMatrix h *ᵥ z) = rightMatrix (h * h') *ᵥ z := by
  apply ext_fst_snd
  · rw [fst_rightMatrix_mulVec, fst_rightMatrix_mulVec, fst_rightMatrix_mulVec, Units.val_mul,
      Matrix.mul_assoc]
  · rw [snd_rightMatrix_mulVec, snd_rightMatrix_mulVec, snd_rightMatrix_mulVec, _root_.mul_inv_rev,
      Units.val_mul, Matrix.mul_assoc]

theorem rightMatrix_one_mulVec (z : Index n → 𝕜) : rightMatrix 1 *ᵥ z = z := by
  apply ext_fst_snd
  · rw [fst_rightMatrix_mulVec, Units.val_one, Matrix.mul_one]
  · rw [snd_rightMatrix_mulVec, inv_one, Units.val_one, Matrix.one_mul]

theorem leftMatrix_rightMatrix_comm (g h : GL n 𝕜) (z : Index n → 𝕜) :
    leftMatrix g *ᵥ (rightMatrix h *ᵥ z) = rightMatrix h *ᵥ (leftMatrix g *ᵥ z) := by
  apply ext_fst_snd
  · rw [fst_leftMatrix_mulVec, fst_rightMatrix_mulVec, fst_rightMatrix_mulVec,
      fst_leftMatrix_mulVec, Matrix.mul_assoc]
  · rw [snd_leftMatrix_mulVec, snd_rightMatrix_mulVec, snd_rightMatrix_mulVec,
      snd_leftMatrix_mulVec, Matrix.mul_assoc]

theorem leftMatrix_mul (g g' : GL n 𝕜) : leftMatrix (g * g') = leftMatrix g * leftMatrix g' :=
  Matrix.ext_iff_mulVec.2 fun z => by rw [← mulVec_mulVec, leftMatrix_mulVec_mulVec]

theorem leftMatrix_one : leftMatrix (1 : GL n 𝕜) = 1 :=
  Matrix.ext_iff_mulVec.2 fun z => by
    rw [one_mulVec]
    apply ext_fst_snd
    · rw [fst_leftMatrix_mulVec, Units.val_one, Matrix.one_mul]
    · rw [snd_leftMatrix_mulVec, inv_one, Units.val_one, Matrix.mul_one]

theorem conjTranspose_leftMatrix (g : GL n 𝕜) : (leftMatrix g)ᴴ = leftMatrix (star g) := by
  rw [leftMatrix, leftMatrix, fromBlocks_conjTranspose, conjTranspose_kronecker,
    conjTranspose_kronecker, conjTranspose_one, conjTranspose_zero, ← star_inv, Units.coe_star,
    Units.coe_star, star_eq_conjTranspose, star_eq_conjTranspose,
    conjTranspose_transpose_eq_transpose_conjTranspose]

/-- The coordinate indices of the entries and inverse entries of a matrix. -/
def coordinateIndex : Coordinate n → Index n
  | .entry i j => Sum.inl (i, j)
  | .inverseEntry i j => Sum.inr (i, j)

theorem point_comp_coordinateIndex (g : GL n 𝕜) : point g ∘ coordinateIndex = values g := by
  funext κ
  cases κ <;> rfl

theorem eval_rename_point (g : GL n 𝕜) (p : MvPolynomial (Coordinate n) 𝕜) :
    eval (point g) (rename coordinateIndex p) = eval (values g) p := by
  rw [eval_rename, point_comp_coordinateIndex]

end Coordinates

section Polynomials

/-- Substitution of the rows of `M` as linear forms. -/
def subst (M : Matrix (Index n) (Index n) 𝕜) :
    MvPolynomial (Index n) 𝕜 →ₐ[𝕜] MvPolynomial (Index n) 𝕜 :=
  bind₁ fun i => ∑ j, M i j • X j

theorem eval_bind₁_eq {σ τ : Type*} (z : τ → 𝕜) (g : σ → MvPolynomial τ 𝕜)
    (p : MvPolynomial σ 𝕜) : eval z (bind₁ g p) = eval (fun i => eval z (g i)) p :=
  eval₂Hom_bind₁ (RingHom.id 𝕜) z g p

omit [DecidableEq n] in
theorem eval_subst (M : Matrix (Index n) (Index n) 𝕜) (z : Index n → 𝕜)
    (p : MvPolynomial (Index n) 𝕜) : eval z (subst M p) = eval (M *ᵥ z) p := by
  have hf : (fun i => eval z (∑ j, M i j • X j)) = M *ᵥ z :=
    funext fun i => by simp [mulVec, dotProduct]
  rw [subst, eval_bind₁_eq, hf]

variable (n 𝕜) in
/-- Right translation of polynomial functions on pairs of matrices:
`(h • p)(X, Y) = p(X h, h⁻¹ Y)`. -/
def rightRep : Representation 𝕜 (GL n 𝕜) (MvPolynomial (Index n) 𝕜) where
  toFun h := (subst (rightMatrix h)).toLinearMap
  map_one' := LinearMap.ext fun p => MvPolynomial.funext fun z => by
    simp [eval_subst, rightMatrix_one_mulVec]
  map_mul' h h' := LinearMap.ext fun p => MvPolynomial.funext fun z => by
    simp only [AlgHom.toLinearMap_apply, Module.End.mul_apply, eval_subst]
    rw [rightMatrix_mulVec_mulVec]

theorem rightRep_apply (h : GL n 𝕜) (p : MvPolynomial (Index n) 𝕜) :
    rightRep 𝕜 n h p = subst (rightMatrix h) p :=
  rfl

/-- Right translation restricted to a subgroup. -/
abbrev subgroupRep (H : Subgroup (GL n 𝕜)) :
    Representation 𝕜 H (MvPolynomial (Index n) 𝕜) :=
  (rightRep 𝕜 n).comp H.subtype

theorem subgroupRep_apply (H : Subgroup (GL n 𝕜)) (h : H) (p : MvPolynomial (Index n) 𝕜) :
    subgroupRep H h p = subst (rightMatrix (h : GL n 𝕜)) p :=
  rfl

theorem isMultiplicative_subgroupRep (H : Subgroup (GL n 𝕜)) :
    IsMultiplicative (subgroupRep H) where
  map_one h := map_one (subst (rightMatrix (h : GL n 𝕜)))
  map_mul h a b := map_mul (subst (rightMatrix (h : GL n 𝕜))) a b

theorem eval_point_mul_of_mem_invariants (H : Subgroup (GL n 𝕜)) {f : MvPolynomial (Index n) 𝕜}
    (hf : f ∈ (subgroupRep H).invariants) (x : GL n 𝕜) {h : GL n 𝕜} (hh : h ∈ H) :
    eval (point (x * h)) f = eval (point x) f := by
  rw [← rightMatrix_mulVec_point, ← eval_subst, ← subgroupRep_apply H ⟨h, hh⟩,
    apply_of_mem_invariants hf]

theorem subst_leftMatrix_subgroupRep (H : Subgroup (GL n 𝕜)) (g : GL n 𝕜) (h : H)
    (p : MvPolynomial (Index n) 𝕜) :
    subst (leftMatrix g) (subgroupRep H h p) = subgroupRep H h (subst (leftMatrix g) p) :=
  MvPolynomial.funext fun z => by
    simp only [subgroupRep_apply, eval_subst, leftMatrix_rightMatrix_comm]

theorem isStable_homogeneousSubmodule (H : Subgroup (GL n 𝕜)) (d : ℕ) :
    IsStable (subgroupRep H) (homogeneousSubmodule (Index n) 𝕜 d) := by
  intro h p hp
  rw [mem_homogeneousSubmodule] at hp ⊢
  have hlin : ∀ i : Index n, (∑ j, rightMatrix (h : GL n 𝕜) i j • X j :
      MvPolynomial (Index n) 𝕜).IsHomogeneous 1 := fun i =>
    (mem_homogeneousSubmodule _ _).1 (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X _ _)))
  have key := hp.aeval (fun i => ∑ j, rightMatrix (h : GL n 𝕜) i j • X j) hlin
  rw [one_mul] at key
  change (bind₁ (fun i => ∑ j, rightMatrix (h : GL n 𝕜) i j • X j) p).IsHomogeneous d
  rwa [← aeval_eq_bind₁]

/-- The polynomial `(X Y - 1)ᵢⱼ`. -/
def relation (i j : n) : MvPolynomial (Index n) 𝕜 :=
  ∑ k, X (Sum.inl (i, k)) * X (Sum.inr (k, j)) - C ((1 : Matrix n n 𝕜) i j)

theorem eval_relation (z : Index n → 𝕜) (i j : n) :
    eval z (relation i j) = (fst z * snd z - 1) i j := by
  simp [relation, mul_apply, fst, snd]

theorem eval_relation_point (g : GL n 𝕜) (i j : n) : eval (point g) (relation i j) = 0 := by
  rw [eval_relation, fst_point, snd_point, Units.mul_inv, sub_self, Matrix.zero_apply]

theorem relation_mem_invariants (H : Subgroup (GL n 𝕜)) (i j : n) :
    relation i j ∈ (subgroupRep H).invariants := by
  refine (Representation.mem_invariants _ _).2 fun h => MvPolynomial.funext fun z => ?_
  rw [subgroupRep_apply, eval_subst, eval_relation, eval_relation, fst_rightMatrix_mulVec,
    snd_rightMatrix_mulVec, Matrix.mul_assoc, ← Matrix.mul_assoc ((h : GL n 𝕜) : Matrix n n 𝕜),
    Units.mul_inv, Matrix.one_mul]

end Polynomials

section Words

/-- The variables, together with the constant `1` for the padding letter. -/
def letter : Index n ⊕ Unit → MvPolynomial (Index n) 𝕜 := Sum.elim X 1

variable (n) in
/-- Words of length `D` in the coordinates and one padding letter. -/
abbrev Word (D : ℕ) : Type := Fin D → Index n ⊕ Unit

/-- The monomial spelled by a padded word. -/
def wordMonomial {D : ℕ} (e : Word n D) : MvPolynomial (Index n) 𝕜 := ∏ k, letter (e k)

theorem exists_wordMonomial_eq (D : ℕ) (α : Index n →₀ ℕ) (hα : α.degree ≤ D) :
    ∃ e : Word n D, wordMonomial (𝕜 := 𝕜) e = monomial α 1 := by
  induction D generalizing α with
  | zero =>
    have hα0 : α = 0 := (Finsupp.degree_eq_zero_iff α).1 (Nat.le_zero.1 hα)
    exact ⟨Fin.elim0, by simp [wordMonomial, hα0]⟩
  | succ D ih =>
    by_cases hα0 : α = 0
    · exact ⟨fun _ => Sum.inr (), by simp [wordMonomial, letter, hα0]⟩
    · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra hne
        push Not at hne
        exact hα0 (Finsupp.ext hne)
      have hle : Finsupp.single i 1 ≤ α := by
        rw [Finsupp.single_le_iff]
        omega
      have hsplit : α = Finsupp.single i 1 + (α - Finsupp.single i 1) :=
        (add_tsub_cancel_of_le hle).symm
      have hdeg : (α - Finsupp.single i 1).degree ≤ D := by
        have h := congrArg Finsupp.degree hsplit
        rw [map_add, Finsupp.degree_single] at h
        omega
      obtain ⟨e, he⟩ := ih _ hdeg
      refine ⟨Fin.cons (Sum.inl i) e, ?_⟩
      rw [wordMonomial, Fin.prod_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [← wordMonomial, he]
      simp only [letter, Sum.elim_inl]
      conv_rhs => rw [hsplit]
      rw [X, monomial_mul_monomial, one_mul]

theorem mem_span_wordMonomial {D : ℕ} {p : MvPolynomial (Index n) 𝕜} (hp : p.totalDegree ≤ D) :
    p ∈ Submodule.span 𝕜 (Set.range (wordMonomial (𝕜 := 𝕜) (n := n) (D := D))) := by
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  obtain ⟨e, he⟩ := exists_wordMonomial_eq (𝕜 := 𝕜) D α ((le_totalDegree hα).trans hp)
  have : monomial α (p.coeff α) = p.coeff α • monomial α (1 : 𝕜) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, ← he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)

/-- Left translation extended by the identity on the padding letter. -/
def extendedMatrix (g : GL n 𝕜) : Matrix (Index n ⊕ Unit) (Index n ⊕ Unit) 𝕜 :=
  fromBlocks (leftMatrix g) 0 0 1

/-- The Kronecker power of a square matrix on words of length `D`. -/
def kroneckerPower {ι : Type*} (D : ℕ) (M : Matrix ι ι 𝕜) : Matrix (Fin D → ι) (Fin D → ι) 𝕜 :=
  Matrix.of fun e e' => ∏ k, M (e k) (e' k)

theorem kroneckerPower_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ℕ)
    (M N : Matrix ι ι 𝕜) :
    kroneckerPower D (M * N) = kroneckerPower D M * kroneckerPower D N := by
  ext e e'
  simp only [kroneckerPower, of_apply, mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun x _ => Finset.prod_mul_distrib

theorem kroneckerPower_one {ι : Type*} [DecidableEq ι] (D : ℕ) :
    kroneckerPower D (1 : Matrix ι ι 𝕜) = 1 := by
  ext e e'
  simp only [kroneckerPower, of_apply, one_apply]
  by_cases h : e = e'
  · subst h
    simp
  · simp only [h, ite_false]
    obtain ⟨k, hk⟩ := Function.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

theorem conjTranspose_kroneckerPower {ι : Type*} (D : ℕ) (M : Matrix ι ι 𝕜) :
    (kroneckerPower D M)ᴴ = kroneckerPower D Mᴴ := by
  ext e e'
  simp [kroneckerPower, conjTranspose_apply, star_prod]

theorem extendedMatrix_mul (g g' : GL n 𝕜) :
    extendedMatrix (g * g') = extendedMatrix g * extendedMatrix g' := by
  simp [extendedMatrix, fromBlocks_multiply, leftMatrix_mul]

theorem extendedMatrix_one : extendedMatrix (1 : GL n 𝕜) = 1 := by
  rw [extendedMatrix, leftMatrix_one, fromBlocks_one]

theorem extendedMatrix_star (g : GL n 𝕜) : extendedMatrix (star g) = (extendedMatrix g)ᴴ := by
  simp [extendedMatrix, fromBlocks_conjTranspose, conjTranspose_leftMatrix]

variable (n 𝕜) in
/-- The `D`th Kronecker power of padded left translation. -/
def tensorHom (D : ℕ) : GL n 𝕜 →* Matrix (Word n D) (Word n D) 𝕜 where
  toFun g := kroneckerPower D (extendedMatrix g)
  map_one' := by rw [extendedMatrix_one, kroneckerPower_one]
  map_mul' g g' := by rw [extendedMatrix_mul, kroneckerPower_mul]

variable (n 𝕜) in
/-- The `D`th Kronecker power of padded left translation, as invertible matrices. -/
def tensorRep (D : ℕ) : GL n 𝕜 →* GL (Word n D) 𝕜 :=
  (tensorHom 𝕜 n D).toHomUnits

theorem coe_tensorRep (D : ℕ) (g : GL n 𝕜) :
    ((tensorRep 𝕜 n D g : GL (Word n D) 𝕜) : Matrix (Word n D) (Word n D) 𝕜) =
      kroneckerPower D (extendedMatrix g) :=
  rfl

/-- The tensor-power representation is compatible with conjugate transpose. -/
theorem tensorRep_star (D : ℕ) (g : GL n 𝕜) :
    tensorRep 𝕜 n D (star g) = star (tensorRep 𝕜 n D g) := by
  ext : 1
  rw [Units.coe_star, coe_tensorRep, coe_tensorRep, star_eq_conjTranspose,
    conjTranspose_kroneckerPower, extendedMatrix_star]

theorem subst_letter (g : GL n 𝕜) (j : Index n ⊕ Unit) :
    subst (leftMatrix g) (letter j) = ∑ j', extendedMatrix g j j' • letter j' := by
  rcases j with i | u
  · simp [letter, subst, extendedMatrix, Fintype.sum_sum_type]
  · simp [letter, extendedMatrix, Fintype.sum_sum_type]

theorem subst_wordMonomial {D : ℕ} (g : GL n 𝕜) (e : Word n D) :
    subst (leftMatrix g) (wordMonomial e) = ∑ e', tensorHom 𝕜 n D g e e' • wordMonomial e' := by
  rw [wordMonomial, map_prod]
  simp_rw [subst_letter]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun e' _ => ?_
  simp only [smul_eq_C_mul, Finset.prod_mul_distrib, ← map_prod C]
  rfl

end Words

section Orbit

variable (H : Subgroup (GL n 𝕜)) [Representation.IsSemisimpleRepresentation (subgroupRep H)]

/-- The Reynolds images of the padded word monomials. -/
def generator {D : ℕ} (e : Word n D) : MvPolynomial (Index n) 𝕜 :=
  reynolds (subgroupRep H) (wordMonomial e)

theorem generator_mem_invariants {D : ℕ} (e : Word n D) :
    generator H e ∈ (subgroupRep H).invariants :=
  reynolds_mem_invariants _

/-- For large word length the generators generate the invariant subalgebra (Hilbert). -/
theorem exists_adjoin_generator_eq :
    ∃ D : ℕ, Algebra.adjoin 𝕜 (Set.range (generator H (D := D))) =
      invariantSubalgebra (isMultiplicative_subgroupRep H) := by
  let _ : GradedAlgebra (homogeneousSubmodule (Index n) 𝕜) := MvPolynomial.gradedAlgebra
  obtain ⟨T, hT⟩ := invariantSubalgebra_fg (homogeneousSubmodule (Index n) 𝕜)
    (isMultiplicative_subgroupRep H) (isStable_homogeneousSubmodule H) fun a ha => by
      rw [homogeneousSubmodule_zero, Submodule.mem_one] at ha
      exact ha
  refine ⟨T.sup totalDegree, le_antisymm ?_ ?_⟩
  · exact Algebra.adjoin_le (by rintro _ ⟨e, rfl⟩; exact generator_mem_invariants H e)
  · rw [← hT]
    refine Algebra.adjoin_le fun t ht => ?_
    have htinv : t ∈ (subgroupRep H).invariants := by
      have h := Algebra.subset_adjoin (R := 𝕜) ht
      rw [hT] at h
      exact h
    have hspan := mem_span_wordMonomial (𝕜 := 𝕜) (n := n) (Finset.le_sup (f := totalDegree) ht)
    have hmap := Submodule.mem_map_of_mem (f := reynolds (subgroupRep H)) hspan
    rw [Submodule.map_span, ← Set.range_comp, reynolds_of_mem_invariants htinv] at hmap
    exact Algebra.span_le_adjoin 𝕜 _ hmap

variable {H} in
/-- The values of the generators at the coordinate vector of `g`. -/
def orbitPoint (D : ℕ) (g : GL n 𝕜) : Word n D → 𝕜 := fun e => eval (point g) (generator H e)

theorem tensorHom_mulVec_orbitPoint (D : ℕ) (g x : GL n 𝕜) :
    tensorHom 𝕜 n D g *ᵥ orbitPoint (H := H) D x = orbitPoint (H := H) D (g * x) := by
  funext e
  have key : subst (leftMatrix g) (generator H e) =
      ∑ e', tensorHom 𝕜 n D g e e' • generator H e' := by
    have := map_reynolds (ρ := subgroupRep H) (σ := subgroupRep H)
      (subst (leftMatrix g)).toLinearMap
      (fun h v => subst_leftMatrix_subgroupRep H g h v) (wordMonomial e)
    simp only [AlgHom.toLinearMap_apply] at this
    rw [generator, this, subst_wordMonomial, map_sum]
    simp only [map_smul, generator]
  simp only [orbitPoint]
  rw [← leftMatrix_mulVec_point, ← eval_subst, key, map_sum]
  simp [mulVec, dotProduct, smul_eval, orbitPoint]

theorem act_tensorRep (D : ℕ) (g : GL n 𝕜) :
    MinimalVector.act (tensorRep 𝕜 n D) g (WithLp.toLp 2 (orbitPoint (H := H) D 1)) =
      WithLp.toLp 2 (orbitPoint (H := H) D g) := by
  unfold MinimalVector.act
  rw [coe_tensorRep, toEuclideanCLM_toLp]
  change WithLp.toLp 2 (tensorHom 𝕜 n D g *ᵥ _) = _
  rw [tensorHom_mulVec_orbitPoint, mul_one]

/-- Invariant polynomials take equal values at the coordinate vectors of `g` and of `1` only
when `g` lies in the polynomially defined group `H`. -/
theorem mem_of_forall_eval_eq [IsAlgClosed 𝕜] (hH : AlgebraicMatrixPowers.IsPolynomiallyDefined H)
    {g : GL n 𝕜}
    (hg : ∀ f ∈ (subgroupRep H).invariants, eval (point g) f = eval (point 1) f) : g ∈ H := by
  obtain ⟨S, hS⟩ := hH
  by_contra hgH
  let I : GL n 𝕜 → Ideal (MvPolynomial (Index n) 𝕜) := fun x =>
    vanishingIdeal 𝕜 ((fun h => point (x * h)) '' (H : Set (GL n 𝕜)))
  have hI : ∀ x p, p ∈ I x ↔ ∀ h ∈ H, eval (point (x * h)) p = 0 := fun x p => by
    simp [I, mem_vanishingIdeal_iff]
  have hstable : ∀ x, IsStable (subgroupRep H) ((I x).restrictScalars 𝕜) := by
    intro x h p hp
    simp only [Submodule.restrictScalars_mem] at hp ⊢
    refine (hI x _).2 fun h' hh' => ?_
    rw [subgroupRep_apply, eval_subst, rightMatrix_mulVec_point, mul_assoc]
    exact (hI x p).1 hp _ (H.mul_mem hh' h.2)
  have hrel : ∀ x i j, relation i j ∈ I x := fun x i j =>
    (hI x _).2 fun h _ => eval_relation_point _ i j
  have hcomax : I 1 ⊔ I g = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨z, rfl⟩ := eq_vanishingIdeal_singleton_of_isMaximal 𝕜 hM
    have h0 : ∀ p ∈ I 1, eval z p = 0 := fun p hp =>
      (mem_vanishingIdeal_singleton_iff z p).1 (hle (Ideal.mem_sup_left hp))
    have h1 : ∀ p ∈ I g, eval z p = 0 := fun p hp =>
      (mem_vanishingIdeal_singleton_iff z p).1 (hle (Ideal.mem_sup_right hp))
    have hz : fst z * snd z = 1 := by
      ext i j
      have := h0 _ (hrel 1 i j)
      rwa [eval_relation, Matrix.sub_apply, sub_eq_zero] at this
    have hza : z = point (unitOf z hz) := (point_unitOf z hz).symm
    set a := unitOf z hz
    have haH : a ∈ H := (hS a).2 fun p hp => by
      have hmem : rename coordinateIndex p ∈ I 1 := (hI 1 _).2 fun h hh => by
        rw [one_mul, eval_rename_point]
        exact (hS h).1 hh p hp
      have := h0 _ hmem
      rwa [hza, eval_rename_point] at this
    have hgaH : g⁻¹ * a ∈ H := (hS _).2 fun p hp => by
      have hmem : subst (leftMatrix g⁻¹) (rename coordinateIndex p) ∈ I g :=
        (hI g _).2 fun h hh => by
          rw [eval_subst, leftMatrix_mulVec_point, inv_mul_cancel_left, eval_rename_point]
          exact (hS h).1 hh p hp
      have := h1 _ hmem
      rwa [hza, eval_subst, leftMatrix_mulVec_point, eval_rename_point] at this
    exact hgH (by simpa using H.mul_mem haH (H.inv_mem hgaH))
  obtain ⟨f, hf, hf0, hf1⟩ := exists_invariant_mem_sub_one_mem (isMultiplicative_subgroupRep H)
    (hstable 1) (hstable g) hcomax
  have e0 : eval (point 1) f = 0 := by
    simpa using (hI 1 f).1 hf0 1 H.one_mem
  have e1 : eval (point g) f = 1 := by
    have := (hI g _).1 hf1 1 H.one_mem
    rwa [mul_one, map_sub, map_one, sub_eq_zero] at this
  have := hg f hf
  rw [e0, e1] at this
  exact one_ne_zero this

/-- The stabilizer of the orbit vector is exactly `H`. -/
theorem stabilizer_tensorRep [IsAlgClosed 𝕜] (hH : AlgebraicMatrixPowers.IsPolynomiallyDefined H)
    {D : ℕ} (hD : Algebra.adjoin 𝕜 (Set.range (generator H (D := D))) =
      invariantSubalgebra (isMultiplicative_subgroupRep H)) :
    MinimalVector.stabilizer (tensorRep 𝕜 n D) (WithLp.toLp 2 (orbitPoint (H := H) D 1)) =
      H := by
  ext g
  rw [MinimalVector.mem_stabilizer_iff, act_tensorRep]
  constructor
  · intro hg
    have hg' : orbitPoint (H := H) D g = orbitPoint D 1 := congrArg WithLp.ofLp hg
    refine mem_of_forall_eval_eq H hH fun f hf => ?_
    have hle : Algebra.adjoin 𝕜 (Set.range (generator H (D := D))) ≤
        AlgHom.equalizer (aeval (point g)) (aeval (point 1)) :=
      Algebra.adjoin_le (by rintro _ ⟨e, rfl⟩; exact congrFun hg' e)
    have hf' : f ∈ Algebra.adjoin 𝕜 (Set.range (generator H (D := D))) := by
      rw [hD]
      exact hf
    simpa using hle hf'
  · intro hg
    congr 1
    funext e
    simpa [orbitPoint] using
      eval_point_mul_of_mem_invariants H (generator_mem_invariants H e) 1 hg

/-- The orbit of the generator values is Zariski closed: it is the common zero set of all
polynomial relations which vanish on it. -/
theorem range_orbitPoint_eq [IsAlgClosed 𝕜] {D : ℕ}
    (hD : Algebra.adjoin 𝕜 (Set.range (generator H (D := D))) =
      invariantSubalgebra (isMultiplicative_subgroupRep H)) :
    Set.range (orbitPoint (H := H) D) =
      {x | ∀ R : MvPolynomial (Word n D) 𝕜,
        (∀ g, eval (orbitPoint (H := H) D g) R = 0) → eval x R = 0} := by
  refine Set.Subset.antisymm (by rintro _ ⟨g, rfl⟩ R hR; exact hR g) fun x hx => ?_
  simp only [Set.mem_ofPred_eq] at hx
  set A := invariantSubalgebra (isMultiplicative_subgroupRep H)
  have hrange : ∀ f, f ∈ A ↔ ∃ R, aeval (generator H (D := D)) R = f := fun f => by
    rw [← hD, Algebra.adjoin_range_eq_range_aeval]
    rfl
  let Φ : MvPolynomial (Word n D) 𝕜 →ₐ[𝕜] A :=
    (aeval (generator H (D := D))).codRestrict A fun R => (hrange _).2 ⟨R, rfl⟩
  have hΦ : Function.Surjective Φ := by
    rintro ⟨f, hf⟩
    obtain ⟨R, rfl⟩ := (hrange f).1 hf
    exact ⟨R, rfl⟩
  have heval : ∀ g R, eval (orbitPoint (H := H) D g) R =
      eval (point g) (aeval (generator H (D := D)) R) := fun g R => by
    rw [aeval_eq_bind₁, eval_bind₁_eq]
    rfl
  have hker : ∀ R ∈ RingHom.ker Φ, aeval x R = 0 := by
    intro R hR
    have h0 : aeval (generator H (D := D)) R = 0 := congrArg Subtype.val hR
    rw [aeval_eq_eval]
    exact hx R fun g => by rw [heval, h0, map_zero]
  let χ : A →ₐ[𝕜] 𝕜 := (Ideal.Quotient.liftₐ (RingHom.ker Φ) (aeval x) hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hΦ).symm.toAlgHom
  have hχ : ∀ R, χ (Φ R) = eval x R := fun R => by
    simp [χ, Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
  obtain ⟨ψ, hψ⟩ := exists_algHom_comp_val_eq (isMultiplicative_subgroupRep H) χ
  set z : Index n → 𝕜 := fun i => ψ (X i)
  have hψz : ∀ p, ψ p = eval z p := by
    have : ψ = aeval z := MvPolynomial.algHom_ext fun i => by simp [z]
    intro p
    rw [this, aeval_eq_eval]
  have hψA : ∀ R, eval z (aeval (generator H (D := D)) R) = eval x R := fun R => by
    rw [← hψz, ← hχ, ← hψ]
    rfl
  have hz : fst z * snd z = 1 := by
    ext i j
    obtain ⟨R, hR⟩ := (hrange _).1 (relation_mem_invariants H i j)
    have h0 : eval x R = 0 := hx R fun g => by rw [heval, hR, eval_relation_point]
    rw [← hψA, hR, eval_relation, Matrix.sub_apply, sub_eq_zero] at h0
    exact h0
  refine ⟨unitOf z hz, funext fun e => ?_⟩
  simp only [orbitPoint, point_unitOf]
  have := hψA (X e)
  rwa [aeval_X, eval_X] at this

theorem isClosed_range_act [IsAlgClosed 𝕜] {D : ℕ}
    (hD : Algebra.adjoin 𝕜 (Set.range (generator H (D := D))) =
      invariantSubalgebra (isMultiplicative_subgroupRep H)) :
    IsClosed (Set.range fun g : GL n 𝕜 =>
      MinimalVector.act (tensorRep 𝕜 n D) g (WithLp.toLp 2 (orbitPoint (H := H) D 1))) := by
  have hclosed : IsClosed (Set.range (orbitPoint (H := H) D)) := by
    rw [range_orbitPoint_eq H hD]
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun R => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval R) continuous_const
  have hrange : (Set.range fun g : GL n 𝕜 =>
      MinimalVector.act (tensorRep 𝕜 n D) g (WithLp.toLp 2 (orbitPoint (H := H) D 1))) =
      WithLp.ofLp ⁻¹' Set.range (orbitPoint (H := H) D) := by
    ext v
    simp only [Set.mem_range, Set.mem_preimage, act_tensorRep]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, by rw [hg]⟩
  rw [hrange]
  exact hclosed.preimage (PiLp.continuous_ofLp 2 _)

end Orbit

/-- **Closed orbits with prescribed stabilizer.** Over an algebraically closed `RCLike` field, a
polynomially defined matrix group whose right translation on polynomial functions of a matrix
and its inverse is semisimple is the stabilizer of a vector with closed orbit, in a
representation compatible with conjugate transpose. -/
theorem exists_closed_orbit_stabilizer_eq [IsAlgClosed 𝕜] (H : Subgroup (GL n 𝕜))
    (hH : AlgebraicMatrixPowers.IsPolynomiallyDefined H)
    [Representation.IsSemisimpleRepresentation (subgroupRep H)] :
    ∃ (m : Type) (_ : Fintype m) (_ : DecidableEq m) (π : GL n 𝕜 →* GL m 𝕜)
      (w : EuclideanSpace 𝕜 m), (∀ g, π (star g) = star (π g)) ∧
      IsClosed (Set.range fun g => MinimalVector.act π g w) ∧
      MinimalVector.stabilizer π w = H := by
  obtain ⟨D, hD⟩ := exists_adjoin_generator_eq H
  exact ⟨Word n D, inferInstance, inferInstance, tensorRep 𝕜 n D,
    WithLp.toLp 2 (orbitPoint (H := H) D 1), tensorRep_star D, isClosed_range_act H hD,
    stabilizer_tensorRep H hH hD⟩

/-- Such a group has a conjugate which is stable under conjugate transpose. -/
theorem exists_conj_star_mem [IsAlgClosed 𝕜] (H : Subgroup (GL n 𝕜))
    (hH : AlgebraicMatrixPowers.IsPolynomiallyDefined H)
    [Representation.IsSemisimpleRepresentation (subgroupRep H)] :
    ∃ x : GL n 𝕜, ∀ g : GL n 𝕜, x⁻¹ * g * x ∈ H → x⁻¹ * star g * x ∈ H := by
  obtain ⟨m, _, _, π, w, hπ, hclosed, hstab⟩ := exists_closed_orbit_stabilizer_eq H hH
  obtain ⟨x, hx⟩ := MinimalVector.exists_conj_star_mem_stabilizer π hπ w hclosed
  rw [hstab] at hx
  exact ⟨x, hx⟩

end Langlands.Group.ClosedOrbit
