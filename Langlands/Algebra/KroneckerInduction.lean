import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Tower

/-! # Kronecker products of families of matrices and Galois induction of twisting matrices -/

noncomputable section

open scoped Matrix

namespace Langlands.Algebra.KroneckerInduction

section Kronecker

variable {R : Type*} [CommRing R] {D : Type*} [Fintype D] [DecidableEq D]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The Kronecker product of a finite family of square matrices: the matrix indexed by
`D → n` whose `(a, b)` entry is `∏ σ, Z σ (a σ) (b σ)`. -/
def piKronecker (Z : D → Matrix n n R) : Matrix (D → n) (D → n) R :=
  Matrix.of fun a b => ∏ σ, Z σ (a σ) (b σ)

omit [DecidableEq D] [Fintype n] [DecidableEq n] in
@[simp] theorem piKronecker_apply (Z : D → Matrix n n R) (a b : D → n) :
    piKronecker Z a b = ∏ σ, Z σ (a σ) (b σ) := rfl

omit [DecidableEq n] in
/-- The Kronecker product of factorwise products is the product of the Kronecker products. -/
theorem piKronecker_mul (Z W : D → Matrix n n R) :
    piKronecker (fun σ => Z σ * W σ) = piKronecker Z * piKronecker W := by
  ext a b
  simp only [piKronecker_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.prod_mul_distrib]

omit [DecidableEq D] [Fintype n] in
/-- The Kronecker product of identity matrices is the identity matrix. -/
theorem piKronecker_one : piKronecker (fun _ : D => (1 : Matrix n n R)) = 1 := by
  ext a b
  rw [piKronecker_apply, Matrix.one_apply]
  simp only [Matrix.one_apply]
  rw [Fintype.prod_boole]
  simp only [funext_iff]

omit [DecidableEq D] [Fintype n] [DecidableEq n] in
/-- Applying a ring homomorphism entrywise commutes with Kronecker products. -/
theorem piKronecker_map {S : Type*} [CommRing S] (f : R →+* S) (Z : D → Matrix n n R) :
    (piKronecker Z).map f = piKronecker (fun σ => (Z σ).map f) := by
  ext a b
  simp only [Matrix.map_apply, piKronecker_apply, map_prod]

omit [DecidableEq D] [Fintype n] [DecidableEq n] in
/-- Scalars of the factors multiply. -/
theorem piKronecker_smul (c : D → R) (Z : D → Matrix n n R) :
    piKronecker (fun σ => c σ • Z σ) = (∏ σ, c σ) • piKronecker Z := by
  ext a b
  simp only [piKronecker_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/-- Precomposition with a permutation of the index set, as an equivalence of the index type
`D → n` of a Kronecker product. -/
def indexEquiv (π : Equiv.Perm D) : (D → n) ≃ (D → n) where
  toFun a := a ∘ π
  invFun a := a ∘ π.symm
  left_inv a := by funext σ; simp
  right_inv a := by funext σ; simp

omit [Fintype D] [DecidableEq D] [Fintype n] [DecidableEq n] in
@[simp] theorem indexEquiv_apply (π : Equiv.Perm D) (a : D → n) :
    indexEquiv π a = a ∘ π := rfl

omit [Fintype D] [DecidableEq D] [Fintype n] [DecidableEq n] in
@[simp] theorem indexEquiv_symm_apply (π : Equiv.Perm D) (a : D → n) :
    (indexEquiv π).symm a = a ∘ π.symm := rfl

omit [DecidableEq D] [Fintype n] [DecidableEq n] in
/-- Permuting the factors of a Kronecker product reindexes its rows and columns. -/
theorem piKronecker_perm (π : Equiv.Perm D) (Z : D → Matrix n n R) :
    piKronecker (fun σ => Z (π.symm σ)) =
      (piKronecker Z).submatrix (indexEquiv π) (indexEquiv π) := by
  ext a b
  simp only [piKronecker_apply, Matrix.submatrix_apply, indexEquiv_apply, Function.comp_apply]
  rw [← Equiv.prod_comp π]
  simp only [Equiv.symm_apply_apply]

omit [DecidableEq D] [Fintype n] [DecidableEq n] in
/-- An entry of the Kronecker product of a family with one factor replaced. -/
theorem piKronecker_update {_ : DecidableEq D} (Z : D → Matrix n n R) (σ : D)
    (X : Matrix n n R) (a b : D → n) :
    piKronecker (Function.update Z σ X) a b =
      X (a σ) (b σ) * ∏ τ ∈ Finset.univ.erase σ, Z τ (a τ) (b τ) := by
  rw [piKronecker_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ),
    Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun τ hτ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

variable (S : Type*) [CommSemiring S] [Algebra S R] in
/-- The Kronecker product as a multilinear map of the factors, over any ring of scalars `S`
of `R`. -/
def piKroneckerMultilinear :
    MultilinearMap S (fun _ : D => Matrix n n R) (Matrix (D → n) (D → n) R) where
  toFun := piKronecker
  map_update_add' Z σ X Y := by
    ext a b
    rw [Matrix.add_apply, piKronecker_update, piKronecker_update, piKronecker_update,
      Matrix.add_apply, add_mul]
  map_update_smul' Z σ c X := by
    ext a b
    rw [Matrix.smul_apply, piKronecker_update, piKronecker_update, Matrix.smul_apply,
      smul_mul_assoc]

omit [DecidableEq D] [Fintype n] [DecidableEq n] in
@[simp] theorem piKroneckerMultilinear_apply (S : Type*) [CommSemiring S] [Algebra S R]
    (Z : D → Matrix n n R) : piKroneckerMultilinear S Z = piKronecker Z := rfl

omit [DecidableEq n] in
/-- **Intertwining Kronecker products.** If the factors satisfy `F σ * Y σ = X (π⁻¹ σ) * F σ`,
then the Kronecker product of the `F σ`, with rows reindexed along `π`, intertwines the
Kronecker products of `Y` and of `X`. -/
theorem piKronecker_intertwine (π : Equiv.Perm D) (F X Y : D → Matrix n n R)
    (h : ∀ σ, F σ * Y σ = X (π.symm σ) * F σ) :
    (piKronecker F).submatrix (indexEquiv π).symm id * piKronecker Y =
      piKronecker X * (piKronecker F).submatrix (indexEquiv π).symm id := by
  have hK := congrArg piKronecker (funext h)
  rw [piKronecker_mul, piKronecker_mul, piKronecker_perm π X] at hK
  have hrow := congrArg (fun M => M.submatrix (indexEquiv π).symm id) hK
  have e1 : ∀ M N : Matrix (D → n) (D → n) R,
      (M * N).submatrix (indexEquiv π).symm id = M.submatrix (indexEquiv π).symm id * N := by
    intro M N
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]
  have e2 : ∀ M N : Matrix (D → n) (D → n) R,
      (M.submatrix (indexEquiv π) (indexEquiv π) * N).submatrix (indexEquiv π).symm id =
        M * N.submatrix (indexEquiv π).symm id := by
    intro M N
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, id, Equiv.apply_symm_apply]
    exact Fintype.sum_equiv (indexEquiv π) _ _ fun c => by
      simp only [Equiv.symm_apply_apply]
  rw [e1, e2] at hrow
  exact hrow

/-- A Kronecker product of invertible matrices is invertible. -/
theorem isUnit_piKronecker {Z : D → Matrix n n R} (hZ : ∀ σ, IsUnit (Z σ)) :
    IsUnit (piKronecker Z) := by
  classical
  have h : piKronecker Z * piKronecker (fun σ => (Z σ)⁻¹) = 1 := by
    rw [← piKronecker_mul, ← piKronecker_one]
    congr 1
    funext σ
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hZ σ))
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h)

omit [DecidableEq n] in
/-- Reindexing only the rows of an invertible matrix along an equivalence keeps it
invertible. -/
theorem isUnit_submatrix_left {p : Type*} [Fintype p] [DecidableEq p] {M : Matrix p p R}
    (hM : IsUnit M) (e : p ≃ p) : IsUnit (M.submatrix e id) := by
  have h : M.submatrix e id * (M⁻¹).submatrix id e = 1 := by
    have := Matrix.submatrix_mul_equiv M M⁻¹ e (Equiv.refl p) e
    simp only [Equiv.coe_refl] at this
    rw [this, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM),
      Matrix.submatrix_one_equiv]
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse h)

end Kronecker

section Induction

variable (k E K : Type*) [Field k] [Field E] [Field K] [Algebra k E] [Algebra E K]
  [Algebra k K] [IsScalarTower k E K]

/-- Data for inducing a twisting family from `Gal(K/E)` to `Gal(K/k)`: a finite index set `D`
(in applications, the `k`-embeddings of `E`), a lift `ext σ` of each index to `Gal(K/k)`, the
permutation `perm τ` of indices by left multiplication, and the correction `stab τ σ` in
`Gal(K/E)`, related by `τ * ext σ = ext (perm τ σ) * stab τ σ`. -/
structure InductionData (D : Type*) where
  /-- The chosen lift of each index to `Gal(K/k)`. -/
  ext : D → (K ≃ₐ[k] K)
  /-- The permutation of indices induced by `τ`. -/
  perm : (K ≃ₐ[k] K) → Equiv.Perm D
  /-- The `Gal(K/E)` correction term. -/
  stab : (K ≃ₐ[k] K) → D → (K ≃ₐ[E] K)
  mul_ext : ∀ τ σ, τ * ext σ = ext (perm τ σ) * (stab τ σ).restrictScalars k

variable {k E K}
variable {D : Type*} [Fintype D] [DecidableEq D] {n : Type*} [Fintype n] [DecidableEq n]
  (I : InductionData k E K D) (Q : (K ≃ₐ[E] K) → Matrix n n K)

/-- The factor at the index `σ'` of the induced matrix of `τ`: the twisting matrix of the
correction term, transported by the lift of `σ'`. -/
def inducedFactor (τ : K ≃ₐ[k] K) (σ' : D) : Matrix n n K :=
  (Q (I.stab τ ((I.perm τ).symm σ'))).map (I.ext σ')

/-- The induced twisting matrix of `τ ∈ Gal(K/k)`: the Kronecker product of the factors with its
rows reindexed along the permutation of indices. -/
def inducedMatrix (τ : K ≃ₐ[k] K) : Matrix (D → n) (D → n) K :=
  (piKronecker (inducedFactor I Q τ)).submatrix (indexEquiv (I.perm τ)).symm id

/-- Induced matrices of invertible twisting matrices are invertible. -/
theorem isUnit_inducedMatrix (hQ : ∀ h, IsUnit (Q h)) (τ : K ≃ₐ[k] K) :
    IsUnit (inducedMatrix I Q τ) := by
  refine isUnit_submatrix_left (isUnit_piKronecker fun σ' => ?_) _
  have h := hQ (I.stab τ ((I.perm τ).symm σ'))
  rw [Matrix.isUnit_iff_isUnit_det] at h ⊢
  show IsUnit (((I.ext σ' : K ≃ₐ[k] K) : K →+* K).mapMatrix _).det
  rw [← RingHom.map_det]
  exact h.map _

variable {R : Type*} [CommRing R] [Algebra K R] (act : (K ≃ₐ[k] K) → R →+* R)

omit [DecidableEq n] in
/-- **Galois induction.** Let `Gal(K/k)` act on a commutative `K`-algebra `R` through ring maps
`act`, compatibly with multiplication of automorphisms and with `K`. If each matrix `Z σ` over
`R` satisfies the twisting equation `Q h * Z σ = h(Z σ) * Q h` for all `h ∈ Gal(K/E)`, then the
induced matrix of `τ` intertwines the Kronecker product of the transported factors `ext σ (Z σ)`
with its image under `τ`, up to the permutation of the factors:
`C τ * ⨂_{σ'} ext σ' (Z (perm τ⁻¹ σ')) = τ(⨂_σ ext σ (Z σ)) * C τ`. -/
theorem inducedMatrix_mul_piKronecker
    (hmul : ∀ g g' x, act (g * g') x = act g (act g' x))
    (halg : ∀ g c, act g (algebraMap K R c) = algebraMap K R (g c))
    (Z : D → Matrix n n R)
    (hZ : ∀ σ h, (Q h).map (algebraMap K R) * Z σ =
      (Z σ).map (act (h.restrictScalars k)) * (Q h).map (algebraMap K R))
    (τ : K ≃ₐ[k] K) :
    (inducedMatrix I Q τ).map (algebraMap K R) *
        piKronecker (fun σ' => (Z ((I.perm τ).symm σ')).map (act (I.ext σ'))) =
      (piKronecker fun σ => (Z σ).map (act (I.ext σ))).map (act τ) *
        (inducedMatrix I Q τ).map (algebraMap K R) := by
  set π := I.perm τ
  -- the factorwise identity
  have hfac : ∀ σ', (inducedFactor I Q τ σ').map (algebraMap K R) *
      (Z (π.symm σ')).map (act (I.ext σ')) =
      ((Z (π.symm σ')).map (act (I.ext (π.symm σ')))).map (act τ) *
        (inducedFactor I Q τ σ').map (algebraMap K R) := by
    intro σ'
    have h := congrArg (fun M => M.map (act (I.ext σ'))) (hZ (π.symm σ') (I.stab τ (π.symm σ')))
    simp only [Matrix.map_mul] at h
    have hQ : ((Q (I.stab τ (π.symm σ'))).map (algebraMap K R)).map (act (I.ext σ')) =
        (inducedFactor I Q τ σ').map (algebraMap K R) := by
      ext i j
      simp only [Matrix.map_apply, inducedFactor, halg]
      rfl
    have hZ' : ((Z (π.symm σ')).map (act ((I.stab τ (π.symm σ')).restrictScalars k))).map
        (act (I.ext σ')) = ((Z (π.symm σ')).map (act (I.ext (π.symm σ')))).map (act τ) := by
      ext i j
      simp only [Matrix.map_apply]
      rw [← hmul, ← hmul, I.mul_ext τ (π.symm σ')]
      simp only [π, Equiv.apply_symm_apply]
    rw [hQ, hZ'] at h
    exact h
  -- Kronecker products of both sides
  have hK := congrArg piKronecker (funext hfac)
  rw [piKronecker_mul, piKronecker_mul] at hK
  rw [← piKronecker_map, ← piKronecker_map] at hK
  rw [piKronecker_perm π (fun σ => (Z σ).map (act (I.ext σ))), ← Matrix.submatrix_map] at hK
  -- reindex the rows
  have hrow := congrArg (fun M => M.submatrix (indexEquiv π).symm id) hK
  have e1 : ∀ (M : Matrix (D → n) (D → n) K) (N : Matrix (D → n) (D → n) R),
      (M.map (algebraMap K R) * N).submatrix (indexEquiv π).symm id =
        (M.submatrix (indexEquiv π).symm id).map (algebraMap K R) * N := by
    intro M N
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.map_apply, id]
  have e2 : ∀ (X : Matrix (D → n) (D → n) R) (M : Matrix (D → n) (D → n) K),
      (X.submatrix (indexEquiv π) (indexEquiv π) * M.map (algebraMap K R)).submatrix
          (indexEquiv π).symm id =
        X * (M.submatrix (indexEquiv π).symm id).map (algebraMap K R) := by
    intro X M
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.map_apply, id,
      Equiv.apply_symm_apply]
    exact Fintype.sum_equiv (indexEquiv π) _ _ fun c => by
      simp only [Equiv.symm_apply_apply]
  rw [e1, e2] at hrow
  exact hrow

end Induction

end Langlands.Algebra.KroneckerInduction
