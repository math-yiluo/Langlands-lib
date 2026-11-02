import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Split

/-!
# Kernels of matrices with a block of columns that is split injective

Let `d : M₀ →ₗ[R] M₁` be a linear map of finite free modules. Suppose a block `P` of columns of
its matrix has a left inverse up to a scalar `t` (a `ColumnSplit` of `d`). Wherever `t` is
invertible, the kernel of `d` is the kernel of the Schur complement of `P`. Combined with
McCoy's theorem, this shows the following. If the kernel of `d ⊗ A` is free with one generator
for each remaining column, then the Schur complement vanishes over `A`. If an element `u` kills
the Schur complement, then over every algebra in which `t` and `u` are units, the kernel of
`d ⊗ A` is spanned by finitely many explicit vectors of the kernel of `d`. At every field point
there is a column split whose scalar is nonzero there and whose remaining columns are as many as
the dimension of the kernel of the fibre.
-/

open Matrix Module TensorProduct

noncomputable section

namespace Langlands.LinearAlgebra.KernelColumnSplit

section McCoy

variable {A : Type*} [CommRing A] {m n : Type*} [Fintype n] [DecidableEq n]

/-- **McCoy.** A matrix whose kernel is free with one generator for each column is zero. -/
theorem eq_zero_of_ker_linearEquiv (S : Matrix m n A)
    (e : LinearMap.ker S.mulVecLin ≃ₗ[A] (n → A)) : S = 0 := by
  let φ : (n → A) →ₗ[A] n → A := (LinearMap.ker S.mulVecLin).subtype ∘ₗ e.symm.toLinearMap
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  let Φ : Matrix n n A := LinearMap.toMatrix' φ
  have hΦ : ∀ v, Φ *ᵥ v = φ v := LinearMap.toMatrix'_mulVec φ
  have hinj : Function.Injective Φ.mulVec := fun v w h => hφ (by rw [← hΦ, ← hΦ, h])
  have hdet : Φ.det ∈ nonZeroDivisors A :=
    nonsingular_iff_det_mem_nonZeroDivisors.mp
      (Nonsingular.of_linearIndependent_col (mulVec_injective_iff.mp hinj))
  have hSΦ : S * Φ = 0 := by
    ext i j
    have h1 : S *ᵥ φ (Pi.single j 1) = 0 := LinearMap.mem_ker.mp (e.symm (Pi.single j 1)).2
    rw [← hΦ, mulVec_mulVec, mulVec_single_one] at h1
    exact congrFun h1 i
  have h2 : Φ.det • S = 0 := by
    calc Φ.det • S = S * (Φ.det • (1 : Matrix n n A)) := by
          rw [Matrix.mul_smul, Matrix.mul_one]
      _ = S * (Φ * Φ.adjugate) := by rw [mul_adjugate]
      _ = 0 := by rw [← Matrix.mul_assoc, hSΦ, Matrix.zero_mul]
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h3
  rw [Matrix.zero_apply]
  exact (mem_nonZeroDivisors_iff.mp hdet).1 _ h3

end McCoy

section ColumnBlocks

variable {A : Type*} [CommRing A] {m κ α : Type*} [Fintype m] [Fintype κ] [Fintype α]
  [DecidableEq κ]

/-- The Schur complement `c • Q - P * (G * Q)` of a column block `P` with left inverse `G`
up to the scalar `c`. -/
def schur (P : Matrix m κ A) (Q : Matrix m α A) (G : Matrix κ m A) (c : A) : Matrix m α A :=
  c • Q - P * (G * Q)

omit [Fintype α] [DecidableEq κ] in
lemma schur_map {B : Type*} [CommRing B] (f : A →+* B) (P : Matrix m κ A) (Q : Matrix m α A)
    (G : Matrix κ m A) (c : A) :
    (schur P Q G c).map f = schur (P.map f) (Q.map f) (G.map f) (f c) := by
  ext i j
  simp [schur, Matrix.mul_apply, map_sum]

variable (P : Matrix m κ A) (Q : Matrix m α A) (G : Matrix κ m A) (c : A)

lemma schur_mulVec_eq_zero_of_mulVec_eq_zero (hG : G * P = c • 1)
    (v : κ ⊕ α → A) (hv : fromCols P Q *ᵥ v = 0) :
    schur P Q G c *ᵥ (v ∘ Sum.inr) = 0 := by
  rw [fromCols_mulVec] at hv
  have hQ : Q *ᵥ (v ∘ Sum.inr) = -(P *ᵥ (v ∘ Sum.inl)) := eq_neg_of_add_eq_zero_right hv
  rw [schur, sub_mulVec, smul_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hQ, mulVec_neg,
    mulVec_neg, mulVec_mulVec (M := G) (N := P), hG, smul_mulVec, one_mulVec, mulVec_smul]
  simp

lemma mulVec_eq_neg_of_mulVec_eq_zero (hG : G * P = c • 1)
    (v : κ ⊕ α → A) (hv : fromCols P Q *ᵥ v = 0) :
    (G * Q) *ᵥ (v ∘ Sum.inr) = -(c • (v ∘ Sum.inl)) := by
  rw [fromCols_mulVec] at hv
  have hQ : Q *ᵥ (v ∘ Sum.inr) = -(P *ᵥ (v ∘ Sum.inl)) := eq_neg_of_add_eq_zero_right hv
  rw [← mulVec_mulVec, hQ, mulVec_neg, mulVec_mulVec, hG, smul_mulVec, one_mulVec]

variable {c} (hc : IsUnit c)

/-- The vector of the kernel of `fromCols P Q` lying over `y` in the kernel of the Schur
complement. -/
def kerLift (y : α → A) : κ ⊕ α → A :=
  Sum.elim (-((hc.unit⁻¹ : Aˣ) : A) • ((G * Q) *ᵥ y)) y

omit [DecidableEq κ] in
lemma fromCols_mulVec_kerLift (y : α → A) :
    fromCols P Q *ᵥ kerLift Q G hc y = ((hc.unit⁻¹ : Aˣ) : A) • (schur P Q G c *ᵥ y) := by
  have h1 : ((hc.unit⁻¹ : Aˣ) : A) * c = 1 := hc.val_inv_mul
  rw [kerLift, fromCols_mulVec_sumElim, schur, sub_mulVec, smul_mulVec, mulVec_smul, smul_sub,
    smul_smul, h1, one_smul]
  simp only [neg_smul, mulVec_mulVec]
  abel

variable (hG : G * P = c • 1)
include hG

/-- If `G * P = c • 1` with `c` a unit, projection to the second block identifies the kernel of
`fromCols P Q` with the kernel of the Schur complement. -/
def kerFromColsEquiv :
    LinearMap.ker (fromCols P Q).mulVecLin ≃ₗ[A] LinearMap.ker (schur P Q G c).mulVecLin where
  toFun v := ⟨(v : κ ⊕ α → A) ∘ Sum.inr,
    schur_mulVec_eq_zero_of_mulVec_eq_zero P Q G c hG v (LinearMap.mem_ker.mp v.2)⟩
  invFun y := ⟨kerLift Q G hc y, by
    rw [LinearMap.mem_ker, mulVecLin_apply, fromCols_mulVec_kerLift,
      show schur P Q G c *ᵥ (y : α → A) = 0 from LinearMap.mem_ker.mp y.2, smul_zero]⟩
  map_add' v w := rfl
  map_smul' a v := rfl
  left_inv v := by
    apply Subtype.ext
    have h := mulVec_eq_neg_of_mulVec_eq_zero P Q G c hG v (LinearMap.mem_ker.mp v.2)
    change kerLift Q G hc ((v : κ ⊕ α → A) ∘ Sum.inr) = v
    rw [kerLift, h, smul_neg, neg_smul, neg_neg, smul_smul, hc.val_inv_mul, one_smul,
      Sum.elim_comp_inl_inr]
  right_inv y := by
    apply Subtype.ext
    rfl

end ColumnBlocks

section KerMatrix

variable {R : Type*} [CommRing R] {M₀ M₁ : Type*} [AddCommGroup M₀] [Module R M₀]
  [AddCommGroup M₁] [Module R M₁] {ι₀ ι₁ : Type*} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁]

/-- The kernel of a linear map between modules with finite bases is the kernel of its matrix;
the equivalence sends a vector to its coordinates. -/
def kerEquivMatrix (b₀ : Basis ι₀ R M₀) (b₁ : Basis ι₁ R M₁) (f : M₀ →ₗ[R] M₁) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker (LinearMap.toMatrix b₀ b₁ f).mulVecLin :=
  b₀.equivFun.ofSubmodules _ _ (by
    ext v
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearMap.mem_ker,
      LinearMap.mem_ker, Matrix.mulVecLin_apply]
    have hv : ⇑(b₀.repr (b₀.equivFun.symm v)) = v := b₀.equivFun.apply_symm_apply v
    have h := LinearMap.toMatrix_mulVec_repr b₀ b₁ f (b₀.equivFun.symm v)
    rw [hv] at h
    rw [h, LinearEquiv.coe_coe]
    constructor
    · intro hf
      rw [hf, map_zero, Finsupp.coe_zero]
    · intro h0
      exact b₁.repr.map_eq_zero_iff.mp (DFunLike.coe_injective h0))

lemma kerEquivMatrix_apply (b₀ : Basis ι₀ R M₀) (b₁ : Basis ι₁ R M₁) (f : M₀ →ₗ[R] M₁)
    (x : LinearMap.ker f) : (kerEquivMatrix b₀ b₁ f x : ι₀ → R) = b₀.repr x :=
  rfl

end KerMatrix

section Split

variable {R : Type*} [CommRing R] {M₀ M₁ : Type*} [AddCommGroup M₀] [Module R M₀]
  [AddCommGroup M₁] [Module R M₁]

/-- A splitting of the columns of the matrix of `d` into a block `P` with a left inverse up to the
scalar `t` and a remaining block `Q`. -/
structure ColumnSplit (d : M₀ →ₗ[R] M₁) where
  /-- Index type of the split block of columns. -/
  κ : Type
  /-- Index type of the remaining columns. -/
  α : Type
  /-- Index type of the rows. -/
  ι : Type
  [instFintypeκ : Fintype κ]
  [instDecidableEqκ : DecidableEq κ]
  [instFintypeα : Fintype α]
  [instDecidableEqα : DecidableEq α]
  [instFintypeι : Fintype ι]
  /-- The basis of the source, indexed by both blocks of columns. -/
  b₀ : Basis (κ ⊕ α) R M₀
  /-- The basis of the target. -/
  b₁ : Basis ι R M₁
  /-- The scalar. -/
  t : R
  /-- The left inverse of the split block up to `t`. -/
  inv : Matrix κ ι R
  inv_mul : inv * (LinearMap.toMatrix b₀ b₁ d).toCols₁ = t • 1

attribute [instance] ColumnSplit.instFintypeκ ColumnSplit.instDecidableEqκ
  ColumnSplit.instFintypeα ColumnSplit.instDecidableEqα ColumnSplit.instFintypeι

namespace ColumnSplit

variable {d : M₀ →ₗ[R] M₁} (S : ColumnSplit d)

/-- The split block of columns. -/
def P : Matrix S.ι S.κ R := (LinearMap.toMatrix S.b₀ S.b₁ d).toCols₁

/-- The remaining block of columns. -/
def Q : Matrix S.ι S.α R := (LinearMap.toMatrix S.b₀ S.b₁ d).toCols₂

/-- The Schur complement of the split block. -/
def schurMatrix : Matrix S.ι S.α R := schur S.P S.Q S.inv S.t

lemma inv_mul_P : S.inv * S.P = S.t • 1 := S.inv_mul

variable (A : Type*) [CommRing A] [Algebra R A]

lemma toMatrix_baseChange_eq :
    LinearMap.toMatrix (Algebra.TensorProduct.basis A S.b₀) (Algebra.TensorProduct.basis A S.b₁)
      (d.baseChange A) = fromCols (S.P.map (algebraMap R A)) (S.Q.map (algebraMap R A)) := by
  rw [LinearMap.toMatrix_baseChange, ← fromCols_map, P, Q, fromCols_toCols]

lemma inv_mul_P_map :
    S.inv.map (algebraMap R A) * S.P.map (algebraMap R A) = algebraMap R A S.t • 1 := by
  rw [← Matrix.map_mul, S.inv_mul_P, Matrix.map_smul' _ _ _ (map_mul _),
    Matrix.map_one _ (map_zero _) (map_one _)]

variable {A}

/-- Where `t` is a unit, the kernel of `d ⊗ A` is the kernel of the Schur complement over `A`. -/
def kerBaseChangeEquiv (ht : IsUnit (algebraMap R A S.t)) :
    LinearMap.ker (d.baseChange A) ≃ₗ[A]
      LinearMap.ker (S.schurMatrix.map (algebraMap R A)).mulVecLin :=
  (kerEquivMatrix (Algebra.TensorProduct.basis A S.b₀) (Algebra.TensorProduct.basis A S.b₁)
      (d.baseChange A)).trans <|
    (LinearEquiv.ofEq _ _ (by rw [S.toMatrix_baseChange_eq A])).trans <|
      (kerFromColsEquiv _ _ _ ht (S.inv_mul_P_map A)).trans <|
        LinearEquiv.ofEq _ _ (by rw [schurMatrix, schur_map])

lemma kerBaseChangeEquiv_apply (ht : IsUnit (algebraMap R A S.t))
    (w : LinearMap.ker (d.baseChange A)) :
    (S.kerBaseChangeEquiv ht w : S.α → A) =
      fun j => (Algebra.TensorProduct.basis A S.b₀).repr w (Sum.inr j) :=
  rfl

/-- If `t` is a unit in `A` and the kernel of `d ⊗ A` is free with one generator for each
remaining column, then the Schur complement vanishes in `A`. -/
theorem schurMatrix_map_eq_zero (ht : IsUnit (algebraMap R A S.t))
    (e : LinearMap.ker (d.baseChange A) ≃ₗ[A] (S.α → A)) :
    S.schurMatrix.map (algebraMap R A) = 0 :=
  eq_zero_of_ker_linearEquiv _ ((S.kerBaseChangeEquiv ht).symm.trans e)

/-- Where `t` is a unit and the Schur complement vanishes, the kernel of `d ⊗ A` is free on the
remaining columns; the equivalence takes the corresponding coordinates. -/
def kerBaseChangeEquivFun (ht : IsUnit (algebraMap R A S.t))
    (h0 : S.schurMatrix.map (algebraMap R A) = 0) :
    LinearMap.ker (d.baseChange A) ≃ₗ[A] (S.α → A) :=
  (S.kerBaseChangeEquiv ht).trans <|
    (LinearEquiv.ofEq _ _ (by rw [h0]; ext v; simp)).trans (LinearEquiv.ofTop _ rfl)

lemma kerBaseChangeEquivFun_apply (ht : IsUnit (algebraMap R A S.t))
    (h0 : S.schurMatrix.map (algebraMap R A) = 0) (w : LinearMap.ker (d.baseChange A))
    (j : S.α) :
    S.kerBaseChangeEquivFun ht h0 w j = (Algebra.TensorProduct.basis A S.b₀).repr w (Sum.inr j) :=
  rfl

lemma fromCols_mulVec_kerCoords (y : S.α → R) :
    fromCols S.P S.Q *ᵥ Sum.elim (-((S.inv * S.Q) *ᵥ y)) (S.t • y) = S.schurMatrix *ᵥ y := by
  rw [Matrix.fromCols_mulVec_sumElim, schurMatrix, schur, sub_mulVec, smul_mulVec, mulVec_neg,
    mulVec_smul, mulVec_mulVec]
  abel

/-- The vector of `M₀` with coordinates `u • (-(inv * Q) *ᵥ e_j, t • e_j)`. Its image under `d`
is `u` times the `j`-th column of the Schur complement. -/
def kerVector (u : R) (j : S.α) : M₀ :=
  S.b₀.equivFun.symm
    (u • Sum.elim (-((S.inv * S.Q) *ᵥ Pi.single j 1)) (S.t • Pi.single j 1))

lemma repr_kerVector (u : R) (j : S.α) :
    ⇑(S.b₀.repr (S.kerVector u j)) =
      u • Sum.elim (-((S.inv * S.Q) *ᵥ Pi.single j 1)) (S.t • Pi.single j 1) :=
  S.b₀.equivFun.apply_symm_apply _

lemma kerVector_mem_ker {u : R} (hu : u • S.schurMatrix = 0) (j : S.α) :
    S.kerVector u j ∈ LinearMap.ker d := by
  rw [LinearMap.mem_ker, ← S.b₁.repr.map_eq_zero_iff]
  apply DFunLike.coe_injective
  rw [← LinearMap.toMatrix_mulVec_repr S.b₀ S.b₁, repr_kerVector, mulVec_smul, ← fromCols_toCols
    (LinearMap.toMatrix S.b₀ S.b₁ d)]
  change u • (fromCols S.P S.Q *ᵥ _) = _
  rw [fromCols_mulVec_kerCoords, ← smul_mulVec, hu, zero_mulVec, Finsupp.coe_zero]

/-- If `u` kills the Schur complement, then over every `R`-algebra in which `t` and `u` are
units, every vector of the kernel of `d ⊗ A` is an `A`-linear combination of the vectors
`1 ⊗ kerVector u j`. -/
theorem exists_eq_sum_kerVector {u : R} (hu : u • S.schurMatrix = 0) (A : Type*) [CommRing A]
    [Algebra R A] (ht : IsUnit (algebraMap R A S.t)) (huA : IsUnit (algebraMap R A u))
    (w : A ⊗[R] M₀) (hw : w ∈ LinearMap.ker (d.baseChange A)) :
    ∃ a : S.α → A, w = ∑ j, a j • ((1 : A) ⊗ₜ[R] S.kerVector u j) := by
  have h0 : S.schurMatrix.map (algebraMap R A) = 0 := by
    ext i j
    have h := congrFun (congrFun hu i) j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h
    rw [Matrix.map_apply, Matrix.zero_apply, ← huA.mul_right_eq_zero, ← map_mul, h, map_zero]
  have hut : IsUnit (algebraMap R A u * algebraMap R A S.t) := huA.mul ht
  let c : A := ((hut.unit⁻¹ : Aˣ) : A)
  have hc : c * (algebraMap R A u * algebraMap R A S.t) = 1 := hut.val_inv_mul
  let y : S.α → A := S.kerBaseChangeEquivFun ht h0 ⟨w, hw⟩
  let v : A ⊗[R] M₀ := ∑ j, (y j * c) • ((1 : A) ⊗ₜ[R] S.kerVector u j)
  have hv : v ∈ LinearMap.ker (d.baseChange A) := by
    rw [LinearMap.mem_ker]
    simp only [v, map_sum, map_smul, LinearMap.baseChange_tmul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show d (S.kerVector u j) = 0 from S.kerVector_mem_ker hu j, TensorProduct.tmul_zero,
      smul_zero]
  have hyv : S.kerBaseChangeEquivFun ht h0 ⟨v, hv⟩ = S.kerBaseChangeEquivFun ht h0 ⟨w, hw⟩ := by
    funext j'
    rw [kerBaseChangeEquivFun_apply]
    change _ = y j'
    simp only [v, map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
      Finset.sum_apply, Pi.smul_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.mapRange_apply, repr_kerVector, one_smul, smul_eq_mul, Sum.elim_inr]
    rw [Finset.sum_eq_single j']
    · simp only [Pi.single_eq_same, mul_one, map_mul]
      rw [mul_assoc, hc, mul_one]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  refine ⟨fun j => y j * c, ?_⟩
  exact (congrArg Subtype.val ((S.kerBaseChangeEquivFun ht h0).injective hyv)).symm

/-- If `u` kills the Schur complement, then over every `R`-algebra in which `t` and `u` are
units, every vector of the kernel of `d ⊗ A` comes from `A ⊗ ker d`. -/
theorem kerBaseChange_le_range {u : R} (hu : u • S.schurMatrix = 0) (A : Type*) [CommRing A]
    [Algebra R A] (ht : IsUnit (algebraMap R A S.t)) (huA : IsUnit (algebraMap R A u)) :
    LinearMap.ker (d.baseChange A) ≤
      LinearMap.range ((LinearMap.ker d).subtype.baseChange A) := by
  intro w hw
  obtain ⟨a, rfl⟩ := S.exists_eq_sum_kerVector hu A ht huA w hw
  refine ⟨∑ j, a j • ((1 : A) ⊗ₜ[R] (⟨S.kerVector u j, S.kerVector_mem_ker hu j⟩ :
    LinearMap.ker d)), ?_⟩
  simp only [map_sum, map_smul, LinearMap.baseChange_tmul, Submodule.subtype_apply]

/-- If the Schur complement vanishes after inverting `u`, then a power of `u` kills it. -/
lemma exists_pow_smul_schurMatrix_eq_zero (u : R) (Rᵤ : Type*) [CommRing Rᵤ] [Algebra R Rᵤ]
    [IsLocalization.Away u Rᵤ] (h : S.schurMatrix.map (algebraMap R Rᵤ) = 0) :
    ∃ n : ℕ, u ^ n • S.schurMatrix = 0 := by
  classical
  have hx : ∀ i j, ∃ m : Submonoid.powers u, (m : R) * S.schurMatrix i j = 0 := fun i j =>
    (IsLocalization.map_eq_zero_iff (Submonoid.powers u) Rᵤ _).mp
      (by simpa using congrFun (congrFun h i) j)
  choose m hm using hx
  obtain ⟨n, hn⟩ : (∏ p : S.ι × S.α, (m p.1 p.2 : R)) ∈ Submonoid.powers u :=
    Submonoid.prod_mem _ fun p _ => (m p.1 p.2).2
  refine ⟨n, ?_⟩
  ext i j
  change u ^ n * S.schurMatrix i j = 0
  rw [show u ^ n = _ from hn,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), mul_assoc, hm, mul_zero]

end ColumnSplit

/-- At a field point `R → K`, a map of finite free modules has a column split whose scalar is
nonzero in `K` and whose remaining columns are as many as the dimension of the kernel of `d ⊗ K`.
The split block consists of a maximal family of columns that are linearly independent over `K`. -/
theorem exists_columnSplit {K : Type*} [Field K] [Algebra R K] [Module.Free R M₀]
    [Module.Finite R M₀] [Module.Free R M₁] [Module.Finite R M₁] (d : M₀ →ₗ[R] M₁) :
    ∃ S : ColumnSplit d, algebraMap R K S.t ≠ 0 ∧
      Fintype.card S.α = Module.finrank K (LinearMap.ker (d.baseChange K)) := by
  classical
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  let b₀ := Module.finBasis R M₀
  let b₁ := Module.finBasis R M₁
  let D : Matrix (Fin (Module.finrank R M₁)) (Fin (Module.finrank R M₀)) K :=
    (LinearMap.toMatrix b₀ b₁ d).map (algebraMap R K)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K D.col
  have : Fintype κ := @Fintype.ofFinite κ (Finite.of_injective a ha)
  let α := {j // j ∉ Set.range a}
  let e : κ ⊕ α ≃ Fin (Module.finrank R M₀) :=
    ((Equiv.ofInjective a ha).sumCongr (Equiv.refl α)).trans (Equiv.sumCompl _)
  have he : ∀ k, e (Sum.inl k) = a k := fun _ => rfl
  let b₀' := b₀.reindex e.symm
  let F : Matrix (Fin (Module.finrank R M₁)) κ R := (LinearMap.toMatrix b₀' b₁ d).toCols₁
  have hF : Function.Injective (F.map (algebraMap R K)).mulVec := by
    rw [mulVec_injective_iff]
    convert hli using 1
    funext k i
    rw [Function.comp_apply, col_apply, col_apply]
    simp [F, D, b₀', LinearMap.toMatrix_apply, he]
  obtain ⟨t, ht, G, hG⟩ :=
    Langlands.Cohomology.ModuleComplex.FibreH0Spread.exists_mul_eq_smul_one
      (algebraMap R K) F hF
  refine ⟨
    { κ := κ, α := α, ι := Fin (Module.finrank R M₁), b₀ := b₀', b₁ := b₁, t := t
      inv := G, inv_mul := hG }, ht, ?_⟩
  change Fintype.card α = _
  have hker : Module.finrank K (LinearMap.ker (d.baseChange K)) =
      Module.finrank K (LinearMap.ker D.mulVecLin) := by
    refine LinearEquiv.finrank_eq ((kerEquivMatrix (Algebra.TensorProduct.basis K b₀)
      (Algebra.TensorProduct.basis K b₁) (d.baseChange K)).trans (LinearEquiv.ofEq _ _ ?_))
    rw [LinearMap.toMatrix_baseChange]
  have hrank := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  rw [Matrix.range_mulVecLin, ← hsp, finrank_span_eq_card hli, Module.finrank_fin_fun] at hrank
  have hcard : Fintype.card κ + Fintype.card α = Module.finrank R M₀ := by
    rw [← Fintype.card_sum, Fintype.card_congr e, Fintype.card_fin]
  rw [hker]
  omega

end Split

end Langlands.LinearAlgebra.KernelColumnSplit
