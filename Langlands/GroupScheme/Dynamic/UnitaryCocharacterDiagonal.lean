import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterWeights
import Mathlib.Analysis.Matrix.Hermitian

/-! # Unitary diagonalization of Hermitian cocharacter weight projectors -/

noncomputable section

universe u

open Module
open scoped InnerProductSpace Matrix

namespace Langlands.LinearAlgebra

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  {ι : Type*} [DecidableEq ι]

/-- Complete Hermitian orthogonal projectors admit a unitary common
coordinate basis, including when some projectors vanish. -/
theorem exists_unitary_conj_eq_diagonal_of_hermitian_orthogonal
    (E : ι → Matrix n n 𝕜)
    (hE : ∀ a b, E a * E b = if a = b then E a else 0)
    (s : Finset ι) (hs : ∑ a ∈ s, E a = 1)
    (hH : ∀ a, (E a).IsHermitian) :
    ∃ (P : Matrix.GeneralLinearGroup n 𝕜) (e : n → ι),
      (P : Matrix n n 𝕜) ∈ Matrix.unitaryGroup n 𝕜 ∧ ∀ a,
        ((P⁻¹ : Matrix.GeneralLinearGroup n 𝕜) : Matrix n n 𝕜) * E a *
          (P : Matrix n n 𝕜) =
            Matrix.diagonal fun i => if e i = a then 1 else 0 := by
  classical
  let A : ι → EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n :=
    fun a => (E a).toEuclideanLin
  let W : ι → Submodule 𝕜 (EuclideanSpace 𝕜 n) := fun a => LinearMap.range (A a)
  have hmul (a b : ι) (x : EuclideanSpace 𝕜 n) :
      A a (A b x) = if a = b then A a x else 0 := by
    change ((E a).toEuclideanLin.comp (E b).toEuclideanLin) x = _
    rw [← Matrix.toLpLin_mul_same, hE]
    split_ifs with h
    · rfl
    · simp
  have hfix (a : ι) (x : EuclideanSpace 𝕜 n) (hx : x ∈ W a) : A a x = x := by
    obtain ⟨y, rfl⟩ := hx
    simpa using hmul a a y
  have hkill (a b : ι) (hab : a ≠ b) (x : EuclideanSpace 𝕜 n) (hx : x ∈ W b) :
      A a x = 0 := by
    obtain ⟨y, rfl⟩ := hx
    simpa [hab] using hmul a b y
  have horth : OrthogonalFamily 𝕜 (fun a => W a) fun a => (W a).subtypeₗᵢ := by
    intro a b hab x y
    change inner 𝕜 (x : EuclideanSpace 𝕜 n) (y : EuclideanSpace 𝕜 n) = 0
    rw [← hfix a x x.property,
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (hH a), hkill a b hab y y.property,
      inner_zero_right]
  have htop : iSup W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ a ∈ s, A a x := by
      have h := congrArg (fun B : Matrix n n 𝕜 => B.toEuclideanLin x) hs
      simpa [A, map_sum, Matrix.toEuclideanLin] using h.symm
    rw [hx]
    exact Submodule.sum_mem _ fun a _ =>
      Submodule.mem_iSup_of_mem a ⟨x, rfl⟩
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top horth.independent htop
  let B0 := hint.collectedBasis fun a => (stdOrthonormalBasis 𝕜 (W a)).toBasis
  let : Finite (Σ a, Fin (finrank 𝕜 (W a))) := Module.Finite.finite_basis B0
  let : Fintype (Σ a, Fin (finrank 𝕜 (W a))) := Fintype.ofFinite _
  let B := B0.toOrthonormalBasis
    (DirectSum.IsInternal.collectedBasis_orthonormal horth hint
      (fun a => (stdOrthonormalBasis 𝕜 (W a)).orthonormal))
  let std := EuclideanSpace.basisFun n 𝕜
  let σ := std.toBasis.indexEquiv B.toBasis
  let B' := B.reindex σ.symm
  let e : n → ι := fun i => (σ i).1
  have hB' (i : n) : B' i ∈ W (e i) := by
    simp only [B', OrthonormalBasis.reindex_apply, Equiv.symm_symm]
    change B (σ i) ∈ W (σ i).1
    simp only [B, Basis.coe_toOrthonormalBasis]
    exact hint.collectedBasis_mem _ (σ i)
  let P0 := std.toBasis.toMatrix B'.toBasis
  let Q0 := B'.toBasis.toMatrix std.toBasis
  have hPQ : P0 * Q0 = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  have hQP : Q0 * P0 = 1 := Basis.toMatrix_mul_toMatrix_flip _ _
  let P : Matrix.GeneralLinearGroup n 𝕜 := ⟨P0, Q0, hPQ, hQP⟩
  refine ⟨P, e, std.toMatrix_orthonormalBasis_mem_unitary B', fun a => ?_⟩
  have hcol : E a * P0 = P0 * Matrix.diagonal (fun i => if e i = a then 1 else 0) := by
    ext r i
    have hP (j : n) : P0 j i = B' i j := by
      simp [P0, Basis.toMatrix_apply, std, EuclideanSpace.basisFun_repr]
    have hval : A a (B' i) = if a = e i then B' i else 0 := by
      by_cases h : a = e i
      · simpa [h] using hfix (e i) (B' i) (hB' i)
      · simpa [h] using hkill a (e i) h (B' i) (hB' i)
    have hv := congrArg (fun x : EuclideanSpace 𝕜 n => x r) hval
    change ((E a).mulVec (B' i)) r = _ at hv
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [hP]
    change (E a).mulVec (B' i) r = _
    rw [hv]
    by_cases h : a = e i
    · simp [h]
    · simp [h, Ne.symm h]
  change Q0 * E a * P0 = _
  rw [Matrix.mul_assoc, hcol, ← Matrix.mul_assoc, hQP, Matrix.one_mul]

end Langlands.LinearAlgebra

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]
  {𝕜 : Type u} [RCLike 𝕜]
  (χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ groupScheme n (CommRingCat.of 𝕜))

/-- Every Laurent weight projector is Hermitian in the given coordinates. -/
def HasHermitianWeightProjectors : Prop :=
  ∀ a, (weightProjector χ a).IsHermitian

/-- A cocharacter with Hermitian weight projectors is diagonalized by a unitary
base point on the actual general linear group scheme. -/
theorem exists_unitary_innerIso_comp_eq_diagonalCocharacter
    (hχ : HasHermitianWeightProjectors χ) :
    ∃ (g : GL n 𝕜) (e : n → ℤ),
      (g : Matrix n n 𝕜) ∈ Matrix.unitaryGroup n 𝕜 ∧
        χ ≫ (innerIso (groupScheme n (CommRingCat.of 𝕜))
          (baseOfMatrix (CommRingCat.of 𝕜) g)).hom =
            diagonalCocharacter n (CommRingCat.of 𝕜) e := by
  classical
  obtain ⟨P, e, hU, hP⟩ :=
    Langlands.LinearAlgebra.exists_unitary_conj_eq_diagonal_of_hermitian_orthogonal
      (weightProjector χ) (fun a b => by
        rw [weightProjector_mul]
        split_ifs with h
        · rw [h]
        · rfl) (cocharacterWeightSupport χ) (sum_weightProjector χ) hχ
  have hUi : ((P⁻¹ : GL n 𝕜) : Matrix n n 𝕜) ∈ Matrix.unitaryGroup n 𝕜 := by
    have h : P ∈ unitary (GL n 𝕜) := by
      simpa only [Units.unitary_eq, Submonoid.mem_comap, Units.coeHom_apply] using hU
    simpa only [Units.unitary_eq, Submonoid.mem_comap, Units.coeHom_apply] using
      Unitary.inv_mem h
  refine ⟨P⁻¹, e, hUi, eq_of_weightMatrix_eq _ ?_⟩
  rw [weightMatrix_innerIso, weightMatrix_diagonalCocharacter]
  have he : ∀ i, e i ∈ cocharacterWeightSupport χ := by
    intro i
    by_contra hi
    have h := congrFun (congrFun (hP (e i)) i) i
    rw [weightProjector_eq_zero χ hi, Matrix.mul_zero, Matrix.zero_mul] at h
    simp at h
  set φ := algebraMap 𝕜 (LaurentPolynomial 𝕜)
  have hM : (weightMatrix χ : Matrix n n (LaurentPolynomial 𝕜)) =
      ∑ a ∈ cocharacterWeightSupport χ,
        (LaurentPolynomial.T a : LaurentPolynomial 𝕜) • (weightProjector χ a).map φ := by
    refine Matrix.ext fun i j => ?_
    rw [weightMatrix_apply]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro a _
    change AddMonoidAlgebra.single a (weightProjector χ a i j) = _
    rw [LaurentPolynomial.single_eq_C_mul_T (R := 𝕜), mul_comm]
    rfl
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv, inv_inv, coe_diagonalUnits]
  change (P⁻¹ : GL n 𝕜).val.map φ * (weightMatrix χ : Matrix n n (LaurentPolynomial 𝕜)) *
    (P : GL n 𝕜).val.map φ = _
  rw [hM, Finset.mul_sum, Finset.sum_mul]
  have hterm : ∀ a, (P⁻¹ : GL n 𝕜).val.map φ *
      ((LaurentPolynomial.T a : LaurentPolynomial 𝕜) • (weightProjector χ a).map φ) *
      (P : GL n 𝕜).val.map φ =
        (LaurentPolynomial.T a : LaurentPolynomial 𝕜) •
          Matrix.diagonal (fun i => φ (if e i = a then 1 else 0)) := by
    intro a
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, ← Matrix.map_mul, hP a,
      Matrix.diagonal_map (map_zero φ)]
  simp only [hterm]
  ext i j
  rw [Matrix.sum_apply, Matrix.diagonal_apply]
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with hij
  · subst hij
    rw [cocharacterLaurentUnit_zpow]
    simp only [apply_ite φ, map_one, map_zero, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq (cocharacterWeightSupport χ) (e i)]
    simp [he i]
  · simp

end Langlands.GroupScheme.GeneralLinear
