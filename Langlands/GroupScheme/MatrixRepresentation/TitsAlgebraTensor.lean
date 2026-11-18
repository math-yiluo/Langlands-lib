import Langlands.GroupScheme.MatrixRepresentation.TitsAlgebraFixed
import Langlands.GroupScheme.MatrixRepresentationTensor
import Langlands.Algebra.CentralSimpleTensor

/-! # Tits algebras of tensor products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix TensorProduct Kronecker

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

section Kronecker

/-- `X ↦ X ⊗ₖ 1` as a `k`-algebra map. -/
def kroneckerLeft : Matrix n n K →ₐ[k] Matrix (n × m) (n × m) K where
  toFun X := X ⊗ₖ (1 : Matrix m m K)
  map_one' := Matrix.one_kronecker_one
  map_mul' X Y := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  map_zero' := Matrix.zero_kronecker _
  map_add' X Y := Matrix.add_kronecker _ _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [Matrix.smul_kronecker, Matrix.one_kronecker_one]

/-- `Y ↦ 1 ⊗ₖ Y` as a `k`-algebra map. -/
def kroneckerRight : Matrix m m K →ₐ[k] Matrix (n × m) (n × m) K where
  toFun Y := (1 : Matrix n n K) ⊗ₖ Y
  map_one' := Matrix.one_kronecker_one
  map_mul' X Y := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
  map_zero' := Matrix.kronecker_zero _
  map_add' X Y := Matrix.kronecker_add _ _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [Matrix.kronecker_smul, Matrix.one_kronecker_one]

theorem kroneckerLeft_mul_kroneckerRight (X : Matrix n n K) (Y : Matrix m m K) :
    kroneckerLeft (k := k) (m := m) X * kroneckerRight (k := k) (n := n) Y = X ⊗ₖ Y := by
  change (X ⊗ₖ (1 : Matrix m m K)) * ((1 : Matrix n n K) ⊗ₖ Y) = X ⊗ₖ Y
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- The Kronecker product of two subalgebras, as an algebra map from their tensor product. -/
def kroneckerTensor (A : Subalgebra k (Matrix n n K)) (B : Subalgebra k (Matrix m m K)) :
    A ⊗[k] B →ₐ[k] Matrix (n × m) (n × m) K :=
  Algebra.TensorProduct.lift ((kroneckerLeft (k := k) (m := m)).comp A.val)
    ((kroneckerRight (k := k) (n := n)).comp B.val) (fun X Y => by
      change Commute ((X : Matrix n n K) ⊗ₖ (1 : Matrix m m K))
        ((1 : Matrix n n K) ⊗ₖ (Y : Matrix m m K))
      rw [Commute, SemiconjBy, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul])

theorem kroneckerTensor_tmul (A : Subalgebra k (Matrix n n K)) (B : Subalgebra k (Matrix m m K))
    (X : A) (Y : B) :
    kroneckerTensor A B (X ⊗ₜ Y) = (X : Matrix n n K) ⊗ₖ (Y : Matrix m m K) := by
  rw [kroneckerTensor, Algebra.TensorProduct.lift_tmul]
  exact kroneckerLeft_mul_kroneckerRight (k := k) _ _

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem kronecker_map_galois (σ : K ≃ₐ[k] K) (X : Matrix n n K) (Y : Matrix m m K) :
    (X ⊗ₖ Y).map σ = X.map σ ⊗ₖ Y.map σ := by
  ext a b
  simp [map_mul]

/-- The Kronecker product of twisted-fixed algebras is twisted-fixed for the Kronecker product
of the twisting matrices. -/
theorem range_kroneckerTensor_le_twistedFixed
    {A : Subalgebra k (Matrix n n K)} {B : Subalgebra k (Matrix m m K)}
    {P : (K ≃ₐ[k] K) → Matrix n n K} {Q : (K ≃ₐ[k] K) → Matrix m m K}
    (hA : A ≤ Algebra.GaloisTwistedMatrix.twistedFixed P)
    (hB : B ≤ Algebra.GaloisTwistedMatrix.twistedFixed Q) :
    (kroneckerTensor A B).range ≤
      Algebra.GaloisTwistedMatrix.twistedFixed (fun σ => P σ ⊗ₖ Q σ) := by
  rintro _ ⟨z, rfl⟩
  change kroneckerTensor A B z ∈ _
  induction z with
  | tmul X Y =>
    rw [kroneckerTensor_tmul]
    intro σ
    rw [← Matrix.mul_kronecker_mul, hA X.2 σ, hB Y.2 σ, Matrix.mul_kronecker_mul,
      kronecker_map_galois]
  | add z w hz hw => rw [map_add]; exact add_mem hz hw

/-- If both factors span the full matrix algebras over `K`, so does their Kronecker product. -/
theorem span_range_kroneckerTensor
    {A : Subalgebra k (Matrix n n K)} {B : Subalgebra k (Matrix m m K)}
    (hA : Submodule.span K (A : Set (Matrix n n K)) = ⊤)
    (hB : Submodule.span K (B : Set (Matrix m m K)) = ⊤) :
    Submodule.span K ((kroneckerTensor A B).range : Set (Matrix (n × m) (n × m) K)) = ⊤ := by
  classical
  let S := Submodule.span K ((kroneckerTensor A B).range : Set (Matrix (n × m) (n × m) K))
  have hpure : ∀ (X : Matrix n n K) (Y : Matrix m m K), X ⊗ₖ Y ∈ S := by
    intro X Y
    have hY : ∀ Y' ∈ B, ∀ X : Matrix n n K, X ⊗ₖ (Y' : Matrix m m K) ∈ S := by
      intro Y' hY' X
      have hX : X ∈ Submodule.span K (A : Set (Matrix n n K)) := by rw [hA]; trivial
      induction hX using Submodule.span_induction with
      | mem X hX =>
        exact Submodule.subset_span ⟨(⟨X, hX⟩ : A) ⊗ₜ (⟨Y', hY'⟩ : B),
          kroneckerTensor_tmul _ _ _ _⟩
      | zero => rw [Matrix.zero_kronecker]; exact S.zero_mem
      | add X X' _ _ h1 h2 => rw [Matrix.add_kronecker]; exact S.add_mem h1 h2
      | smul c X _ h1 => rw [Matrix.smul_kronecker]; exact S.smul_mem c h1
    have hYm : Y ∈ Submodule.span K (B : Set (Matrix m m K)) := by rw [hB]; trivial
    induction hYm using Submodule.span_induction with
    | mem Y hY' => exact hY Y hY' X
    | zero => rw [Matrix.kronecker_zero]; exact S.zero_mem
    | add Y Y' _ _ h1 h2 => rw [Matrix.kronecker_add]; exact S.add_mem h1 h2
    | smul c Y _ h1 => rw [Matrix.kronecker_smul]; exact S.smul_mem c h1
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  have h := hpure (Matrix.single a.1 b.1 (M a b)) (Matrix.single a.2 b.2 1)
  rwa [Matrix.single_kronecker_single, mul_one] at h

end Kronecker

section CentralSimple

variable [IsGalois k K] [Nonempty n] [Nonempty m]

/-- Under the descent hypotheses, the Kronecker product map is injective. -/
theorem kroneckerTensor_injective
    {A : Subalgebra k (Matrix n n K)} {B : Subalgebra k (Matrix m m K)}
    {P : (K ≃ₐ[k] K) → Matrix n n K} {Q : (K ≃ₐ[k] K) → Matrix m m K}
    (hPu : ∀ σ, IsUnit (P σ)) (hQu : ∀ σ, IsUnit (Q σ))
    (hA : A ≤ Algebra.GaloisTwistedMatrix.twistedFixed P)
    (hB : B ≤ Algebra.GaloisTwistedMatrix.twistedFixed Q)
    (hAs : Submodule.span K (A : Set (Matrix n n K)) = ⊤)
    (hBs : Submodule.span K (B : Set (Matrix m m K)) = ⊤) :
    Function.Injective (kroneckerTensor A B) := by
  have := Algebra.GaloisTwistedMatrix.finiteDimensional P hPu A hA
  have := Algebra.GaloisTwistedMatrix.finiteDimensional Q hQu B hB
  have := Algebra.GaloisTwistedMatrix.isSimpleRing P hPu A hA hAs
  have := Algebra.GaloisTwistedMatrix.isSimpleRing Q hQu B hB hBs
  have := Algebra.GaloisTwistedMatrix.isCentral P hPu A hA hAs
  have := Algebra.GaloisTwistedMatrix.isCentral Q hQu B hB hBs
  have : IsSimpleRing (A ⊗[k] B) := Langlands.CentralSimple.isSimpleRing_tensor k A B
  have : Nontrivial (Matrix (n × m) (n × m) K) := inferInstance
  exact (IsSimpleRing.injective_ringHom_or_subsingleton_codomain (R := A ⊗[k] B)
    (S := Matrix (n × m) (n × m) K) (kroneckerTensor A B).toRingHom).resolve_right
    (not_subsingleton _)

omit [Nonempty n] [Nonempty m] in
theorem isUnit_kronecker {P : Matrix n n K} {Q : Matrix m m K} (hP : IsUnit P) (hQ : IsUnit Q) :
    IsUnit (P ⊗ₖ Q) := by
  rw [Matrix.isUnit_iff_isUnit_det] at hP hQ ⊢
  rw [Matrix.det_kronecker]
  exact (hP.pow _).mul (hQ.pow _)

/-- The Kronecker product of two descended algebras, as a central simple algebra. -/
def kroneckerCSA (A : Subalgebra k (Matrix n n K)) (B : Subalgebra k (Matrix m m K))
    (P : (K ≃ₐ[k] K) → Matrix n n K) (Q : (K ≃ₐ[k] K) → Matrix m m K)
    (hPu : ∀ σ, IsUnit (P σ)) (hQu : ∀ σ, IsUnit (Q σ))
    (hA : A ≤ Algebra.GaloisTwistedMatrix.twistedFixed P)
    (hB : B ≤ Algebra.GaloisTwistedMatrix.twistedFixed Q)
    (hAs : Submodule.span K (A : Set (Matrix n n K)) = ⊤)
    (hBs : Submodule.span K (B : Set (Matrix m m K)) = ⊤) : CSA.{u, u} k :=
  Algebra.GaloisTwistedMatrix.toCSA (fun σ => P σ ⊗ₖ Q σ)
    (fun σ => isUnit_kronecker (hPu σ) (hQu σ)) (kroneckerTensor A B).range
    (range_kroneckerTensor_le_twistedFixed hA hB) (span_range_kroneckerTensor hAs hBs)

/-- The Kronecker product algebra is isomorphic to the tensor product, hence represents the
product of the Brauer classes. -/
theorem kroneckerCSA_isBrauerEquivalent (A : Subalgebra k (Matrix n n K))
    (B : Subalgebra k (Matrix m m K))
    (P : (K ≃ₐ[k] K) → Matrix n n K) (Q : (K ≃ₐ[k] K) → Matrix m m K)
    (hPu : ∀ σ, IsUnit (P σ)) (hQu : ∀ σ, IsUnit (Q σ))
    (hA : A ≤ Algebra.GaloisTwistedMatrix.twistedFixed P)
    (hB : B ≤ Algebra.GaloisTwistedMatrix.twistedFixed Q)
    (hAs : Submodule.span K (A : Set (Matrix n n K)) = ⊤)
    (hBs : Submodule.span K (B : Set (Matrix m m K)) = ⊤) :
    IsBrauerEquivalent (kroneckerCSA A B P Q hPu hQu hA hB hAs hBs)
      (Langlands.Brauer.tensor (Algebra.GaloisTwistedMatrix.toCSA P hPu A hA hAs)
        (Algebra.GaloisTwistedMatrix.toCSA Q hQu B hB hBs)) :=
  ⟨1, 1, one_ne_zero, one_ne_zero,
    ⟨(AlgEquiv.ofInjective (kroneckerTensor A B)
      (kroneckerTensor_injective hPu hQu hA hB hAs hBs)).symm.mapMatrix⟩⟩

end CentralSimple


section Representations

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

theorem universalMatrix_tensor
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (τ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) m)
    (i i' : n) (j j' : m) :
    universalMatrix (ρ.tensor τ) (i, j) (i', j') = universalMatrix ρ i i' * universalMatrix τ j j' :=
  tensor_affineMatrix_entry ρ τ _ _ i i' j j'

/-- The Tits algebra of a tensor product lies in the Kronecker product of the Tits algebras. -/
theorem titsAlgebra_tensor_le
    (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) n)
    (τ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) m) :
    titsAlgebra (ρ.tensor τ) ≤ (kroneckerTensor (titsAlgebra ρ) (titsAlgebra τ)).range := by
  classical
  rw [titsAlgebra, Algebra.adjoin_le_iff]
  rintro _ ⟨φ, rfl⟩
  obtain ⟨r, ψ, o, h⟩ := exists_reconstruction (K := K)
    (Finset.univ.image (fun p : n × n => universalMatrix ρ p.1 p.2) ∪
      Finset.univ.image (fun p : m × m => universalMatrix τ p.1 p.2))
  have hρ : ∀ i i', universalMatrix ρ i i' =
      ∑ s, baseFunctional K (ψ s) (universalMatrix ρ i i') • ((1 : K) ⊗ₜ[k] o s) := fun i i' =>
    h _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, i'), Finset.mem_univ _, rfl⟩))
  have hτ : ∀ j j', universalMatrix τ j j' =
      ∑ s, baseFunctional K (ψ s) (universalMatrix τ j j') • ((1 : K) ⊗ₜ[k] o s) := fun j j' =>
    h _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(j, j'), Finset.mem_univ _, rfl⟩))
  have key : coefficientMatrix (ρ.tensor τ) φ = ∑ s, ∑ t, φ (o s * o t) •
      (coefficientMatrix ρ (ψ s) ⊗ₖ coefficientMatrix τ (ψ t)) := by
    ext ⟨i, j⟩ ⟨i', j'⟩
    rw [coefficientMatrix, Matrix.map_apply, universalMatrix_tensor, hρ i i', hτ j j',
      Finset.sum_mul_sum]
    simp only [map_sum, Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker_apply,
      coefficientMatrix, Matrix.map_apply]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [smul_mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_smul,
      baseFunctional_tmul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def]
    ring
  rw [key]
  refine Subalgebra.sum_mem _ fun s _ => Subalgebra.sum_mem _ fun t _ => ?_
  refine Subalgebra.smul_mem _ ?_ _
  exact ⟨(⟨_, Algebra.subset_adjoin ⟨ψ s, rfl⟩⟩ : titsAlgebra ρ) ⊗ₜ
    (⟨_, Algebra.subset_adjoin ⟨ψ t, rfl⟩⟩ : titsAlgebra τ), kroneckerTensor_tmul _ _ _ _⟩

end Representations

end Langlands.GroupScheme.MatrixRepresentation
