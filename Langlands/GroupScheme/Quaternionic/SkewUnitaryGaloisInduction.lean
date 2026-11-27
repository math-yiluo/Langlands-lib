import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisLocalStep
import Langlands.GroupScheme.Rational.NumberFieldSkewRepresentation

/-! # The inductive step of the special unitary Hasse principle

For `H = adjoinSkewLine H₁ c` over a number field, a locally trivial special unitary crossed
homomorphism is moved into the stabilizer of the last row by the global representation of `c`
by the descended Gram matrix and proper Witt transitivity; the block crossed homomorphism for
`H₁` is again locally trivial.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]

section VecMap

/-- Entrywise coefficient change on row vectors. -/
def vecMap {n : ℕ} {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (x : Fin n → R ⊗[F] D) : Fin n → S ⊗[F] D :=
  fun j => Algebra.TensorProduct.map f (AlgHom.id F D) (x j)

theorem vecMap_vecMul {n : ℕ} {R S : Type u} [CommRing R] [CommRing S] [Algebra F R]
    [Algebra F S] (f : R →ₐ[F] S) (x : Fin n → R ⊗[F] D)
    (M : Matrix (Fin n) (Fin n) (R ⊗[F] D)) :
    vecMap f (x ᵥ* M) = vecMap f x ᵥ* coeffMap f M := by
  funext j
  exact RingHom.map_vecMul (Algebra.TensorProduct.map f (AlgHom.id F D)).toRingHom M x j

theorem matrixSesqBilin_eq_dotProduct {n : ℕ} {R : Type u} [CommRing R] [Algebra F R]
    (τ : FirstKindInvolution F D) (G : Matrix (Fin n) (Fin n) (R ⊗[F] D))
    (x y : Fin n → R ⊗[F] D) :
    (τ.baseChange R).matrixSesqBilin G x y =
      x ⬝ᵥ (G *ᵥ fun j => (τ.baseChange R) (y j)) := by
  simp only [FirstKindInvolution.matrixSesqBilin, LinearMap.mk₂_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem baseChange_vecMul {n : ℕ} {R : Type u} [CommRing R] [Algebra F R]
    (τ : FirstKindInvolution F D) (C : Matrix (Fin n) (Fin n) (R ⊗[F] D))
    (y : Fin n → R ⊗[F] D) :
    (fun j => (τ.baseChange R) ((y ᵥ* C) j)) =
      (τ.baseChange R).matrix (Fin n) C *ᵥ fun j => (τ.baseChange R) (y j) := by
  funext j
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, FirstKindInvolution.map_sum,
    FirstKindInvolution.map_mul, FirstKindInvolution.matrix_apply]

theorem matrixSesqBilin_vecMul {n : ℕ} {R : Type u} [CommRing R] [Algebra F R]
    (τ : FirstKindInvolution F D) (G A C : Matrix (Fin n) (Fin n) (R ⊗[F] D))
    (x y : Fin n → R ⊗[F] D) :
    (τ.baseChange R).matrixSesqBilin G (x ᵥ* A) (y ᵥ* C) =
      (τ.baseChange R).matrixSesqBilin (A * G * (τ.baseChange R).matrix (Fin n) C) x y := by
  rw [matrixSesqBilin_eq_dotProduct, matrixSesqBilin_eq_dotProduct, baseChange_vecMul,
    Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

end VecMap

section Gram

variable [Algebra.IsCentral F D] [FiniteDimensional F D] (τ : FirstKindInvolution F D)

omit [Algebra.IsCentral F D] [FiniteDimensional F D] in
theorem matrixSesqBilin_gramOver {n : ℕ} (L : Type u) [CommRing L] [Algebra F L]
    (G : Matrix (Fin n) (Fin n) D) (y : Fin n → D) :
    (τ.baseChange L).matrixSesqBilin (gramOver n G L)
        (fun j => (Algebra.TensorProduct.includeRight (y j) : L ⊗[F] D))
        (fun j => (Algebra.TensorProduct.includeRight (y j) : L ⊗[F] D)) =
      Algebra.TensorProduct.includeRight (τ.sesqForm G y y) := by
  simp only [FirstKindInvolution.matrixSesqBilin, LinearMap.mk₂_apply, gramOver, Matrix.map_apply,
    FirstKindInvolution.sesqForm, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1

omit [Algebra.IsCentral F D] [FiniteDimensional F D] in
theorem matrixSesqBilin_lastRow {m : ℕ} (R : Type u) [CommRing R] [Algebra F R]
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) (R ⊗[F] D)) :
    (τ.baseChange R).matrixSesqBilin G (lastRow R) (lastRow R) = G (Fin.last m) (Fin.last m) := by
  have hone : lastRow R = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (R ⊗[F] D)) (Fin.last m) := by
    funext j
    simp only [lastRow, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [hone, matrixSesqBilin_row, Matrix.one_mul, FirstKindInvolution.map_one, Matrix.mul_one]

omit [Algebra.IsCentral F D] [FiniteDimensional F D] in
theorem GramDescent.inv_gram_eq {n : ℕ} [NeZero n] {H : Matrix (Fin n) (Fin n) D}
    {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ} (d : GramDescent τ H c) :
    ((d.primitive⁻¹ : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) : Matrix (Fin n) (Fin n) (L ⊗[F] D)) *
        gramOver n H L * (τ.baseChange L).matrix (Fin n)
          ((d.primitive⁻¹ : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) :
            Matrix (Fin n) (Fin n) (L ⊗[F] D)) = gramOver n d.gram L := by
  set adj := (τ.baseChange L).matrix (Fin n)
  set P : Matrix (Fin n) (Fin n) (L ⊗[F] D) := (d.primitive : Matrix (Fin n) (Fin n) (L ⊗[F] D))
  set Pi : Matrix (Fin n) (Fin n) (L ⊗[F] D) :=
    ((d.primitive⁻¹ : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) : Matrix (Fin n) (Fin n) (L ⊗[F] D))
  have h1 : Pi * P = 1 := Units.inv_mul d.primitive
  calc Pi * gramOver n H L * adj Pi = Pi * (P * gramOver n d.gram L * adj P) * adj Pi := by
        rw [d.gram_eq]
    _ = (Pi * P) * gramOver n d.gram L * (adj P * adj Pi) := by simp only [Matrix.mul_assoc]
    _ = gramOver n d.gram L := by
        rw [h1, ← FirstKindInvolution.map_mul, h1, FirstKindInvolution.map_one, Matrix.one_mul,
          Matrix.mul_one]

end Gram

section Core

variable [Algebra.IsCentral F D] [FiniteDimensional F D] [NumberField F]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

/-- The special unitary Hasse principle at the Galois level for Gram matrices of size `n`. -/
def SUHasse (n : ℕ) [NeZero n] : Prop :=
  ∀ (H : Matrix (Fin n) (Fin n) D), (σ.quaternionConjugation hdim hsym).IsAntihermitian H →
    IsUnit H →
  ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ), IsCrossed c →
    (∀ s, c s ∈ suGroup (σ.quaternionConjugation hdim hsym) H L) →
    IsLocallyCoboundary (σ.quaternionConjugation hdim hsym) H c →
    ∃ a ∈ suGroup (σ.quaternionConjugation hdim hsym) H L,
      ∀ s, c s = a * (unitMap s.toAlgHom a)⁻¹

omit [NumberField F] [Algebra.IsCentral F D] [FiniteDimensional F D] in
theorem vecMap_includeRight {n : ℕ} {L : Type u} [Field L] [Algebra F L] (s : L ≃ₐ[F] L)
    (y : Fin n → D) :
    vecMap s.toAlgHom (fun j => (Algebra.TensorProduct.includeRight (y j) : L ⊗[F] D)) =
      fun j => Algebra.TensorProduct.includeRight (y j) := by
  funext j
  simp [vecMap]

omit [NumberField F] [Algebra.IsCentral F D] [FiniteDimensional F D] in
theorem vecMap_lastRow {m : ℕ} {L : Type u} [Field L] [Algebra F L] (s : L ≃ₐ[F] L) :
    vecMap s.toAlgHom (lastRow (F := F) (D := D) (m := m) L) = lastRow L := by
  funext j
  by_cases hj : j = Fin.last m
  · subst hj
    simp [vecMap, lastRow]
  · simp [vecMap, lastRow, Pi.single_eq_of_ne hj]

/-- The inductive step for an adjoined line. -/
theorem suHasse_adjoin {m : ℕ} [NeZero m]
    (hW : ∀ (K : Type u) [Field K] [Algebra F K] [CharZero K],
      ProperWittAt (σ.quaternionConjugation hdim hsym) K (m + 1))
    (IH : SUHasse σ hdim hsym m)
    (H₁ : Matrix (Fin m) (Fin m) D) (c0 : D)
    (hH₁ : (σ.quaternionConjugation hdim hsym).IsAntihermitian H₁) (hu₁ : IsUnit H₁)
    (hc0 : c0 ∈ (σ.quaternionConjugation hdim hsym).alternatingSubspace) (hc0' : c0 ≠ 0)
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (c : (L ≃ₐ[F] L) → (Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D))ˣ) (hc : IsCrossed c)
    (hsu : ∀ s, c s ∈ suGroup (σ.quaternionConjugation hdim hsym) (adjoinSkewLine H₁ c0) L)
    (hloc : IsLocallyCoboundary (σ.quaternionConjugation hdim hsym) (adjoinSkewLine H₁ c0) c) :
    ∃ a ∈ suGroup (σ.quaternionConjugation hdim hsym) (adjoinSkewLine H₁ c0) L,
      ∀ s, c s = a * (unitMap s.toAlgHom a)⁻¹ := by
  set τ := σ.quaternionConjugation hdim hsym
  let : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  set H := adjoinSkewLine H₁ c0 with hHdef
  have hH : τ.IsAntihermitian H := hH₁.adjoinSkewLine hc0
  have hcu : IsUnit c0 := isUnit_iff_ne_zero.mpr hc0'
  have hu : IsUnit H := adjoinSkewLine_isUnit hu₁ hcu
  obtain ⟨d⟩ := exists_gramDescent τ H hc hsu
  have hrep : τ.IsLocallyRepresented d.gram c0 := by
    have h := GramDescent.isLocallyRepresented τ H d hloc (Fin.last m)
    rwa [show H (Fin.last m) (Fin.last m) = c0 from adjoinSkewLine_last H₁ c0] at h
  obtain ⟨yv, hyv⟩ := numberFieldSkewRepresentation F D σ hdim hsym (m + 1)
    (by have := NeZero.ne m; omega) d.gram (GramDescent.gram_antihermitian τ H d hH.1)
    (GramDescent.gram_isUnit τ H d hu) c0 hc0 hc0' hrep
  set Pi : Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D) :=
    ((d.primitive⁻¹ : (Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D))ˣ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D))
  set yL : Fin (m + 1) → L ⊗[F] D := fun j => Algebra.TensorProduct.includeRight (yv j)
  set z := yL ᵥ* Pi
  have hz : (τ.baseChange L).matrixSesqBilin (gramOver (m + 1) H L) z z =
      Algebra.TensorProduct.includeRight c0 := by
    rw [matrixSesqBilin_vecMul, GramDescent.inv_gram_eq τ d, matrixSesqBilin_gramOver, hyv]
  have hlast : (τ.baseChange L).matrixSesqBilin (gramOver (m + 1) H L) (lastRow L) (lastRow L) =
      Algebra.TensorProduct.includeRight c0 := by
    rw [matrixSesqBilin_lastRow]
    simp [gramOver, H, adjoinSkewLine_last]
  have hGanti : (τ.baseChange L).matrix (Fin (m + 1)) (gramOver (m + 1) H L) =
      -gramOver (m + 1) H L := by
    rw [adjoint_gramOver, hH.1]
    ext i j
    simp [gramOver, TensorProduct.tmul_neg]
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap F L).injective
  obtain ⟨w, hwH, hwN, hwx⟩ := hW L (gramOver (m + 1) H L) hGanti (gramOver_isUnit L hu)
    (lastRow L) z (by rw [hlast]; exact hcu.map Algebra.TensorProduct.includeRight)
    (hlast.trans hz.symm)
  have hwSU : w ∈ suGroup τ H L := ⟨hwH, hwN⟩
  have hfix : ∀ s, lastRow L ᵥ* ((w * c s * (unitMap s.toAlgHom w)⁻¹ :
      (Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D))ˣ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D)) = lastRow L := by
    intro s
    have hpc : d.primitive⁻¹ * c s = (unitMap s.toAlgHom d.primitive)⁻¹ := by
      rw [d.coboundary s, ← mul_assoc, inv_mul_cancel, one_mul]
    have hzc : z ᵥ* (c s : Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D)) =
        lastRow L ᵥ* (unitMap s.toAlgHom w : Matrix (Fin (m + 1)) (Fin (m + 1)) (L ⊗[F] D)) := by
      have hyL : vecMap s.toAlgHom yL = yL := vecMap_includeRight s yv
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, hpc, ← coeffMap_units_inv, ← hyL,
        ← vecMap_vecMul]
      change vecMap s.toAlgHom z = _
      rw [← hwx, vecMap_vecMul, vecMap_lastRow]
      rfl
    rw [Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hwx, hzc,
      Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  obtain ⟨c₁, hc₁, hsu₁, hblock⟩ := exists_block_cocycle τ H₁ c0 hcu hc hsu w hwSU hfix
  have hloc₁ : IsLocallyCoboundary τ H₁ c₁ := by
    refine ⟨fun v => ?_, fun v => ?_⟩
    · let : CharZero v.Completion :=
        charZero_of_injective_algebraMap (algebraMap F v.Completion).injective
      exact IsCoboundaryAt.block τ H₁ c0 hcu hH.1 hu w hwSU c₁ hblock _ (hW _) (hloc.1 v)
    · let : CharZero (Global.FiniteCompletion F v) :=
        charZero_of_injective_algebraMap (algebraMap F (Global.FiniteCompletion F v)).injective
      exact IsCoboundaryAt.block τ H₁ c0 hcu hH.1 hu w hwSU c₁ hblock _ (hW _) (hloc.2 v)
  obtain ⟨a₁, ha₁, hcob⟩ := IH H₁ hH₁ hu₁ L c₁ hc₁ hsu₁ hloc₁
  exact exists_coboundary_of_block τ H₁ c0 w hwSU c₁ hblock a₁ ha₁ hcob

end Core

end Langlands.GroupScheme.Quaternionic.SkewUnitary
