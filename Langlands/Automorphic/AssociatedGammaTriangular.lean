import Langlands.Weil.Local.DegreeFrobenius
import Langlands.Group.LieKolchin.Triangularization
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Langlands.Weil.Local.Assembly
import Langlands.LocalFactor.Euler.Definitions
import Mathlib.RepresentationTheory.Basic
import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof

/-!
# Simultaneous triangularization of a cyclic matrix group

Every homomorphism `ℤ → GL_n(ℂ)` is conjugate to one with upper triangular values. This is
the cyclic case of the Lie–Kolchin argument of `Langlands.LieKolchin.exists_triangularizing`,
where the common eigenvector is an eigenvector of the generator.
-/

noncomputable section

set_option autoImplicit false

open scoped Matrix

namespace Langlands.LieKolchin

open Langlands.Algebra.GradedHopf.Triangular

/-- A homomorphism from `ℤ` into matrices has a common eigenvector. -/
theorem exists_mulVec_eigenvector_cyclic {n : ℕ}
    (ρ : Multiplicative ℤ →* Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ v : Fin (n + 1) → ℂ, v ≠ 0 ∧ ∀ g, ∃ c : ℂ, ρ g *ᵥ v = c • v := by
  let A := ρ (Multiplicative.ofAdd 1)
  let B := ρ (Multiplicative.ofAdd (-1))
  have hAB : B * A = 1 := by
    rw [← map_mul, ← ofAdd_add, neg_add_cancel, ofAdd_zero, map_one]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hAv : A *ᵥ v = c • v := by
    have := hv.apply_eq_smul
    rwa [Matrix.toLin'_apply] at this
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : B *ᵥ (A *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
    rw [hAv, h0, zero_smul, Matrix.mulVec_zero] at h1
    exact hv.2 h1.symm
  have hBv : B *ᵥ v = c⁻¹ • v := by
    have h1 : B *ᵥ (A *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
    rw [hAv, Matrix.mulVec_smul] at h1
    calc B *ᵥ v = c⁻¹ • (c • B *ᵥ v) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • v := by rw [h1]
  refine ⟨v, hv.2, fun g => ?_⟩
  induction g using Multiplicative.rec with
  | ofAdd k =>
    induction k using Int.induction_on with
    | zero => exact ⟨1, by rw [ofAdd_zero, map_one, Matrix.one_mulVec, one_smul]⟩
    | succ k ih =>
      obtain ⟨d, hd⟩ := ih
      refine ⟨d * c, ?_⟩
      rw [ofAdd_add, map_mul, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, hd, smul_smul,
        mul_comm]
    | pred k ih =>
      obtain ⟨d, hd⟩ := ih
      refine ⟨d * c⁻¹, ?_⟩
      rw [sub_eq_add_neg, ofAdd_add, map_mul, ← Matrix.mulVec_mulVec, hBv, Matrix.mulVec_smul,
        hd, smul_smul, mul_comm]

/-- **Cyclic triangularization.** Every homomorphism `ℤ → M_n(ℂ)` is conjugate to one with
upper triangular values. -/
theorem exists_triangularizing_cyclic :
    ∀ (n : ℕ) (ρ : Multiplicative ℤ →* Matrix (Fin n) (Fin n) ℂ),
      ∃ P Q : Matrix (Fin n) (Fin n) ℂ, P * Q = 1 ∧
        ∀ g (i j : Fin n), j < i → (Q * ρ g * P) i j = 0 := by
  intro n
  induction n with
  | zero =>
    intro ρ
    exact ⟨1, 1, Matrix.mul_one 1, fun _ i => i.elim0⟩
  | succ n ih =>
    intro ρ
    obtain ⟨v, hv0, hv⟩ := exists_mulVec_eigenvector_cyclic ρ
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hv0
    set P₁ := stepP v i₀
    set Q₁ := stepQ v i₀
    have hQP : Q₁ * P₁ = 1 := stepQ_mul_stepP v i₀ hi₀
    have hPQ : P₁ * Q₁ = 1 := mul_eq_one_comm.1 hQP
    let B : Multiplicative ℤ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun g => Q₁ * ρ g * P₁
    have hB0 : ∀ g (i : Fin n), B g i.succ 0 = 0 := by
      intro g i
      obtain ⟨c, hc⟩ := hv g
      have hQv : Q₁ *ᵥ v = fun i => (Q₁ * P₁) i 0 := by
        ext l
        rw [mul_stepP_apply_zero]
      change (Q₁ * ρ g * stepP v i₀) i.succ 0 = 0
      rw [mul_stepP_apply_zero, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hQv, hQP]
      simp [Matrix.one_apply_ne (Fin.succ_ne_zero i)]
    have hBmul : ∀ g h, B (g * h) = B g * B h := by
      intro g h
      simp only [B, map_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P₁ Q₁, hPQ, Matrix.one_mul]
    let ρ₂ : Multiplicative ℤ →* Matrix (Fin n) (Fin n) ℂ :=
      { toFun := fun g => (B g).submatrix Fin.succ Fin.succ
        map_one' := by
          simp only [B, map_one, Matrix.mul_one, hQP]
          exact Matrix.submatrix_one _ (Fin.succ_injective _)
        map_mul' := fun g h => by
          ext i j
          simp [hBmul, Matrix.mul_apply, Fin.sum_univ_succ, hB0] }
    obtain ⟨P₂, Q₂, hPQ₂, htri⟩ := ih ρ₂
    refine ⟨P₁ * ext1 P₂, ext1 Q₂ * Q₁, ?_, fun g i j hji => ?_⟩
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (ext1 P₂), ext1_mul, hPQ₂, ext1_one,
        Matrix.one_mul, hPQ]
    · have hE : ext1 Q₂ * Q₁ * ρ g * (P₁ * ext1 P₂) = ext1 Q₂ * B g * ext1 P₂ := by
        simp only [B, Matrix.mul_assoc]
      rw [hE]
      induction i using Fin.cases with
      | zero => exact absurd hji (Fin.not_lt_zero j)
      | succ i =>
        induction j using Fin.cases with
        | zero => exact ext1_mul_mul_succ_zero Q₂ P₂ (B g) (hB0 g) i
        | succ j =>
          rw [ext1_mul_mul_succ_succ]
          exact htri g i j (Fin.succ_lt_succ_iff.1 hji)

end Langlands.LieKolchin

namespace Langlands.Weil.Local

open Polynomial

universe u

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)
  {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- An unramified representation of the local Weil group is a power of its value at the
geometric Frobenius. -/
theorem representation_eq_frobenius_zpow (ρ : Representation ℂ (localWeilGroup K) V)
    (hI : ∀ i ∈ localInertia K, ρ i = 1) (g : localWeilGroup K) :
    ρ g = ((MonoidHom.toHomUnits ρ (localGeometricFrobenius K) ^ localDegreeInt K g :
      (Module.End ℂ V)ˣ) : Module.End ℂ V) := by
  set k := localDegreeInt K g
  have hdeg : localDegree K ((localGeometricFrobenius K ^ k)⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, map_zpow, localGeometricFrobenius_degree]
    have hg : localDegree K g = Multiplicative.ofAdd k := rfl
    rw [hg, ← ofAdd_zsmul, smul_eq_mul, mul_one, inv_mul_cancel]
  have hmem : (localGeometricFrobenius K ^ k)⁻¹ * g ∈ localInertia K := hdeg
  have h1 := hI _ hmem
  have hg : g = localGeometricFrobenius K ^ k * ((localGeometricFrobenius K ^ k)⁻¹ * g) := by
    rw [mul_inv_cancel_left]
  conv_lhs => rw [hg]
  rw [map_mul, h1, mul_one, ← MonoidHom.coe_toHomUnits, map_zpow]

/-- **Triangular basis** of an unramified representation of the local Weil group: every Weil
element acts by an upper triangular matrix, with diagonal entries `d_i ^ deg g`. -/
theorem exists_triangular_basis {n : ℕ} (hn : Module.finrank ℂ V = n)
    (ρ : Representation ℂ (localWeilGroup K) V) (hI : ∀ i ∈ localInertia K, ρ i = 1) :
    ∃ (b : Module.Basis (Fin n) ℂ V) (d : Fin n → ℂˣ), ∀ g : localWeilGroup K,
      (∀ i j : Fin n, j < i → b.repr (ρ g (b j)) i = 0) ∧
      ∀ i : Fin n, b.repr (ρ g (b i)) i = ((d i ^ localDegreeInt K g : ℂˣ) : ℂ) := by
  classical
  let e : Module.Basis (Fin n) ℂ V := (Module.finBasis ℂ V).reindex (finCongr hn)
  let u := MonoidHom.toHomUnits ρ (localGeometricFrobenius K)
  let ρℤ : Multiplicative ℤ →* Matrix (Fin n) (Fin n) ℂ :=
    (LinearMap.toMatrixAlgEquiv e).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom _).comp (zpowersHom _ u))
  have hρℤ : ∀ k : ℤ, ρℤ (Multiplicative.ofAdd k) =
      LinearMap.toMatrixAlgEquiv e ((u ^ k : (Module.End ℂ V)ˣ) : Module.End ℂ V) := by
    intro k
    simp only [ρℤ, MonoidHom.comp_apply, zpowersHom_apply, toAdd_ofAdd, Units.coeHom_apply]
    rfl
  obtain ⟨P, Q, hPQ, htri⟩ := LieKolchin.exists_triangularizing_cyclic n ρℤ
  have hQP : Q * P = 1 := mul_eq_one_comm.mp hPQ
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.End ℂ V, LinearMap.toMatrixAlgEquiv e φ = P :=
    (LinearMap.toMatrixAlgEquiv e).surjective P
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.End ℂ V, LinearMap.toMatrixAlgEquiv e ψ = Q :=
    (LinearMap.toMatrixAlgEquiv e).surjective Q
  have hφψ : φ ∘ₗ ψ = LinearMap.id := by
    apply (LinearMap.toMatrixAlgEquiv e).injective
    rw [LinearMap.toMatrixAlgEquiv_comp, hφ, hψ, hPQ, LinearMap.toMatrixAlgEquiv_id]
  have hψφ : ψ ∘ₗ φ = LinearMap.id := by
    apply (LinearMap.toMatrixAlgEquiv e).injective
    rw [LinearMap.toMatrixAlgEquiv_comp, hφ, hψ, hQP, LinearMap.toMatrixAlgEquiv_id]
  let b := e.map (LinearEquiv.ofLinearMap φ ψ hφψ hψφ)
  have hrepr : ∀ (M : Module.End ℂ V) (i j : Fin n),
      b.repr (M (b j)) i = (Q * LinearMap.toMatrixAlgEquiv e M * P) i j := by
    intro M i j
    rw [← hφ, ← hψ, ← LinearMap.toMatrixAlgEquiv_comp, ← LinearMap.toMatrixAlgEquiv_comp,
      LinearMap.toMatrixAlgEquiv_apply, Module.Basis.map_repr, Module.Basis.map_apply]
    rfl
  have hρg : ∀ g, LinearMap.toMatrixAlgEquiv e (ρ g) =
      ρℤ (Multiplicative.ofAdd (localDegreeInt K g)) := by
    intro g
    rw [hρℤ, representation_eq_frobenius_zpow K ρ hI g]
  let D : Multiplicative ℤ → Matrix (Fin n) (Fin n) ℂ := fun g => Q * ρℤ g * P
  have hDmul : ∀ g h, D (g * h) = D g * D h := by
    intro g h
    simp only [D, map_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P Q, hPQ, Matrix.one_mul]
  have hdiag : ∀ g h (i : Fin n), D (g * h) i i = D g i i * D h i i := by
    intro g h i
    rw [hDmul, Matrix.mul_apply, Finset.sum_eq_single i]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h1 | h1
      · rw [show D g i l = 0 from htri g i l h1, zero_mul]
      · rw [show D h l i = 0 from htri h l i h1, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hD1 : ∀ i : Fin n, D 1 i i = 1 := by
    intro i
    simp [D, hQP]
  let dU : Fin n → Multiplicative ℤ →* ℂ := fun i =>
    { toFun := fun g => D g i i
      map_one' := hD1 i
      map_mul' := fun g h => hdiag g h i }
  refine ⟨b, fun i => MonoidHom.toHomUnits (dU i) (Multiplicative.ofAdd 1), fun g =>
    ⟨fun i j hji => ?_, fun i => ?_⟩⟩
  · rw [hrepr, hρg]
    exact htri _ i j hji
  · rw [hrepr, hρg, ← map_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one, MonoidHom.coe_toHomUnits]
    rfl

/-- The Euler polynomial of an operator with upper triangular matrix in a basis is the product
of the linear factors of its diagonal entries. -/
theorem eulerPolynomial_of_triangular {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (A : Module.End ℂ V) (htri : ∀ i j : Fin n, j < i → b.repr (A (b j)) i = 0) :
    LocalFactor.eulerPolynomial A = ∏ i, (1 - C (b.repr (A (b i)) i) * X) := by
  classical
  rw [LocalFactor.eulerPolynomial_eq_det A b, Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, Matrix.map_apply,
      LinearMap.toMatrix_apply, smul_eq_mul]
    rw [mul_comm]
  · intro i j hij
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply,
      LinearMap.toMatrix_apply, htri i j hij, map_zero, smul_eq_mul, mul_zero, sub_zero]
    exact Matrix.one_apply_ne (ne_of_gt hij)

/-- Two tuples with the same unordered spectrum differ by a permutation. -/
theorem _root_.Langlands.Unramified.Eigenvalues.exists_perm_of_ofTuple_eq {n : ℕ}
    {d z : Fin n → ℂˣ}
    (h : Unramified.Eigenvalues.ofTuple d = Unramified.Eigenvalues.ofTuple z) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, d i = z (σ i) := by
  classical
  have hm : (Finset.univ.val.map d : Multiset ℂˣ) = Finset.univ.val.map z := by
    have h1 := congrArg (fun s : Unramified.Eigenvalues n => (s : Multiset ℂˣ)) h
    change (List.ofFn d : Multiset ℂˣ) = (List.ofFn z : Multiset ℂˣ) at h1
    rw [← Fin.univ_val_map, ← Fin.univ_val_map] at h1
    exact h1
  have hcount : ∀ (f : Fin n → ℂˣ) (c : ℂˣ),
      Fintype.card {i // f i = c} = Multiset.count c (Finset.univ.val.map f) := by
    intro f c
    rw [Fintype.card_subtype, Multiset.count_map]
    simp only [Finset.card, Finset.filter_val, eq_comm]
  let e : ∀ c : ℂˣ, {i // d i = c} ≃ {j // z j = c} := fun c =>
    Fintype.equivOfCardEq (by rw [hcount, hcount, hm])
  exact ⟨Equiv.ofFiberEquiv e, fun i => (Equiv.ofFiberEquiv_map e i).symm⟩

/-- **Triangular basis with prescribed spectrum.** For an unramified representation whose
Frobenius Euler polynomial is `∏ (1 - z_i X)`, some basis makes every Weil element act upper
triangularly with diagonal entries `z_(σ i) ^ deg g`, for a permutation `σ`. -/
theorem exists_triangular_basis_of_eulerPolynomial {n : ℕ} (hn : Module.finrank ℂ V = n)
    (ρ : Representation ℂ (localWeilGroup K) V) (hI : ∀ i ∈ localInertia K, ρ i = 1)
    (z : Fin n → ℂˣ)
    (hz : LocalFactor.eulerPolynomial (ρ (localGeometricFrobenius K)) =
      ∏ i, (1 - C (z i : ℂ) * X)) :
    ∃ (b : Module.Basis (Fin n) ℂ V) (σ : Equiv.Perm (Fin n)), ∀ g : localWeilGroup K,
      (∀ i j : Fin n, j < i → b.repr (ρ g (b j)) i = 0) ∧
      ∀ i : Fin n, b.repr (ρ g (b i)) i = ((z (σ i) ^ localDegreeInt K g : ℂˣ) : ℂ) := by
  obtain ⟨b, d, hb⟩ := exists_triangular_basis K hn ρ hI
  have hE := eulerPolynomial_of_triangular b (ρ (localGeometricFrobenius K))
    (hb (localGeometricFrobenius K)).1
  simp only [(hb (localGeometricFrobenius K)).2, localDegreeInt_localGeometricFrobenius,
    zpow_one] at hE
  have hspec : Unramified.Eigenvalues.ofTuple d = Unramified.Eigenvalues.ofTuple z := by
    apply Unramified.Eigenvalues.eulerPolynomial_injective
    rw [Unramified.Eigenvalues.eulerPolynomial_ofTuple,
      Unramified.Eigenvalues.eulerPolynomial_ofTuple, ← hE, hz]
  obtain ⟨σ, hσ⟩ := Unramified.Eigenvalues.exists_perm_of_ofTuple_eq hspec
  refine ⟨b, σ, fun g => ⟨(hb g).1, fun i => ?_⟩⟩
  rw [(hb g).2, hσ]

end Langlands.Weil.Local
