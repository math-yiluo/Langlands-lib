import Langlands.GroupScheme.Quaternionic.SkewHermitianOrthogonalBasis
import Langlands.GroupScheme.Rational.NumberFieldHermitianGram
import Langlands.GroupScheme.Examples.SU3RootHeisenbergComparison

/-! # Gram matrices of Hermitian forms over a quadratic field -/

noncomputable section

universe u v w

open Matrix

namespace Langlands.GroupScheme.Quaternionic.HermitianPairing

open HermitianMatrix SU3Root

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
  {V : Type v} [AddCommGroup V] [Module E V]

local notation "κ" => SU3Root.conjugation F E
local notation "τ" => quadraticConjugationInvolution F E

variable (G : V →ₗ[E] (V →ₛₗ[(SU3Root.conjugation F E).toRingHom] E))

section Restriction

variable [Module F V] [IsScalarTower F E V]

/-- A Hermitian pairing times a skew scalar can be treated as an antihermitian
  form for the quadratic field involution. -/
def toAntihermitian (r : E) (hr : κ r = -r) (hG : ∀ x y, κ (G x y) = G y x) :
    AntihermitianForm τ V where
  toBilin := LinearMap.mk₂ F (fun x y => r * G x y)
    (fun x y z => by rw [G.map_add, LinearMap.add_apply, mul_add])
    (fun a x y => by
      rw [← IsScalarTower.algebraMap_smul E a x, G.map_smul, LinearMap.smul_apply]
      simp only [smul_eq_mul, Algebra.smul_def]
      ring)
    (fun x y z => by rw [(G x).map_add, mul_add])
    (fun a x y => by
      rw [← IsScalarTower.algebraMap_smul E a y, (G x).map_smulₛₗ]
      change r * (κ (algebraMap F E a) * G x y) = a • (r * G x y)
      rw [AlgEquiv.commutes, Algebra.smul_def]
      ring)
  smul_left' a x y := by
    change r * G (a • x) y = a * (r * G x y)
    rw [G.map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  skew' x y := by
    change r * G y x = -(κ (r * G x y))
    rw [map_mul, hr, hG, neg_mul, neg_neg]

@[simp]
theorem toAntihermitian_apply (r : E) (hr : κ r = -r) (hG : ∀ x y, κ (G x y) = G y x)
    (x y : V) : toAntihermitian G r hr hG x y = r * G x y := rfl

/-- Multiplication by a nonzero skew scalar preserves left separation. -/
theorem toAntihermitian_separating (r : E) (hr : κ r = -r) (hG : ∀ x y, κ (G x y) = G y x)
    (hr0 : r ≠ 0) (hsep : ∀ x, (∀ y, G x y = 0) → x = 0) :
    (toAntihermitian G r hr hG).toBilin.SeparatingLeft := by
  intro x hx
  apply hsep x
  intro y
  exact (mul_eq_zero.mp (hx y)).resolve_left hr0

/-- Orthogonalize a left-separating Hermitian pairing using the antihermitian
  Gram–Schmidt construction after multiplication by a skew scalar. -/
theorem exists_orthogonalBasis [FiniteDimensional E V] {n : ℕ} (hn : Module.finrank E V = n)
    (hG : ∀ x y, κ (G x y) = G y x) (hsep : ∀ x, (∀ y, G x y = 0) → x = 0) :
    ∃ b : Module.Basis (Fin n) E V, (∀ i j, i ≠ j → G (b i) (b j) = 0) ∧
      (∀ i, G (b i) (b i) ≠ 0) := by
  obtain ⟨r, hr0, hr⟩ := exists_ne_zero_add_conjugation_eq_zero F E
  have hr' : κ r = -r := eq_neg_of_add_eq_zero_right hr
  obtain ⟨a, ha⟩ := exists_conjugation_ne F E
  let A := toAntihermitian G r hr' hG
  obtain ⟨b, hb, hd⟩ := AntihermitianForm.orthogonalBasis F E τ V A ⟨a, ha⟩
    (toAntihermitian_separating G r hr' hG hr0 hsep)
  let c := b.reindex (finCongr hn)
  refine ⟨c, ?_, ?_⟩
  · intro i j hij
    have he := hb ((finCongr hn).symm i) ((finCongr hn).symm j) ((finCongr hn).symm.injective.ne hij)
    simpa only [c, Module.Basis.reindex_apply] using (mul_eq_zero.mp he).resolve_left hr0
  · intro i hi
    apply hd ((finCongr hn).symm i)
    change r * G (b ((finCongr hn).symm i)) (b ((finCongr hn).symm i)) = 0
    simp only [c, Module.Basis.reindex_apply] at hi
    rw [hi, mul_zero]

end Restriction

section Gram

variable {I : Type w} (b c : Module.Basis I E V)

/-- The Hermitian Gram matrix with the linear argument indexing its rows. -/
def gram : Matrix I I E := fun i j => G (b i) (b j)

@[simp] theorem gram_apply (i j : I) : gram G b i j = G (b i) (b j) := rfl

/-- Orthogonal bases give the diagonal of self-values. -/
theorem gram_eq_diagonal [DecidableEq I] (hb : ∀ i j, i ≠ j → G (b i) (b j) = 0) :
    gram G b = Matrix.diagonal (fun i => G (b i) (b i)) := by
  apply Matrix.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp
  · rw [gram_apply, Matrix.diagonal_apply_ne _ h]
    exact hb i j h

variable [Fintype I]

/-- The two basis coefficients in a Hermitian pairing differ by conjugation. -/
theorem apply_eq_sum_repr (x y : V) :
    G x y = ∑ i, ∑ j, b.repr x i * G (b i) (b j) * κ (b.repr y j) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.map_smulₛₗ, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change κ (b.repr y i) * (b.repr x j * G (b j) (b i)) = _
  ring

/-- The basis change of the Gram matrix uses ordinary transpose on the linear
  side and coefficient conjugation on the semilinear side. -/
theorem gram_change_basis :
    gram G c = (b.toMatrix c)ᵀ * (gram G b * (b.toMatrix c).map (κ).toRingHom) := by
  apply Matrix.ext
  intro i j
  rw [gram_apply G, apply_eq_sum_repr G b]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Module.Basis.toMatrix_apply,
    gram_apply, Finset.mul_sum, mul_assoc]
  rfl

variable [DecidableEq I]

/-- The Hermitian Gram determinant changes by a quadratic norm. -/
theorem det_gram_change_basis :
    (gram G c).det = (gram G b).det * ((b.toMatrix c).det * κ (b.toMatrix c).det) := by
  have hmap : ((b.toMatrix c).map (κ).toRingHom).det = κ (b.toMatrix c).det :=
    ((κ).toRingHom.map_det _).symm
  rw [gram_change_basis G b c, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmap]
  ring

/-- The determinant is the product of the nonzero diagonal entries in an orthogonal basis. -/
theorem det_gram_eq_prod (hb : ∀ i j, i ≠ j → G (b i) (b j) = 0) :
    (gram G b).det = ∏ i, G (b i) (b i) := by
  rw [gram_eq_diagonal G b hb, Matrix.det_diagonal]

end Gram

end Langlands.GroupScheme.Quaternionic.HermitianPairing
