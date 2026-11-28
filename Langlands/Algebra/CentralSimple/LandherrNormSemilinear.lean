import Langlands.Algebra.CentralSimple.LandherrNonsplitLocal
import Mathlib.Algebra.MvPolynomial.Funext

/-! # The relative reduced norm is semilinear for an involution of the second kind -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root
open scoped TensorProduct

universe u

variable (F E : Type u) [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F]

/-- The conjugation of `E` extended to `E ⊗_F R`. -/
def tensorConj (R : Type u) [CommRing R] [Algebra F R] : E ⊗[F] R →ₐ[F] E ⊗[F] R :=
  Algebra.TensorProduct.map (conjugation F E).toAlgHom (AlgHom.id F R)

omit [CharZero F] in
@[simp] theorem tensorConj_tmul {R : Type u} [CommRing R] [Algebra F R] (e : E) (r : R) :
    tensorConj F E R (e ⊗ₜ r) = conjugation F E e ⊗ₜ r := rfl

omit [CharZero F] in
theorem tensorConj_naturality {R S : Type u} [CommRing R] [Algebra F R] [CommRing S]
    [Algebra F S] (φ : R →ₐ[F] S) (u : E ⊗[F] R) :
    tensorConj F E S (Algebra.TensorProduct.map (AlgHom.id F E) φ u) =
      Algebra.TensorProduct.map (AlgHom.id F E) φ (tensorConj F E R u) := by
  induction u using TensorProduct.inductionOn with
  | tmul e r => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Every element of `E ⊗_F R` is `1 ⊗ r₁ + r ⊗ r₂`. -/
theorem exists_eq_one_tmul_add_skewRoot_tmul' (R : Type u) [CommRing R] [Algebra F R]
    (z : E ⊗[F] R) : ∃ r₁ r₂ : R, z = (1 : E) ⊗ₜ r₁ + skewRoot F E ⊗ₜ r₂ := by
  induction z using TensorProduct.inductionOn with
  | tmul e k =>
    obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_skewRoot F E e
    refine ⟨algebraMap F R a * k, algebraMap F R b * k, ?_⟩
    have h1 : (algebraMap F E a) ⊗ₜ[F] k = (1 : E) ⊗ₜ[F] (algebraMap F R a * k) := by
      rw [← Algebra.smul_def, Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.smul_tmul]
    have h2 : (algebraMap F E b * skewRoot F E) ⊗ₜ[F] k =
        skewRoot F E ⊗ₜ[F] (algebraMap F R b * k) := by
      rw [← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
    rw [TensorProduct.add_tmul, h1, h2]
  | add x y hx hy =>
    obtain ⟨a₁, a₂, rfl⟩ := hx
    obtain ⟨b₁, b₂, rfl⟩ := hy
    refine ⟨a₁ + b₁, a₂ + b₂, ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel

variable (B : Type u) [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]

omit [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F] in
/-- The relative reduced norm is natural in the coefficient algebra. -/
theorem relNorm_naturality {R S : Type u} [CommRing R] [Algebra F R] [CommRing S]
    [Algebra F S] (φ : R →ₐ[F] S) (z : R ⊗[F] B) :
    relNorm F E B S (Algebra.TensorProduct.map φ (AlgHom.id F B) z) =
      Algebra.TensorProduct.map (AlgHom.id F E) φ (relNorm F E B R z) := by
  unfold relNorm
  rw [UnitaryPoints.tensorEquiv_naturality, reducedNorm_naturality]
  rfl

variable (τ : FirstKindInvolution F B)
  (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))

include hτ in
/-- Suppose `τ` acts on `E` by quadratic conjugation and some field `K` over `F`
in which `d` is nonsquare has the unitary splitting property. For every commutative
`F`-algebra `R`, the relative reduced norm satisfies `ν_R(τ_R z) = σ_R(ν_R z)`. -/
theorem relNorm_baseChange_of_nonsplit (K : Type u) [Field K] [Algebra F K]
    [Fact (¬ IsSquare (algebraMap F K (skewSq F E)))] (hS : UnitaryInvolutionSplitting K)
    (R : Type u) [CommRing R] [Algebra F R] (z : R ⊗[F] B) :
    relNorm F E B R (τ.baseChange R z) = tensorConj F E R (relNorm F E B R z) := by
  classical
  have : FiniteDimensional F E :=
    .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)
  have : FiniteDimensional F B := Module.Finite.trans E B
  let β := Module.finBasis F B
  let P := MvPolynomial (Fin (Module.finrank F B)) F
  let g : P ⊗[F] B := ∑ i, MvPolynomial.X i ⊗ₜ β i
  have hgen : ∀ (S : Type u) [CommRing S] [Algebra F S] (w : S ⊗[F] B),
      ∃ φ : P →ₐ[F] S, Algebra.TensorProduct.map φ (AlgHom.id F B) g = w := by
    intro S _ _ w
    let bS := Algebra.TensorProduct.basis S β
    refine ⟨MvPolynomial.aeval (fun i => bS.repr w i), ?_⟩
    conv_rhs => rw [← bS.sum_repr w]
    simp only [g, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      bS, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.aeval_X]
  let D := relNorm F E B P (τ.baseChange P g) - tensorConj F E P (relNorm F E B P g)
  have hD : ∀ (S : Type u) [CommRing S] [Algebra F S] (φ : P →ₐ[F] S),
      Algebra.TensorProduct.map (AlgHom.id F E) φ D =
        relNorm F E B S (τ.baseChange S (Algebra.TensorProduct.map φ (AlgHom.id F B) g)) -
          tensorConj F E S (relNorm F E B S (Algebra.TensorProduct.map φ (AlgHom.id F B) g)) := by
    intro S _ _ φ
    rw [map_sub, ← tensorConj_naturality, ← relNorm_naturality, ← relNorm_naturality,
      FirstKindInvolution.map_baseChange]
  obtain ⟨D₁, D₂, hD12⟩ := exists_eq_one_tmul_add_skewRoot_tmul' F E P D
  have hK0 : ∀ φ : P →ₐ[F] K, φ D₁ = 0 ∧ φ D₂ = 0 := by
    intro φ
    have h := hD K φ
    rw [relNorm_baseChange_nonsplit F E B K τ hτ hS,
      show centerConj F E K = tensorConj F E K from rfl, sub_self, hD12, map_add,
      Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      AlgHom.id_apply] at h
    have h' := congrArg (nonsplitCenterMap F E K) h
    rw [nonsplitCenterMap_one_add, map_zero] at h'
    exact ⟨congrArg QuadraticAlgebra.re h', congrArg QuadraticAlgebra.im h'⟩
  have : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  have hzero : ∀ Q : P, (∀ φ : P →ₐ[F] K, φ Q = 0) → Q = 0 := by
    intro Q hQ
    apply MvPolynomial.funext
    intro f
    have h := hQ ((Algebra.ofId F K).comp (MvPolynomial.aeval f))
    rw [AlgHom.comp_apply, Algebra.ofId_apply] at h
    rw [map_zero, ← MvPolynomial.coe_aeval_eq_eval]
    exact (algebraMap F K).injective (h.trans (map_zero _).symm)
  have hD0 : D = 0 := by
    rw [hD12, hzero D₁ (fun φ => (hK0 φ).1), hzero D₂ (fun φ => (hK0 φ).2),
      TensorProduct.tmul_zero, TensorProduct.tmul_zero, add_zero]
  obtain ⟨φ, hφ⟩ := hgen R z
  have h := hD R φ
  rw [hD0, map_zero, hφ] at h
  exact (sub_eq_zero.mp h.symm)

end Langlands.CentralSimple.Landherr
