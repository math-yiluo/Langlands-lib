import Langlands.Algebra.CentralSimple.UnitaryPoints
import Langlands.Algebra.CentralSimple.LandherrQuadraticData
import Langlands.Algebra.CentralSimple.LandherrHermitianUnitary
import Langlands.Algebra.CentralSimple.LandherrElementary
import Langlands.Algebra.CentralSimpleScalarExtension
import Langlands.Algebra.UnitaryInvolutionStatements
import Langlands.Shimura.Unitary.HermitianAdjointChart

/-! # Central simple algebras with unitary involution at a nonsplit completion -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root
open scoped TensorProduct

universe u

variable {F E B : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]

variable (F E) (K : Type u) [Field K] [Algebra F K]
  [hK : Fact (¬ IsSquare (algebraMap F K (skewSq F E)))]

/-- The quadratic `K`-algebra with a generator whose square is the image of `d`.
It is a field when `d` has nonsquare image in `K`. -/
abbrev nonsplitField := QuadraticAlgebra K (algebraMap F K (skewSq F E)) 0

omit hK in
theorem omega_mul_omega_nonsplit :
    (QuadraticAlgebra.omega : nonsplitField F E K) * QuadraticAlgebra.omega =
      algebraMap F (nonsplitField F E K) (skewSq F E) := by
  rw [QuadraticAlgebra.omega_mul_omega_eq_add, zero_smul, add_zero,
    IsScalarTower.algebraMap_apply F K (nonsplitField F E K), Algebra.smul_def, mul_one]

/-- The embedding `E → K(√d)` sending the skew root to `ω`. -/
def nonsplitEmbedding : E →ₐ[F] nonsplitField F E K :=
  liftSkew F E QuadraticAlgebra.omega (omega_mul_omega_nonsplit F E K)

@[simp] theorem nonsplitEmbedding_skewRoot :
    nonsplitEmbedding F E K (skewRoot F E) = QuadraticAlgebra.omega :=
  liftSkew_skewRoot F E _ _

/-- `K(√d)` as an `E`-algebra through `nonsplitEmbedding`. -/
@[instance_reducible] def nonsplitAlgebra : Algebra E (nonsplitField F E K) :=
  (nonsplitEmbedding F E K).toRingHom.toAlgebra

attribute [local instance] nonsplitAlgebra

theorem algebraMap_nonsplit (e : E) :
    algebraMap E (nonsplitField F E K) e = nonsplitEmbedding F E K e := rfl

theorem nonsplit_isScalarTower : IsScalarTower F E (nonsplitField F E K) :=
  IsScalarTower.of_algebraMap_eq fun x => ((nonsplitEmbedding F E K).commutes x).symm

theorem nonsplit_smulCommClass : SMulCommClass E K (nonsplitField F E K) where
  smul_comm e k x := by
    simp only [Algebra.smul_def]
    ring

attribute [local instance] nonsplit_isScalarTower nonsplit_smulCommClass

variable (B)

/-- The scalar extension `K(√d) ⊗_E B`. -/
abbrev nonsplitAlg := nonsplitField F E K ⊗[E] B

/-- The map `K ⊗_F B → K(√d) ⊗_E B`, `k ⊗ b ↦ k ⊗ b`. -/
def nonsplitMap : K ⊗[F] B →ₐ[K] nonsplitAlg F E B K :=
  Algebra.TensorProduct.lift (Algebra.ofId K _)
    ((Algebra.TensorProduct.includeRight : B →ₐ[E] nonsplitAlg F E B K).restrictScalars F)
    (fun k b => by
      change Commute (algebraMap K _ k) _
      exact Algebra.commutes k _)

@[simp] theorem nonsplitMap_tmul (k : K) (b : B) :
    nonsplitMap F E B K (k ⊗ₜ[F] b) = algebraMap K (nonsplitField F E K) k ⊗ₜ[E] b := by
  simp [nonsplitMap, Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply]

theorem nonsplitMap_surjective : Function.Surjective (nonsplitMap F E B K) := by
  rw [← AlgHom.range_eq_top, eq_top_iff]
  intro z _hz
  clear _hz
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => exact Subalgebra.add_mem _ hx hy
  | tmul l b =>
    have h1 : ∀ k : K, algebraMap K (nonsplitField F E K) k ⊗ₜ[E] b ∈
        (nonsplitMap F E B K).range := fun k => ⟨k ⊗ₜ b, nonsplitMap_tmul F E B K k b⟩
    have h2 : ∀ k : K, (algebraMap K (nonsplitField F E K) k * QuadraticAlgebra.omega) ⊗ₜ[E] b ∈
        (nonsplitMap F E B K).range := fun k => by
      refine ⟨k ⊗ₜ (skewRoot F E • b), ?_⟩
      change nonsplitMap F E B K (k ⊗ₜ (skewRoot F E • b)) = _
      rw [nonsplitMap_tmul, ← TensorProduct.smul_tmul, Algebra.smul_def, algebraMap_nonsplit,
        nonsplitEmbedding_skewRoot, mul_comm]
    rw [← QuadraticAlgebra.re_smul_add_im_smul l, TensorProduct.add_tmul]
    refine Subalgebra.add_mem _ ?_ ?_
    · rw [Algebra.smul_def, mul_one]; exact h1 _
    · rw [Algebra.smul_def]; exact h2 _

theorem finrank_nonsplitAlg :
    Module.finrank K (nonsplitAlg F E B K) = Module.finrank K (K ⊗[F] B) := by
  have : FiniteDimensional F E :=
    .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)
  have : FiniteDimensional F B := Module.Finite.trans E B
  calc Module.finrank K (nonsplitAlg F E B K)
      = Module.finrank K (nonsplitField F E K) *
          Module.finrank (nonsplitField F E K) (nonsplitAlg F E B K) :=
        (Module.finrank_mul_finrank K (nonsplitField F E K) _).symm
    _ = 2 * Module.finrank E B := by
        rw [QuadraticAlgebra.finrank_eq_two, Module.finrank_baseChange]
    _ = Module.finrank F E * Module.finrank E B := by
        rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]
    _ = Module.finrank F B := Module.finrank_mul_finrank F E B
    _ = Module.finrank K (K ⊗[F] B) := Module.finrank_baseChange.symm

theorem nonsplitMap_bijective : Function.Bijective (nonsplitMap F E B K) := by
  have : FiniteDimensional F E :=
    .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)
  have : FiniteDimensional F B := Module.Finite.trans E B
  have : FiniteDimensional K (nonsplitAlg F E B K) :=
    Module.Finite.trans (nonsplitField F E K) _
  refine ⟨?_, nonsplitMap_surjective F E B K⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (nonsplitMap F E B K).toLinearMap) (finrank_nonsplitAlg F E B K).symm).mpr
    (nonsplitMap_surjective F E B K)

/-- `K ⊗_F B ≃ K(√d) ⊗_E B`. -/
def nonsplitEquiv : K ⊗[F] B ≃ₐ[K] nonsplitAlg F E B K :=
  AlgEquiv.ofBijective _ (nonsplitMap_bijective F E B K)

@[simp] theorem nonsplitEquiv_tmul (k : K) (b : B) :
    nonsplitEquiv F E B K (k ⊗ₜ[F] b) = algebraMap K (nonsplitField F E K) k ⊗ₜ[E] b :=
  nonsplitMap_tmul F E B K k b

/-- The conjugation `x + yω ↦ x - yω` of `K(√d)`. -/
def nonsplitConj : nonsplitField F E K ≃ₐ[K] nonsplitField F E K :=
  AlgEquiv.ofRingEquiv (f := starRingAut) (fun k => by
    ext <;> simp [Algebra.algebraMap_eq_smul_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_one])

omit hK in
@[simp] theorem nonsplitConj_apply (x : nonsplitField F E K) : nonsplitConj F E K x = star x :=
  rfl

omit hK in
theorem nonsplitConj_omega :
    nonsplitConj F E K QuadraticAlgebra.omega = -QuadraticAlgebra.omega := by
  ext <;> simp

omit hK in
theorem nonsplitConj_ne_one : nonsplitConj F E K ≠ 1 := by
  intro h
  have h1 := congrArg (fun f => f (QuadraticAlgebra.omega : nonsplitField F E K)) h
  simp only [nonsplitConj_omega, AlgEquiv.one_apply] at h1
  have hK0 : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have := congrArg QuadraticAlgebra.im h1
  simp at this
  norm_num at this

theorem nonsplitConj_embedding (e : E) :
    nonsplitConj F E K (nonsplitEmbedding F E K e) =
      nonsplitEmbedding F E K (conjugation F E e) := by
  obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_skewRoot F E e
  simp only [map_add, map_mul, AlgHom.commutes, AlgEquiv.commutes, nonsplitEmbedding_skewRoot,
    conjugation_skewRoot, nonsplitConj_omega, map_neg, mul_neg]
  rw [IsScalarTower.algebraMap_apply F K (nonsplitField F E K),
    IsScalarTower.algebraMap_apply F K (nonsplitField F E K), AlgEquiv.commutes,
    AlgEquiv.commutes]

theorem nonsplitEquiv_tmul_skewRoot (k : K) :
    nonsplitEquiv F E B K (k ⊗ₜ[F] algebraMap E B (skewRoot F E)) =
      algebraMap (nonsplitField F E K) (nonsplitAlg F E B K)
        (algebraMap K (nonsplitField F E K) k * QuadraticAlgebra.omega) := by
  rw [nonsplitEquiv_tmul, Algebra.TensorProduct.algebraMap_apply,
    show algebraMap E B (skewRoot F E) = skewRoot F E • (1 : B) from
      Algebra.algebraMap_eq_smul_one _,
    ← TensorProduct.smul_tmul, Algebra.smul_def, algebraMap_nonsplit, nonsplitEmbedding_skewRoot,
    mul_comm]
  rfl

theorem nonsplitEquiv_tmul_one (k : K) :
    nonsplitEquiv F E B K (k ⊗ₜ[F] (1 : B)) =
      algebraMap (nonsplitField F E K) (nonsplitAlg F E B K) (algebraMap K (nonsplitField F E K) k) := by
  rw [nonsplitEquiv_tmul]
  rfl

theorem nonsplitEquiv_symm_algebraMap (l : nonsplitField F E K) :
    (nonsplitEquiv F E B K).symm (algebraMap (nonsplitField F E K) (nonsplitAlg F E B K) l) =
      l.re ⊗ₜ[F] (1 : B) + l.im ⊗ₜ[F] algebraMap E B (skewRoot F E) := by
  rw [AlgEquiv.symm_apply_eq, map_add, nonsplitEquiv_tmul_one, nonsplitEquiv_tmul_skewRoot,
    ← map_add]
  congr 1
  conv_lhs => rw [← QuadraticAlgebra.re_smul_add_im_smul l]
  rw [Algebra.smul_def, Algebra.smul_def, mul_one]

variable (τ : FirstKindInvolution F B)

/-- The involution `id ⊗ τ` transported to `K(√d) ⊗_E B`. -/
def nonsplitInvolution (z : nonsplitAlg F E B K) : nonsplitAlg F E B K :=
  nonsplitEquiv F E B K (τ.baseChange K ((nonsplitEquiv F E B K).symm z))

theorem nonsplitInvolution_equiv (x : K ⊗[F] B) :
    nonsplitInvolution F E B K τ (nonsplitEquiv F E B K x) =
      nonsplitEquiv F E B K (τ.baseChange K x) := by
  simp [nonsplitInvolution]

variable (hτ : ∀ e : E, τ (algebraMap E B e) = algebraMap E B (conjugation F E e))

include hτ in
theorem nonsplitInvolution_isUnitary :
    IsUnitaryInvolution (nonsplitConj F E K) (nonsplitInvolution F E B K τ) := by
  refine ⟨fun x y => ?_, fun x y => ?_, fun x => ?_, fun l => ?_⟩
  · simp [nonsplitInvolution]
  · simp [nonsplitInvolution]
  · simp [nonsplitInvolution]
  · rw [nonsplitInvolution, nonsplitEquiv_symm_algebraMap, map_add,
      FirstKindInvolution.baseChange_tmul, FirstKindInvolution.baseChange_tmul,
      FirstKindInvolution.map_one, hτ, conjugation_skewRoot, map_neg, TensorProduct.tmul_neg,
      map_add, map_neg, nonsplitEquiv_tmul_one, nonsplitEquiv_tmul_skewRoot, ← map_neg, ← map_add]
    congr 1
    conv_rhs => rw [← QuadraticAlgebra.re_smul_add_im_smul l]
    rw [map_add, map_smul, map_smul, map_one, nonsplitConj_omega, Algebra.smul_def,
      Algebra.smul_def, mul_one, mul_neg]

end Langlands.CentralSimple.Landherr
