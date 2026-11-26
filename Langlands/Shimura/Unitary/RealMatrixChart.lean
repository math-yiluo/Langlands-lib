import Langlands.Shimura.Unitary.FiniteModels
import Langlands.Algebra.CentralSimpleScalarExtension
import Langlands.Algebra.CentralSimple.SeparablyClosedSplitting
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Actual complex matrix coordinates at a real embedding -/

noncomputable section

universe u v w

namespace Langlands.Shimura

open NumberField _root_.Algebra
open scoped TensorProduct

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]

/-- A complex embedding of the CM field above the supplied real embedding. -/
def embeddingOverReal (τ : E →+* ℝ) : K →+* ℂ :=
  letI : Algebra E ℂ := (Complex.ofRealHom.comp τ).toAlgebra
  (IsAlgClosed.lift : K →ₐ[E] ℂ).toRingHom

omit [IsTotallyReal E] [IsTotallyComplex K] in
@[simp] theorem embeddingOverReal_apply_algebraMap (τ : E →+* ℝ) (x : E) :
    embeddingOverReal (K := K) τ (algebraMap E K x) = (τ x : ℂ) :=
  letI : Algebra E ℂ := (Complex.ofRealHom.comp τ).toAlgebra
  (IsAlgClosed.lift : K →ₐ[E] ℂ).commutes x

namespace FiniteUnitary

variable (τ : E →+* ℝ)

private def realCenterMap :
    letI : Algebra E ℝ := τ.toAlgebra
    ℝ ⊗[E] K →ₐ[ℝ] ℂ :=
  letI : Algebra E ℝ := τ.toAlgebra
  letI : Algebra E ℂ := (Complex.ofRealHom.comp τ).toAlgebra
  letI : IsScalarTower E ℝ ℂ := IsScalarTower.of_algebraMap_eq' rfl
  Algebra.TensorProduct.lift (Algebra.ofId ℝ ℂ)
    ({ embeddingOverReal τ with commutes' := embeddingOverReal_apply_algebraMap τ } : K →ₐ[E] ℂ)
    (fun _ _ => Commute.all _ _)

omit [IsTotallyReal E] [IsTotallyComplex K] in
private theorem realCenterMap_tmul (s : ℝ) (k : K) :
    letI : Algebra E ℝ := τ.toAlgebra
    realCenterMap τ (s ⊗ₜ[E] k) = (s : ℂ) * embeddingOverReal τ k := rfl

private theorem realCenterMap_surjective : Function.Surjective (realCenterMap (K := K) τ) := by
  let : Algebra E ℝ := τ.toAlgebra
  let φ := embeddingOverReal (K := K) τ
  obtain ⟨k, hk⟩ : ∃ k : K, cmConjugation E K k ≠ k := by
    by_contra! h
    exact cmConjugation_ne_one E K (AlgEquiv.ext h)
  have him : (φ k).im ≠ 0 := by
    intro h
    apply hk
    apply φ.injective
    rw [embedding_cmConjugation]
    apply Complex.ext
    · simp
    · simp [h]
  intro z
  let t := z.im / (φ k).im
  let s := z.re - t * (φ k).re
  refine ⟨s ⊗ₜ[E] (1 : K) + t ⊗ₜ[E] k, ?_⟩
  rw [map_add, realCenterMap_tmul, realCenterMap_tmul, map_one, mul_one]
  change (s : ℂ) + (t : ℂ) * φ k = z
  apply Complex.ext
  · simp [Complex.mul_re, s]
  · simp [Complex.mul_im, t, div_mul_cancel₀ _ him]

/-- The actual quadratic center at the real embedding is the complex field. -/
def realCenterEquiv :
    letI : Algebra E ℝ := τ.toAlgebra
    ℝ ⊗[E] K ≃ₐ[ℝ] ℂ :=
  letI : Algebra E ℝ := τ.toAlgebra
  AlgEquiv.ofBijective (realCenterMap τ) ⟨by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (realCenterMap (K := K) τ).toLinearMap) ?_).mpr
      (realCenterMap_surjective τ)
    rw [Module.finrank_baseChange, IsQuadraticExtension.finrank_eq_two, Complex.finrank_real_complex],
    realCenterMap_surjective τ⟩

@[simp] theorem realCenterEquiv_tmul (s : ℝ) (k : K) :
    letI : Algebra E ℝ := τ.toAlgebra
    realCenterEquiv τ (s ⊗ₜ[E] k) = (s : ℂ) * embeddingOverReal τ k := rfl

theorem realCenterEquiv_conjugation :
    letI : Algebra E ℝ := τ.toAlgebra
    ∀ z : ℝ ⊗[E] K,
      realCenterEquiv τ ((centerInvolution E K).baseChange ℝ z) = star (realCenterEquiv τ z) := by
  let : Algebra E ℝ := τ.toAlgebra
  intro z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz', star_add]
  | tmul s k =>
    change (s : ℂ) * embeddingOverReal τ (cmConjugation E K k) =
      star ((s : ℂ) * embeddingOverReal τ k)
    rw [embedding_cmConjugation]
    simp

variable {A : Type w} [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]

/-- The actual copy of the quadratic center in the real scalar extension. -/
def realCenterInclusion :
    letI : Algebra E ℝ := τ.toAlgebra
    (ℝ ⊗[E] K) →ₐ[ℝ] ℝ ⊗[E] A :=
  letI : Algebra E ℝ := τ.toAlgebra
  Algebra.TensorProduct.map (AlgHom.id ℝ ℝ) (IsScalarTower.toAlgHom E K A)

omit [NumberField E] [IsTotallyReal E] [NumberField K] [IsTotallyComplex K]
  [IsQuadraticExtension E K] in
@[simp] theorem realCenterInclusion_tmul (s : ℝ) (k : K) :
    letI : Algebra E ℝ := τ.toAlgebra
    realCenterInclusion (A := A) τ (s ⊗ₜ[E] k) = s ⊗ₜ[E] algebraMap K A k := rfl

omit [NumberField E] in
theorem realInvolution_center (σ : SecondKindInvolution E K A) :
    letI : Algebra E ℝ := τ.toAlgebra
    ∀ z : ℝ ⊗[E] K, σ.involution.baseChange ℝ (realCenterInclusion τ z) =
      realCenterInclusion τ ((centerInvolution E K).baseChange ℝ z) := by
  let : Algebra E ℝ := τ.toAlgebra
  intro z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul s k =>
    change s ⊗ₜ[E] σ.involution (algebraMap K A k) =
      s ⊗ₜ[E] algebraMap K A (cmConjugation E K k)
    rw [σ.onCenter]

set_option backward.isDefEq.respectTransparency false in
/-- An actual real matrix chart, including the scalar action of the complex center. -/
def realMatrixChart {n : ℕ} (D : CentralSimpleUnitaryData E K A n) :
    letI : Algebra E ℝ := τ.toAlgebra
    {e : (ℝ ⊗[E] A) ≃ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ //
      ∀ z : ℝ ⊗[E] K,
        e (realCenterInclusion τ z) = Matrix.scalar (Fin n) (realCenterEquiv τ z)} := by
  letI : Algebra E ℝ := τ.toAlgebra
  letI : Algebra E ℂ := (Complex.ofRealHom.comp τ).toAlgebra
  letI : IsScalarTower E ℝ ℂ := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra K ℂ := (embeddingOverReal (K := K) τ).toAlgebra
  letI : IsScalarTower E K ℂ :=
    IsScalarTower.of_algebraMap_eq fun e => (embeddingOverReal_apply_algebraMap τ e).symm
  let C := ℂ ⊗[K] A
  let : Algebra ℝ C := Algebra.compHom C (algebraMap ℝ ℂ)
  let : Algebra E C := Algebra.compHom C (algebraMap E ℂ)
  haveI : IsScalarTower ℝ ℂ C := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower E ℂ C := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower E ℝ C := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower E K C := IsScalarTower.of_algebraMap_eq fun d => by
    change algebraMap ℂ C (algebraMap E ℂ d) = algebraMap K C (algebraMap E K d)
    rw [IsScalarTower.algebraMap_apply E K ℂ, IsScalarTower.algebraMap_apply K ℂ C]
  let i : A →ₐ[K] C := Algebra.TensorProduct.includeRight
  let T : ℝ ⊗[E] A →ₐ[ℝ] C :=
    Algebra.TensorProduct.lift (R := E) (S := ℝ) (C := C) (Algebra.ofId ℝ C)
      (i.restrictScalars E) (fun s a => Algebra.commutes s _)
  have hT (s : ℝ) (a : A) : T (s ⊗ₜ[E] a) = (s : ℂ) ⊗ₜ[K] a := by
    change ((s : ℂ) ⊗ₜ[K] (1 : A)) * ((1 : ℂ) ⊗ₜ[K] a) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hcenter (z : ℝ ⊗[E] K) :
      T (realCenterInclusion τ z) = algebraMap ℂ C (realCenterEquiv τ z) := by
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s k =>
      rw [realCenterInclusion_tmul, hT, realCenterEquiv_tmul]
      change (s : ℂ) ⊗ₜ[K] algebraMap K A k = ((s : ℂ) * embeddingOverReal τ k) ⊗ₜ[K] (1 : A)
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      simp only [Algebra.smul_def, mul_comm ((algebraMap K ℂ) k)]
      rfl
  have hs : Function.Surjective T := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' =>
      obtain ⟨x, rfl⟩ := hz
      obtain ⟨y, rfl⟩ := hz'
      exact ⟨x + y, map_add T _ _⟩
    | tmul c a =>
      obtain ⟨z, hz⟩ := (realCenterEquiv (K := K) τ).surjective c
      refine ⟨realCenterInclusion τ z * ((1 : ℝ) ⊗ₜ[E] a), ?_⟩
      rw [map_mul, hcenter, hz, hT]
      change (c ⊗ₜ[K] (1 : A)) * ((1 : ℂ) ⊗ₜ[K] a) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  letI : FiniteDimensional K A := D.finite
  letI : FiniteDimensional E A := Module.Finite.trans K A
  letI : FiniteDimensional ℂ C := inferInstanceAs (FiniteDimensional ℂ (ℂ ⊗[K] A))
  letI : FiniteDimensional ℝ C := Module.Finite.trans ℂ C
  have hdim : Module.finrank ℝ (ℝ ⊗[E] A) = Module.finrank ℝ C := by
    rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank E K A,
      ← Module.finrank_mul_finrank ℝ ℂ C, Complex.finrank_real_complex,
      IsQuadraticExtension.finrank_eq_two]
    simp only [C, Module.finrank_baseChange]
  let e := AlgEquiv.ofBijective T
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := T.toLinearMap) hdim).mpr hs, hs⟩
  letI : Algebra.IsCentral K A := D.central
  letI : IsSimpleRing A := D.simple
  letI : Algebra.IsCentral ℂ C := Langlands.CentralSimple.isCentral_baseChange K A ℂ
  letI : IsSimpleRing C := Langlands.CentralSimple.isSimpleRing_baseChange K A ℂ
  have hsize : Nat.sqrt (Module.finrank ℂ C) = n := by
    change Nat.sqrt (Module.finrank ℂ (ℂ ⊗[K] A)) = n
    rw [Module.finrank_baseChange, D.dimension, pow_two, Nat.sqrt_eq]
  let f : C ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (Langlands.CentralSimple.sepClosedChart ℂ C).trans
      (Matrix.reindexAlgEquiv ℂ ℂ (finCongr hsize))
  refine ⟨e.trans (f.restrictScalars ℝ), fun z => ?_⟩
  change f (T (realCenterInclusion τ z)) = _
  rw [hcenter, f.commutes]
  rfl

end FiniteUnitary

end Langlands.Shimura
