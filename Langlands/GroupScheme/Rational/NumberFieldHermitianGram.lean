import Langlands.GroupScheme.Examples.HermitianRootQuadraticForm
import Langlands.GroupScheme.Examples.HermitianMatrixBasic
import Langlands.GroupScheme.Quaternionic.AntihermitianScalarIsometry
import Langlands.LinearAlgebra.NumberFieldQuadraticIsometryProof

/-! # Local-to-global congruence of Hermitian matrices over a quadratic field -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.HermitianMatrix

open Quaternionic SU3Root

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

section QuadraticIsometry

private def pullbackIsometry {F V W : Type u} [CommRing F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (q : QuadraticForm F V) (e : W ≃ₗ[F] V) :
    (q.comp e.toLinearMap).IsometryEquiv q :=
  { e with map_app' := fun _ => rfl }

variable {F V W : Type u} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

private def extendPullbackIsometry [Invertible (2 : F)] (q : QuadraticForm F V) (e : W ≃ₗ[F] V)
    (R : Type u) [CommRing R] [Algebra F R] :
    (QuadraticForm.baseChange R (q.comp e.toLinearMap)).IsometryEquiv (q.baseChange R) := by
  let f := e.baseChange F R W V
  have h : QuadraticForm.baseChange R (q.comp e.toLinearMap) = (q.baseChange R).comp f.toLinearMap := by
    apply baseChange_ext
    intro x
    simp only [QuadraticForm.baseChange_tmul, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
      f, LinearEquiv.baseChange_tmul]
  rw [h]
  exact pullbackIsometry (q.baseChange R) f

private theorem nondegenerate_pullback (q : QuadraticForm F V) (e : W ≃ₗ[F] V)
    (hq : q.polarBilin.Nondegenerate) : (q.comp e.toLinearMap).polarBilin.Nondegenerate := by
  have hp (x y : W) : (q.comp e.toLinearMap).polarBilin x y = q.polarBilin (e x) (e y) := by
    rw [QuadraticMap.polarBilin_comp]
    rfl
  have hs : q.polarBilin.IsSymm := ⟨fun x y => QuadraticMap.polar_comm q x y⟩
  have ht : (q.comp e.toLinearMap).polarBilin.IsSymm := ⟨fun x y => by rw [hp, hp, hs.eq]⟩
  apply ht.isRefl.nondegenerate_iff_separatingLeft.mpr
  intro x hx
  apply e.injective
  rw [map_zero]
  apply hq.1
  intro y
  obtain ⟨z, rfl⟩ := e.surjective y
  exact (hp x z).symm.trans (hx z)

private theorem quadraticEquivalent_of_local [NumberField F] [FiniteDimensional F V]
    (q q' : QuadraticForm F V) (hq : q.polarBilin.Nondegenerate) (hq' : q'.polarBilin.Nondegenerate) :
    let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
    (∀ v : Global.Place F, (q.baseChange (Global.placeCompletion F v)).Equivalent
      (q'.baseChange (Global.placeCompletion F v))) → q.Equivalent q' := by
  intro inst hlocal
  let e := (Module.finBasis F V).equivFun.symm
  obtain ⟨f⟩ := numberFieldQuadraticIsometry F (Module.finrank F V)
    (q.comp e.toLinearMap) (q'.comp e.toLinearMap)
    (nondegenerate_pullback q e hq) (nondegenerate_pullback q' e hq') (fun v => by
      obtain ⟨g⟩ := hlocal v
      let K := Global.placeCompletion F v
      exact ⟨((extendPullbackIsometry q e K).trans g).trans (extendPullbackIsometry q' e K).symm⟩)
  exact ⟨((pullbackIsometry q e).symm.trans f).trans (pullbackIsometry q' e)⟩

end QuadraticIsometry

section HermitianComparison

variable (F E : Type u) [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]

/-- The field conjugation as an anti-involution fixing the ground-field scalars. -/
def quadraticConjugationInvolution : FirstKindInvolution F E where
  toLinearMap := (conjugation F E).toLinearMap
  map_one' := map_one (conjugation F E)
  map_mul' x y := (map_mul (conjugation F E) x y).trans (mul_comm _ _)
  involutive' := conjugation_involutive F E

local notation "τ" => quadraticConjugationInvolution F E
local notation "c" => fieldInvolution F E

@[simp] theorem quadraticConjugationInvolution_apply (a : E) : (τ) a = conjugation F E a := rfl

variable {n : ℕ}

/-- Congruence in row-vector convention after extending the ground-field coefficients. -/
def GramCongruentOver (H J : Form c (Fin n)) (R : Type u) [CommRing R] [Algebra F R] : Prop :=
  let i : E →ₐ[F] R ⊗[F] E := Algebra.TensorProduct.includeRight
  ∃ P : GL (Fin n) (R ⊗[F] E),
    (P : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (H.gram : Matrix (Fin n) (Fin n) E).map i *
      ((τ).baseChange R).matrix (Fin n) P = (J.gram : Matrix (Fin n) (Fin n) E).map i

private theorem exists_antiInvariant_coordinate :
    ∃ (d : E) (ℓ : E →ₗ[F] F), d ≠ 0 ∧ (τ) d = -d ∧
      (∃ a, ℓ (a - (τ) a) ≠ 0) ∧ (∀ a ∈ (τ).alternatingSubspace, ℓ a = 0 → a = 0) := by
  obtain ⟨x, hx⟩ : ∃ x : E, (τ) x ≠ x := by
    by_contra! h
    exact conjugation_ne_one F E (AlgEquiv.ext h)
  let d := x - (τ) x
  have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hc : (τ) d = -d := by rw [show d = x - (τ) x from rfl, (τ).map_sub, (τ).apply_apply, neg_sub]
  let r := HermitianRoot.DiagonalForm.traceOneRetraction F E
  let ℓ := r.comp (LinearMap.mulLeft F d⁻¹)
  have hℓ (a : E) (ha : (τ) a = -a) : algebraMap F E (ℓ a) = d⁻¹ * a := by
    change algebraMap F E (r (d⁻¹ * a)) = _
    apply HermitianRoot.DiagonalForm.algebraMap_traceOneRetraction
    change (τ) (d⁻¹ * a) = d⁻¹ * a
    simp only [(τ).map_mul, ha, quadraticConjugationInvolution_apply, map_inv₀]
    change -a * ((τ) d)⁻¹ = d⁻¹ * a
    rw [hc, inv_neg, neg_mul_neg, mul_comm]
  refine ⟨d, ℓ, hd, hc, ⟨x, ?_⟩, ?_⟩
  · intro h
    have h0 := hℓ d hc
    change ℓ d = 0 at h
    rw [h, map_zero, inv_mul_cancel₀ hd] at h0
    exact zero_ne_one h0
  · intro a ha h
    obtain ⟨b, rfl⟩ := (τ).mem_alternatingSubspace.mp ha
    have hc' : (τ) (b - (τ) b) = -(b - (τ) b) := by rw [(τ).map_sub, (τ).apply_apply, neg_sub]
    have h' := hℓ _ hc'
    rw [h, map_zero] at h'
    exact (mul_eq_zero.mp h'.symm).resolve_left (inv_ne_zero hd)

variable [Invertible (2 : F)]

omit [Invertible (2 : F)] in
private theorem matrix_smul_eq_neg (d : E) (hd : (τ) d = -d) (H : Form c (Fin n)) :
    (τ).matrix (Fin n) (d • (H.gram : Matrix (Fin n) (Fin n) E)) =
      -(d • (H.gram : Matrix (Fin n) (Fin n) E)) := by
  ext i j
  rw [FirstKindInvolution.matrix_apply, Matrix.smul_apply, smul_eq_mul, (τ).map_mul, hd]
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) E => A i j) H.hermitian
  change (τ) (H.gram j i) = H.gram i j at h
  rw [h, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem antihermitian_smul (d : E) (hd : (τ) d = -d) (H : Form c (Fin n)) :
    (τ).IsAntihermitian (d • (H.gram : Matrix (Fin n) (Fin n) E)) := by
  let A := d • (H.gram : Matrix (Fin n) (Fin n) E)
  have h : (τ).matrix (Fin n) A = -A := matrix_smul_eq_neg F E d hd H
  refine ⟨h, fun i => (τ).mem_alternatingSubspace.mpr ⟨⅟(2 : F) • A i i, ?_⟩⟩
  have hi : (τ) (A i i) = -A i i := congrArg (fun B : Matrix (Fin n) (Fin n) E => B i i) h
  rw [(τ).map_smul, hi, smul_neg, sub_neg_eq_add, invOf_two_smul_add_invOf_two_smul]

omit [Invertible (2 : F)] in
private theorem isUnit_smul_gram {d : E} (hd : d ≠ 0) (H : Form c (Fin n)) :
    IsUnit (d • (H.gram : Matrix (Fin n) (Fin n) E)) := by
  rw [Algebra.smul_def]
  exact ((isUnit_iff_ne_zero.mpr hd).map (algebraMap E (Matrix (Fin n) (Fin n) E))).mul H.gram.isUnit

private theorem scalarQuadratic_smul_equiv_of_localGram (ℓ : E →ₗ[F] F) (d : E)
    (H J : Form c (Fin n)) (R : Type u) [CommRing R] [Algebra F R]
    (h : GramCongruentOver F E H J R) :
    (((τ).scalarQuadratic ℓ (d • (J.gram : Matrix (Fin n) (Fin n) E))).baseChange R).Equivalent
      (((τ).scalarQuadratic ℓ (d • (H.gram : Matrix (Fin n) (Fin n) E))).baseChange R) := by
  obtain ⟨P, hP⟩ := h
  let i : E →ₐ[F] R ⊗[F] E := Algebra.TensorProduct.includeRight
  have hmap (M : Matrix (Fin n) (Fin n) E) : (d • M).map i = i d • M.map i := by
    ext a b
    exact map_mul i d (M a b)
  have hQ : (P : Matrix (Fin n) (Fin n) (R ⊗[F] E)) *
      (d • (H.gram : Matrix (Fin n) (Fin n) E)).map i * ((τ).baseChange R).matrix (Fin n) P =
        (d • (J.gram : Matrix (Fin n) (Fin n) E)).map i := by
    rw [hmap, hmap, Matrix.mul_smul, Matrix.smul_mul, hP]
  rw [(τ).scalarQuadratic_baseChange, (τ).scalarQuadratic_baseChange]
  let ℓR := FirstKindInvolution.baseChangeScalarFunctional ℓ R
  let HQ := ((τ).baseChange R).scalarQuadratic ℓR ((d • (H.gram : Matrix (Fin n) (Fin n) E)).map i)
  let JQ := ((τ).baseChange R).scalarQuadratic ℓR ((d • (J.gram : Matrix (Fin n) (Fin n) E)).map i)
  let E₀ := TensorProduct.piRight F R R (fun _ : Fin n => E)
  exact ⟨((pullbackIsometry JQ E₀).trans (((τ).baseChange R).scalarQuadraticIsometry ℓR P hQ)).trans
    (pullbackIsometry HQ E₀).symm⟩

end HermitianComparison

/-- Nondegenerate Hermitian Gram matrices over a quadratic extension of a number field are
congruent when their extensions to all completion coefficient algebras are congruent. -/
def NumberFieldHermitianGramCongruenceStatement : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (n : ℕ) (H J : Form (fieldInvolution F E) (Fin n)),
    (∀ v : Global.Place F, GramCongruentOver F E H J (Global.placeCompletion F v)) →
    ∃ P : GL (Fin n) E, (P : Matrix (Fin n) (Fin n) E) * (H.gram : Matrix (Fin n) (Fin n) E) *
      adjoint (fieldInvolution F E) (P : Matrix (Fin n) (Fin n) E) = J.gram

/-- Recover Hermitian congruence from the Hasse–Minkowski theorem on scalar quadratic forms. -/
theorem numberFieldHermitianGramCongruence : NumberFieldHermitianGramCongruenceStatement.{u} := by
  intro F E _ _ _ _ _ _ n H J h
  let σ := quadraticConjugationInvolution F E
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  let : FiniteDimensional F E := .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two F E]; decide)
  obtain ⟨d, ℓ, hd, hbar, hℓ, hcoord⟩ := exists_antiInvariant_coordinate F E
  let A := d • (H.gram : Matrix (Fin n) (Fin n) E)
  let B := d • (J.gram : Matrix (Fin n) (Fin n) E)
  have hA : σ.IsAntihermitian A := antihermitian_smul F E d hbar H
  have hB : σ.IsAntihermitian B := antihermitian_smul F E d hbar J
  have hAu : IsUnit A := isUnit_smul_gram F E hd H
  have hBu : IsUnit B := isUnit_smul_gram F E hd J
  have hQ := quadraticEquivalent_of_local _ _
    (σ.scalarQuadratic_nondegenerate ℓ hB hBu hℓ) (σ.scalarQuadratic_nondegenerate ℓ hA hAu hℓ)
    (fun v => scalarQuadratic_smul_equiv_of_localGram F E ℓ d H J _ (h v))
  obtain ⟨P, hP⟩ := FirstKindInvolution.matrixScalarIsometryReflection F E σ (Fin n)
    ℓ A B hℓ hcoord hA hB hAu hBu hQ
  refine ⟨P, ?_⟩
  change (P : Matrix (Fin n) (Fin n) E) * (H.gram : Matrix (Fin n) (Fin n) E) *
    σ.matrix (Fin n) P = J.gram
  change (P : Matrix (Fin n) (Fin n) E) * (d • (H.gram : Matrix (Fin n) (Fin n) E)) *
    σ.matrix (Fin n) P = d • (J.gram : Matrix (Fin n) (Fin n) E) at hP
  rw [Matrix.mul_smul, Matrix.smul_mul] at hP
  exact smul_right_injective _ hd hP

end Langlands.GroupScheme.HermitianMatrix
