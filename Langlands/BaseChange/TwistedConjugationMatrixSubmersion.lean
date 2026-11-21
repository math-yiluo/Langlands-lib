import Langlands.BaseChange.FiniteAlgebraAnalyticNorm
import Langlands.BaseChange.TwistedTriangularDifferential
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Ring.Units

/-! # The twisted conjugation product in additive matrix coordinates -/

noncomputable section

namespace Langlands.BaseChange

open ContinuousLinearMap
open scoped RightActions

private theorem exists_strictDerivative_twistedProduct
    {F R : Type*} [NontriviallyNormedField F] [CompleteSpace F]
    [NormedRing R] [NormedAlgebra F R] [CompleteSpace R] [FiniteDimensional F R]
    (S : Subalgebra F R) (σ : R ≃ₐ[F] R) (y : R) (k : Rˣ) (p : S) :
    ∃ D : R × (R × S) →L[F] R,
      HasStrictFDerivAt
        (fun z : R × (R × S) => z.2.1 * z.1 * Ring.inverse (σ z.2.1) * σ z.2.2.val)
        D (y, k.val, p) ∧
      ∀ (X : R) (Y : S), D (0, X, Y) =
        X * y * σ (k⁻¹ : Rˣ).val * σ p.val -
          k.val * y * σ (k⁻¹ : Rˣ).val * σ X * σ (k⁻¹ : Rˣ).val * σ p.val +
          k.val * y * σ (k⁻¹ : Rˣ).val * σ Y.val := by
  let A := R × (R × S)
  let z₀ : A := (y, k.val, p)
  let t : A →L[F] R := fst F R (R × S)
  let x : A →L[F] R := (fst F R S).comp (snd F R (R × S))
  let s : R →L[F] R := σ.toLinearMap.toContinuousLinearMap
  let b : A →L[F] R := (s.comp S.val.toLinearMap.toContinuousLinearMap).comp
    ((snd F R S).comp (snd F R (R × S)))
  let kσ : Rˣ := Units.map σ.toMonoidHom k
  let a : R := (kσ⁻¹ : Rˣ).val
  let dInv : A →L[F] R := (-mulLeftRight F R a a).comp (s.comp x)
  have hInv : HasStrictFDerivAt (fun z : A => Ring.inverse (σ (x z))) dInv z₀ :=
    (hasStrictFDerivAt_ringInverse (𝕜 := F) kσ).comp z₀ (s.comp x).hasStrictFDerivAt
  have h := ((x.hasStrictFDerivAt.mul' t.hasStrictFDerivAt).mul' hInv).mul' b.hasStrictFDerivAt
  refine ⟨_, h, ?_⟩
  have hval : Ring.inverse (σ k.val) = σ (k⁻¹ : Rˣ).val := Ring.inverse_unit kσ
  have ha : a = σ (k⁻¹ : Rˣ).val := by
    change ((Units.map σ.toMonoidHom k)⁻¹ : Rˣ).val = _
    rw [← map_inv]
    rfl
  intro X Y
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, _root_.smul_apply,
    smul_eq_mul, op_smul_eq_mul, _root_.neg_apply,
    Pi.mul_apply, mulLeftRight_apply, t, x, b, z₀, dInv, s, LinearMap.coe_toContinuousLinearMap',
    AlgEquiv.toLinearMap_apply, coe_fst', coe_snd', AlgHom.toLinearMap_apply,
    Subalgebra.val_apply, ha, mul_zero, zero_add]
  erw [hval]
  change k.val * y * σ (k⁻¹ : Rˣ).val * σ Y.val +
    (k.val * y * -(σ (k⁻¹ : Rˣ).val * σ X * σ (k⁻¹ : Rˣ).val) +
      X * y * σ (k⁻¹ : Rˣ).val) * σ p.val = _
  noncomm_ring

universe u v

variable {F : Type u} {E : Type v} {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) E
local notation "Tri" => upperTriangularSubalgebra F E n
local notation "G" => GeneralLinear n E

section Field

variable [Field F] [CommRing E] [Algebra F E]

/-- The parameter, conjugator, and upper triangular right factor are expressed as
matrices. On the unit locus this is the matrix of the twisted product. -/
def twistedConjugationMatrixMap (σ : E ≃ₐ[F] E) (z : Mat × (Mat × Tri)) : Mat :=
  z.2.1 * z.1 * Ring.inverse (σ.mapMatrix z.2.1) * σ.mapMatrix z.2.2.val

theorem twistedConjugationMatrixMap_units (σ : E ≃ₐ[F] E) (y k p : G)
    (hp : p.val.IsUpperTriangular) :
    twistedConjugationMatrixMap σ (y.val, k.val, ⟨p.val, hp⟩) =
      (k * y * (entrywiseAut σ n k)⁻¹ * entrywiseAut σ n p).val := by
  change k.val * y.val * Ring.inverse (entrywiseAut σ n k).val *
    (entrywiseAut σ n p).val = _
  rw [Ring.inverse_unit]
  rfl

end Field

section NormedField

variable [NontriviallyNormedField F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [IsModuleTopology F E]

private theorem matrix_moduleTopology : IsModuleTopology F Mat :=
  inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))

variable [CompleteSpace F] [Module.Finite F E]

/-- The coordinate map is continuous wherever the conjugating matrix is a unit. -/
theorem twistedConjugationMatrixMap_continuousOn (σ : E ≃ₐ[F] E) :
    ContinuousOn (twistedConjugationMatrixMap (n := n) σ) {z | IsUnit z.2.1} := by
  let : IsModuleTopology F Mat := matrix_moduleTopology
  let : NormedRing Mat := finiteAlgebraNormedRing F Mat
  let : NormedAlgebra F Mat := finiteAlgebraNormedAlgebra F Mat
  let : CompleteSpace Mat := FiniteDimensional.complete F Mat
  rintro ⟨y, x, p⟩ hx
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨D, hD, _⟩ := exists_strictDerivative_twistedProduct Tri σ.mapMatrix y k p
  exact hD.continuousAt.continuousWithinAt

/-- At a σ-regular parameter and invertible conjugator and triangular factor, the
strict derivative in the source variables is onto. -/
def TwistedConjugationMatrixSubmersionStatement : Prop :=
  ∀ (F : Type u) [NontriviallyNormedField F] [CompleteSpace F] [CharZero F]
    (E : Type v) [CommRing E] [Algebra F E] [Module.Finite F E] [IsReduced E]
    [TopologicalSpace E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ) (δ k p : GeneralLinear n E) (hp : p.val.IsUpperTriangular),
    σ ^ l = 1 → IsSigmaRegular σ l δ →
    let M := Matrix (Fin n) (Fin n) E
    let T := upperTriangularSubalgebra F E n
    let : IsModuleTopology F M := matrix_moduleTopology
    let : NormedRing M := finiteAlgebraNormedRing F M
    let : NormedAlgebra F M := finiteAlgebraNormedAlgebra F M
    ∃ D : M × (M × T) →L[F] M,
      HasStrictFDerivAt (twistedConjugationMatrixMap σ) D (δ.val, k.val, ⟨p.val, hp⟩) ∧
      Function.Surjective (D.comp (inr F M (M × T)))

theorem twistedConjugationMatrixSubmersion : TwistedConjugationMatrixSubmersionStatement.{u, v} := by
  intro F _ _ _ E _ _ _ _ _ _ σ l n δ k p hp hσ hδ
  let M := Matrix (Fin n) (Fin n) E
  let T := upperTriangularSubalgebra F E n
  let G₀ := GeneralLinear n E
  let : IsModuleTopology F M := matrix_moduleTopology
  let : NormedRing M := finiteAlgebraNormedRing F M
  let : NormedAlgebra F M := finiteAlgebraNormedAlgebra F M
  let : CompleteSpace M := FiniteDimensional.complete F M
  let pTri : T := ⟨p.val, hp⟩
  obtain ⟨D, hD, hPart⟩ := exists_strictDerivative_twistedProduct T σ.mapMatrix δ.val k pTri
  refine ⟨D, hD, ?_⟩
  let d : G₀ := k * δ * (entrywiseAut σ n k)⁻¹
  have hd : IsSigmaRegular σ l d := by
    obtain ⟨γ, hN, hγ⟩ := hδ
    exact ⟨γ, by simpa [d, map_inv] using hN.twistedConj hσ k⁻¹ (1 : GeneralLinear n F), hγ⟩
  let w : G₀ := d * entrywiseAut σ n p
  have hsurj := twistedTriangularDifferential_surjective F E n l σ hσ d hd
  intro Z
  obtain ⟨⟨X, Y⟩, hXY⟩ := hsurj (Z * (w⁻¹ : G₀).val)
  refine ⟨(X * k.val, Y * pTri), ?_⟩
  change D (0, X * k.val, Y * pTri) = Z
  have hσk : σ.mapMatrix (k⁻¹ : G₀).val = ((entrywiseAut σ n k)⁻¹ : G₀).val := by
    rw [← map_inv (entrywiseAut σ n)]
    rfl
  have hInv : σ.mapMatrix k.val * σ.mapMatrix (k⁻¹ : G₀).val = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hcancel (Q : M) :
      twistedMatrixConj σ d Q * w.val = d.val * σ.mapMatrix Q * σ.mapMatrix p.val := by
    rw [twistedMatrixConj_apply]
    change d.val * σ.mapMatrix Q * (d⁻¹ : G₀).val * (d.val * σ.mapMatrix p.val) = _
    rw [mul_assoc (d.val * σ.mapMatrix Q), ← mul_assoc (d⁻¹ : G₀).val, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_mul]
  have hfactor : D (0, X * k.val, Y * pTri) = twistedTriangularDifferential σ d (X, Y) * w.val := by
    rw [hPart, twistedTriangularDifferential_apply, add_mul, sub_mul, hcancel, hcancel]
    change X * k.val * δ.val * σ.mapMatrix (k⁻¹ : G₀).val * σ.mapMatrix p.val -
      d.val * σ.mapMatrix (X * k.val) * σ.mapMatrix (k⁻¹ : G₀).val * σ.mapMatrix p.val +
      d.val * σ.mapMatrix (Y.val * p.val) =
      X * w.val - d.val * σ.mapMatrix X * σ.mapMatrix p.val +
        d.val * σ.mapMatrix Y.val * σ.mapMatrix p.val
    rw [map_mul, map_mul, ← mul_assoc d.val (σ.mapMatrix X),
      mul_assoc (d.val * σ.mapMatrix X), hInv, mul_one, ← mul_assoc d.val (σ.mapMatrix Y.val)]
    rw [show w.val = d.val * σ.mapMatrix p.val from rfl,
      show d.val = k.val * δ.val * ((entrywiseAut σ n k)⁻¹ : G₀).val from rfl, hσk]
    simp only [mul_assoc]
  rw [hfactor, hXY, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

end NormedField

end Langlands.BaseChange
