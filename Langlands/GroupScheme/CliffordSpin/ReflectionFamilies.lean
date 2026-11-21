import Langlands.GroupScheme.CliffordSpin.ReflectionCoefficientChange
import Langlands.GroupScheme.CliffordSpin.ScalarIsometryProjection
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Connected families of two-reflection orthogonal transformations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.CliffordSpin

open Quaternionic Langlands.QuadraticForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {F : Type u} [Field F] [CharZero F] [Invertible (2 : F)] {n : ℕ} [NeZero n]
  (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "τ" => FirstKindInvolution.scalar F
local notation "Q" => Matrix.toQuadraticForm' (FirstKindInvolution.polar τ q)
local notation "b" => Pi.basisFun F (Fin n)
local notation "SO" => FirstKindInvolution.normOneIsometryGroup τ q

/-- A product of two reflections is joined to the identity by an affine family over a domain. -/
theorem exists_reflectionPair_family (K : Type u) [Field K] [Algebra F K]
    (v w : K ⊗[F] (Fin n → F)) (hv : (Q).baseChange K v ≠ 0) (hw : (Q).baseChange K w ≠ 0) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra F A) (_ : IsDomain A)
      (φ₀ φ₁ : A →ₐ[F] K) (x : (SO).affinePoints (CommAlgCat.of F A)),
      (SO).affinePointMap (CommAlgCat.ofHom φ₀) x = 1 ∧
      matrixAction b K (actionMatrix q (CommAlgCat.of F K)
        ((SO).affinePointMap (CommAlgCat.ofHom φ₁) x)) =
        (reflection ((Q).baseChange K) v hv).toLinearEquiv *
          (reflection ((Q).baseChange K) w hw).toLinearEquiv := by
  let B := Polynomial K
  let j : K →ₐ[F] B := IsScalarTower.toAlgHom F K B
  let e (t : K) : B →ₐ[F] K := (Polynomial.aeval t).restrictScalars F
  have hej (t : K) : (e t).comp j = AlgHom.id F K := by
    ext c
    exact Polynomial.aeval_C t c
  let vB := changeVectorCoefficients j v
  let wB := changeVectorCoefficients j w
  let uB : B ⊗[F] (Fin n → F) :=
    (1 - (Polynomial.X : B)) • vB + (Polynomial.X : B) • wB
  have he_const (t : K) (z : K ⊗[F] (Fin n → F)) :
      changeVectorCoefficients (e t) (changeVectorCoefficients j z) = z := by
    rw [changeVectorCoefficients_comp, hej]
    exact DFunLike.congr_fun TensorProduct.map_id z
  have heX (t : K) : e t (Polynomial.X : B) = t := Polynomial.aeval_X t
  have he₀ : changeVectorCoefficients (e 0) uB = v := by
    simp [uB, vB, wB, changeVectorCoefficients_smul, he_const, heX]
  have he₁ : changeVectorCoefficients (e 1) uB = w := by
    simp [uB, vB, wB, changeVectorCoefficients_smul, he_const, heX]
  let p := (Q).baseChange B uB
  have hp₀ : e 0 p = (Q).baseChange K v := by
    rw [← he₀, quadratic_changeVectorCoefficients]
  have hp₁ : e 1 p = (Q).baseChange K w := by
    rw [← he₁, quadratic_changeVectorCoefficients]
  have hp : p ≠ 0 := by
    intro h
    exact hv (by rw [← hp₀, h, map_zero])
  let A := Localization.Away p
  let : IsDomain A := Localization.Away.isDomain hp
  let i : B →ₐ[F] A := IsScalarTower.toAlgHom F B A
  let φ₀ : A →ₐ[F] K := IsLocalization.Away.liftAlgHom p (f := e 0)
    (isUnit_iff_ne_zero.mpr (hp₀.trans_ne hv))
  let φ₁ : A →ₐ[F] K := IsLocalization.Away.liftAlgHom p (f := e 1)
    (isUnit_iff_ne_zero.mpr (hp₁.trans_ne hw))
  have hφ₀ : φ₀.comp i = e 0 := by
    apply AlgHom.ext
    intro c
    exact IsLocalization.Away.lift_eq p (isUnit_iff_ne_zero.mpr (hp₀.trans_ne hv)) c
  have hφ₁ : φ₁.comp i = e 1 := by
    apply AlgHom.ext
    intro c
    exact IsLocalization.Away.lift_eq p (isUnit_iff_ne_zero.mpr (hp₁.trans_ne hw)) c
  let vA := changeVectorCoefficients i vB
  let uA := changeVectorCoefficients i uB
  have hvA : IsUnit ((Q).baseChange A vA) := by
    rw [show vA = changeVectorCoefficients (i.comp j) v from changeVectorCoefficients_comp j i v,
      quadratic_changeVectorCoefficients]
    exact (isUnit_iff_ne_zero.mpr hv).map (i.comp j)
  have huA : IsUnit ((Q).baseChange A uA) := by
    rw [show uA = changeVectorCoefficients i uB from rfl, quadratic_changeVectorCoefficients]
    exact IsLocalization.Away.algebraMap_isUnit p
  obtain ⟨av, hav⟩ := hvA
  obtain ⟨au, hau⟩ := huA
  let g := reflectionMatrix b Q vA av hav.symm * reflectionMatrix b Q uA au hau.symm
  have hg : g ∈ (actionMatrix q (CommAlgCat.of F A)).range := by
    apply (mem_range_actionMatrix_iff q (CommAlgCat.of F A) g).mpr
    constructor
    · intro z
      change (Q).baseChange A (matrixAction b A g z) = _
      rw [show g = _ from rfl, map_mul, matrixAction_reflectionMatrix, matrixAction_reflectionMatrix]
      rw [LinearEquiv.mul_apply, reflectionOfUnit_preserves, reflectionOfUnit_preserves]
    · have hd (z : A ⊗[F] (Fin n → F)) (a : Aˣ) (ha : (Q).baseChange A z = (a : A)) :
          Matrix.GeneralLinearGroup.det (reflectionMatrix b Q z a ha) = -1 := by
        rw [← det_matrixAction b, matrixAction_reflectionMatrix]
        exact det_reflectionOfUnit _ ((b).baseChange A) z a ha
      rw [show g = _ from rfl, map_mul, hd, hd, neg_mul_neg, one_mul]
  obtain ⟨x, hx⟩ := hg
  have action (φ : A →ₐ[F] K) :
      matrixAction b K (actionMatrix q (CommAlgCat.of F K)
        ((SO).affinePointMap (CommAlgCat.ofHom φ) x)) =
          reflectionOfUnit ((Q).baseChange K) (changeVectorCoefficients φ vA)
            (Units.map φ.toMonoidHom av)
            ((quadratic_changeVectorCoefficients Q φ vA).trans (congrArg φ hav.symm)) *
          reflectionOfUnit ((Q).baseChange K) (changeVectorCoefficients φ uA)
            (Units.map φ.toMonoidHom au)
            ((quadratic_changeVectorCoefficients Q φ uA).trans (congrArg φ hau.symm)) := by
    rw [actionMatrix_naturality, hx]
    change matrixAction b K (Matrix.GeneralLinearGroup.map φ.toRingHom g) = _
    rw [show g = _ from rfl, map_mul, map_reflectionMatrix, map_reflectionMatrix, map_mul,
      matrixAction_reflectionMatrix, matrixAction_reflectionMatrix]
  have hv₀ : changeVectorCoefficients φ₀ vA = v := by
    rw [show vA = changeVectorCoefficients i vB from rfl, changeVectorCoefficients_comp, hφ₀]
    exact he_const 0 v
  have hv₁ : changeVectorCoefficients φ₁ vA = v := by
    rw [show vA = changeVectorCoefficients i vB from rfl, changeVectorCoefficients_comp, hφ₁]
    exact he_const 1 v
  have hu₀ : changeVectorCoefficients φ₀ uA = v := by
    rw [show uA = changeVectorCoefficients i uB from rfl, changeVectorCoefficients_comp, hφ₀, he₀]
  have hu₁ : changeVectorCoefficients φ₁ uA = w := by
    rw [show uA = changeVectorCoefficients i uB from rfl, changeVectorCoefficients_comp, hφ₁, he₁]
  have reflection_eq {z z' : K ⊗[F] (Fin n → F)}
      (hz : (Q).baseChange K z ≠ 0) (hz' : (Q).baseChange K z' ≠ 0) (h : z = z') :
      (reflection ((Q).baseChange K) z hz).toLinearEquiv =
        (reflection ((Q).baseChange K) z' hz').toLinearEquiv := by
    subst z
    rfl
  refine ⟨A, inferInstance, inferInstance, inferInstance, φ₀, φ₁, x, ?_, ?_⟩
  · apply (actionMatrix_injective q (CommAlgCat.of F K))
    apply (matrixAction b K).injective
    rw [map_one, map_one, action φ₀, reflectionOfUnit_eq_field_reflection,
      reflectionOfUnit_eq_field_reflection, reflection_eq _ hv hv₀, reflection_eq _ hv hu₀,
      ← reflectionOfUnit_eq_field_reflection ((Q).baseChange K) v (Units.mk0 _ hv) rfl,
      reflectionOfUnit_mul_self]
  · rw [action φ₁, reflectionOfUnit_eq_field_reflection, reflectionOfUnit_eq_field_reflection,
      reflection_eq _ hv hv₁, reflection_eq _ hw hu₁]

end Langlands.GroupScheme.CliffordSpin
