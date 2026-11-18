import Langlands.Geometry.Analytic.FiniteTypeDomainNormExtensionStatement
import Langlands.Geometry.Analytic.GaussAlgebraicClosure
import Langlands.Geometry.Analytic.TateUniversal.Definitions
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # A multiplicative norm on every finite type domain -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification

open StrictTateAlgebra

private def polynomialToTate (K : Type u) [NormedField K] [IsUltrametricDist K]
    (n : ℕ) : MvPolynomial (Fin n) K →ₐ[K] StrictTateAlgebra (Fin n) K :=
  MvPolynomial.aeval (StrictTateAlgebra.X (Fin n) K)

private theorem polynomialToTate_injective (K : Type u) [NormedField K]
    [IsUltrametricDist K] (n : ℕ) : Function.Injective (polynomialToTate K n) := by
  have h : (restrictedSubalgebra (Fin n) K).val.comp (polynomialToTate K n) =
      MvPolynomial.coeToMvPowerSeries.algHom K := by
    ext i : 1
    change series (Fin n) K
      (MvPolynomial.aeval (StrictTateAlgebra.X (Fin n) K) (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
    simp [series, StrictTateAlgebra.X, monomial, MvPowerSeries.X]
  intro p q hpq
  apply MvPolynomial.coe_injective
  have hp := DFunLike.congr_fun h p
  have hq := DFunLike.congr_fun h q
  exact hp.symm.trans ((congrArg (series (Fin n) K) hpq).trans hq)

/-- A finitely generated domain over a complete ultrametric field admits
a multiplicative norm extending the scalar norm. -/
theorem finiteTypeDomainNormExtension : FiniteTypeDomainNormExtensionStatement.{u,v} := by
  intro K _ _ _ D _ _ _ _
  classical
  obtain ⟨n, f, hf, hint⟩ := exists_integral_inj_algHom_of_fg K D
  let P := MvPolynomial (Fin n) K
  let T := StrictTateAlgebra (Fin n) K
  let C := GaussAlgebraicClosure K n
  let L := FractionRing D
  let j : P →ₐ[K] C :=
    (IsScalarTower.toAlgHom K T C).comp (polynomialToTate K n)
  have hj : Function.Injective j :=
    (FaithfulSMul.algebraMap_injective T C).comp (polynomialToTate_injective K n)
  let : Algebra P D := f.toRingHom.toAlgebra
  let : FaithfulSMul P D := (faithfulSMul_iff_algebraMap_injective P D).mpr hf
  let : Algebra.IsIntegral P D := ⟨hint⟩
  let : Algebra P C := j.toRingHom.toAlgebra
  let : FaithfulSMul P C := (faithfulSMul_iff_algebraMap_injective P C).mpr hj
  let : IsScalarTower P D L := inferInstance
  let : FaithfulSMul P L := (faithfulSMul_iff_algebraMap_injective P L).mpr
    ((IsFractionRing.injective D L).comp hf)
  let : Algebra.IsAlgebraic P L := (IsFractionRing.isAlgebraic_iff' P D L).mp inferInstance
  let g : L →ₐ[P] C := IsAlgClosed.lift
  let e : D →+* C := g.toRingHom.comp (algebraMap D L)
  have he : Function.Injective e := g.injective.comp (IsFractionRing.injective D L)
  let ν : MulRingSeminorm D :=
    { toFun a := ‖e a‖
      map_zero' := by simp
      map_one' := by simp
      map_mul' := by intros; simp
      add_le' := by intros; simpa using norm_add_le (e _) (e _)
      neg' := by intro a; simpa only [map_neg] using norm_neg (e a) }
  refine ⟨ν, ?_, ?_⟩
  · intro c
    change ‖g (algebraMap D L (algebraMap K D c))‖ = ‖c‖
    have hscalar : algebraMap D L (algebraMap K D c) =
        algebraMap P L (algebraMap K P c) := by
      change algebraMap D L (algebraMap K D c) =
        algebraMap D L (f (algebraMap K P c))
      rw [f.commutes]
    rw [hscalar, g.commutes]
    change ‖j (algebraMap K P c)‖ = ‖c‖
    rw [j.commutes, norm_algebraMap']
  · intro a ha
    apply he
    rw [map_zero]
    exact norm_eq_zero.mp ha

end Langlands.Analytic.AffineAnalytification
