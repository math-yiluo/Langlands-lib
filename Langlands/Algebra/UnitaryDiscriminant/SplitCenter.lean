import Langlands.Algebra.UnitaryDiscriminant.Class
import Langlands.Algebra.BrauerComparison.BaseChangeChart

/-! # Restricting a unitary discriminant to its quadratic center -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.UnitaryDiscriminant

open BrauerComparison ClassFieldTheory.Local LinearAlgebra.UnitaryTwistedDescent
open CentralSimple CentralSimple.SemilinearGaloisAction
open ScalarTwoCocycle (IsTwoCocycle)

attribute [local instance] coefficientGLAction

private theorem unitClass_pow {F M : Type u} [Field F] [Field M] [Algebra F M]
    (c : Gal(M/F) → Gal(M/F) → Mˣ) (hc : IsTwoCocycle c) (m : ℕ)
    (hpow : IsTwoCocycle fun g h => c g h ^ m) :
    unitClass (fun g h => c g h ^ m) hpow = m • unitClass c hc := by
  simp only [unitClass, ← map_nsmul]
  exact congrArg (groupCohomology.H2π (unitsRepresentation F M))
    (groupCohomology.cocycles₂_ext fun _ _ => rfl)

variable {F L M : Type u} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]
  [Algebra L M] [IsScalarTower F L M] [Algebra.IsQuadraticExtension F L]
  {B : Type u} [Ring B] [Algebra L B] {m : ℕ}
  {ι : L ≃ₐ[F] L} (hι : ι ≠ 1) {τ : B → B} (hτ : IsUnitaryInvolution ι τ)
  (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin (2 * m)) (Fin (2 * m)) M)

/-- Upon restriction to the quadratic center the relative discriminant is `m` times the relative
Brauer class of the original algebra. -/
theorem relativeRestriction_relativeDiscriminantClass [Nonempty (Fin (2 * m))] :
    relativeRestriction F L M 2 (relativeDiscriminantClass hι hτ e) = m • relativeClass e := by
  classical
  let r : Gal(M/L) →* Gal(M/F) := AlgEquiv.restrictScalarsHom F
  have hr (g : Gal(M/L)) : r g ∈ centerFixing F L M :=
    (mem_centerFixing (F := F) (L := L) (M := M)).2 g.commutes
  let P (g : Gal(M/L)) := chartLift hι hτ e (r g)
  let c (g h : Gal(M/L)) := chartFactor hι hτ e (r g) (r h)
  have hP (g : Gal(M/L)) (X : Matrix (Fin (2 * m)) (Fin (2 * m)) M) :
      (splittingChartIndexAction e).act g X = (P g : Matrix _ _ _) * X.map g *
        (((P g)⁻¹ : GL _ _) : Matrix _ _ _) := by
    have hN (Y : Matrix (Fin (2 * m)) (Fin (2 * m)) M) :
        (splittingChartIndexAction e).act g Y =
          twistedAct (centerFixing F L M) (chartLift hι hτ e) (r g) Y := by
      induction Y using chart_induction e with
      | hadd X Y hX hY =>
        simp only [map_add, twistedAct_eq, coeffTwist_add, Matrix.mul_add, Matrix.add_mul] at hX hY ⊢
        rw [hX, hY]
      | hgen a b =>
        rw [twistedAct_smul, twistedAct_chartLift_of_mem hι hτ e (hr g)]
        simp only [chartMap_apply, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
          mul_one, splittingChartIndexAction_apply, tensorCoefficientMap_tmul]
        rfl
    rw [hN, twistedAct_eq, coeffTwist_of_mem (hr g)]
    rfl
  have hc (g h : Gal(M/L)) : P g * (g • P h) =
      GeneralLinearGroup.scalar (Fin (2 * m)) (c g h) * P (g * h) := by
    have hl := chartLift_mul hι hτ e (r g) (r h)
    rw [twistGL_of_mem (hr g), ← map_mul r] at hl
    exact hl
  have hz : IsTwoCocycle c := ScalarTwoCocycle.isTwoCocycle_of_lifts (GeneralLinearGroup.scalar _)
    unit_scalar_injective unit_scalar_central coefficientGLAction_scalar P c hc
  have hpow : IsTwoCocycle fun g h => c g h ^ m := by
    intro g h t
    rw [← mul_pow, hz g h t, mul_pow, smul_pow']
  have hdesc : unitClass c hz = relativeClass e :=
    (descentClass_eq_of_lifts (splittingChartIndexAction e) P c hP hc).symm
  rw [← hdesc, ← unitClass_pow c hz m hpow]
  simp only [relativeRestriction, relativeDiscriminantClass, unitClass, groupCohomology.H2π_comp_map_apply]
  congr 1
  refine groupCohomology.cocycles₂_ext fun g h => congrArg Additive.ofMul ?_
  exact discriminantCocycle_of_mem hι hτ e (hr g) (r h)

section Brauer

variable [IsGalois F M]

private theorem relativeInflation_self_discriminant :
    relativeInflation F M M 2 (relativeDiscriminantClass hι hτ e) =
      relativeDiscriminantClass hι hτ e := by
  simp only [relativeInflation, relativeDiscriminantClass, unitClass, groupCohomology.H2π_comp_map_apply]
  congr 1
  refine groupCohomology.cocycles₂_ext fun g h => ?_
  have hr (s : Gal(M/F)) : s.restrictNormal M = s := by
    ext x
    exact s.restrictNormal_commutes M x
  apply Additive.ofMul.injective
  apply Units.ext
  change algebraMap M M (discriminantCocycle hι hτ e (g.restrictNormal M) (h.restrictNormal M) : M) = _
  rw [hr, hr]
  rfl

variable [FiniteDimensional F M] [FiniteDimensional L M] [IsGalois L M]

/-- The scalar extension of the unitary discriminant to the quadratic center is `m` times
the Brauer class of the original algebra of degree `2m`. -/
theorem scalarExtension_discriminantClass {A : CSA.{u, u} L}
    {t : A → A} (ht : IsUnitaryInvolution ι t)
    (f : M ⊗[L] A ≃ₐ[M] Matrix (Fin (2 * m)) (Fin (2 * m)) M)
    [Nonempty (Fin (2 * m))] :
    Brauer.scalarExtension L (discriminantClass hι ht f) = m • Brauer.classOf A := by
  classical
  let j : M →ₐ[L] SeparableClosure L := IsSepClosed.lift
  let : Algebra M (SeparableClosure L) := j.toRingHom.toAlgebra
  let : IsScalarTower L M (SeparableClosure L) := IsScalarTower.of_algHom j
  apply (brauerEquiv L).injective
  rw [map_nsmul, discriminantClass, Brauer.scalarExtension_classOf,
    brauerContinuousEquiv_at_chart L (SeparableClosure L) _ M
      (baseChangeSplittingChart L M (discriminantSplittingChart hι ht f)),
    brauerContinuousEquiv_at_chart L (SeparableClosure L) A M f]
  erw [relativeClass_baseChangeSplittingChart (A := discriminantCSA hι ht f) L M
    (discriminantSplittingChart hι ht f)]
  rw [relativeClass_discriminantSplittingChart,
    relativeInflation_self_discriminant, relativeRestriction_relativeDiscriminantClass, map_nsmul]

end Brauer

end Langlands.UnitaryDiscriminant
