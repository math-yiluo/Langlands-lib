import Langlands.Algebra.UnitaryDiscriminant.CocycleTransfer
import Langlands.Algebra.BrauerComparison.BaseChangeChart

/-! # Base change of the discriminant with a quadratic field center -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.UnitaryDiscriminant

open BrauerComparison ClassFieldTheory.Local LinearAlgebra.UnitaryTwistedDescent

variable {F L M F' L' M' : Type u}
  [Field F] [Field L] [Field M] [Field F'] [Field L'] [Field M']
  [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
  [Algebra F F'] [Algebra F M'] [Algebra F' M'] [IsScalarTower F F' M']
  [Algebra F' L'] [Algebra L' M'] [IsScalarTower F' L' M']
  [Algebra L L'] [Algebra L M'] [Algebra M M'] [IsScalarTower F M M']
  [IsScalarTower L M M'] [IsScalarTower L L' M']
  [Algebra.IsQuadraticExtension F L] [Algebra.IsQuadraticExtension F' L'] [Normal F M]
  {ι : L ≃ₐ[F] L} (hι : ι ≠ 1) {ι' : L' ≃ₐ[F'] L'} (hι' : ι' ≠ 1)
  (hιcompat : ∀ x : L, ι' (algebraMap L L' x) = algebraMap L L' (ι x))

local notation "res" =>
  MonoidHom.comp (AlgEquiv.restrictNormalHom M)
    (AlgEquiv.restrictScalarsHom F : Gal(M'/F') →* Gal(M'/F))

omit [IsScalarTower F L M] [Algebra.IsQuadraticExtension F L] in
include hι hι' hιcompat in
private theorem centerFixing_eq_comap :
    centerFixing F' L' M' = (centerFixing F L M).comap res := by
  ext g
  change g ∈ centerFixing F' L' M' ↔ res g ∈ centerFixing F L M
  have hcoeff (x : L) :
      algebraMap M M' (algebraMap L M x) = algebraMap L' M' (algebraMap L L' x) :=
    (IsScalarTower.algebraMap_apply L M M' x).symm.trans (IsScalarTower.algebraMap_apply L L' M' x)
  have hres (x : M) : algebraMap M M' (res g x) = g (algebraMap M M' x) :=
    (g.restrictScalars F).restrictNormal_commutes M x
  constructor
  · intro hg
    apply mem_centerFixing.mpr
    intro x
    apply (algebraMap M M').injective
    rw [hres, hcoeff]
    exact (mem_centerFixing.mp hg) (algebraMap L L' x)
  · intro hr
    by_contra hg
    apply hι
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L L').injective
    apply (algebraMap L' M').injective
    have hx := congrArg (algebraMap M M') ((mem_centerFixing.mp hr) x)
    rw [hres, hcoeff, apply_algebraMap_of_not_mem hι' hg, hιcompat] at hx
    exact hx

variable {A : CSA.{u, u} L} {m : ℕ} {τ : A → A} (hτ : IsUnitaryInvolution ι τ)
  {τ' : L' ⊗[L] A → L' ⊗[L] A} (hτ' : IsUnitaryInvolution ι' τ')
  (hτcompat : ∀ a : A, τ' (1 ⊗ₜ[L] a) = 1 ⊗ₜ[L] τ a)
  (e : M ⊗[L] A ≃ₐ[M] Matrix (Fin (2 * m)) (Fin (2 * m)) M)

include hιcompat hτcompat in
/-- Extending coefficients and restricting the base changes the relative discriminant to
the class of the scalar-extended pair, for compatible quadratic field centers. -/
theorem relativeDiscriminantClass_baseChange :
    relativeRestriction F F' M' 2 (relativeInflation F M M' 2 (relativeDiscriminantClass hι hτ e)) =
      relativeDiscriminantClass hι' hτ' (baseChangeSplittingChart (A := A) L' M' e) := by
  classical
  let J := centerFixing F L M
  let J' := centerFixing F' L' M'
  let f := algebraMap M M'
  let P := chartLift hι hτ e
  let c := chartFactor hι hτ e
  let P' := transferredLift f res P
  let c' := transferredFactor f res c
  let e' := baseChangeSplittingChart (A := A) L' M' e
  have hJ : J' = J.comap res := centerFixing_eq_comap hι hι' hιcompat
  have hres (g : Gal(M'/F')) (x : M) : g (f x) = f (res g x) :=
    ((g.restrictScalars F).restrictNormal_commutes M x).symm
  have hmem (g : Gal(M'/F')) : g ∈ J' ↔ res g ∈ J := by
    rw [hJ]
    rfl
  have hP' (g : Gal(M'/F')) (X : Matrix (Fin (2 * m)) (Fin (2 * m)) M) :
      twistedAct J' P' g (X.map f) = (twistedAct J P (res g) X).map f := by
    rw [hJ]
    exact twistedAct_transferredLift f res hres P g X
  have hc' (g h : Gal(M'/F')) : P' g * twistGL J' g (P' h) =
      GeneralLinearGroup.scalar (Fin (2 * m)) (c' g h) * P' (g * h) := by
    rw [hJ]
    exact transferredLift_mul f res hres P c (chartLift_mul hι hτ e) g h
  have hchart (b : L') (a : A) :
      chartMap e' (b ⊗ₜ[L] a) = algebraMap L' M' b • (chartMap e a).map f := by
    simp only [e', chartMap_apply, baseChangeSplittingChart_tmul, Algebra.smul_def, mul_one, f]
  have hτ'tensor (b : L') (a : A) : τ' (b ⊗ₜ[L] a) = ι' b ⊗ₜ[L] τ a := by
    have hba : b ⊗ₜ[L] a = (1 ⊗ₜ[L] a) * algebraMap L' (L' ⊗[L] A) b := by
      change b ⊗ₜ[L] a = (1 ⊗ₜ[L] a) * (b ⊗ₜ[L] (1 : A))
      simp
    rw [hba, hτ'.2.1, hτ'.2.2.2, hτcompat]
    change (ι' b ⊗ₜ[L] (1 : A)) * (1 ⊗ₜ[L] τ a) = _
    simp
  have hin (g : Gal(M'/F')) (hg : g ∈ J') (x : L' ⊗[L] A) :
      twistedAct J' P' g (chartMap e' x) = chartMap e' x := by
    induction x using TensorProduct.inductionOn with
    | tmul b a =>
      rw [hchart, twistedAct_smul, hP', twistedAct_chartLift_of_mem hι hτ e ((hmem g).mp hg),
        (mem_centerFixing.mp hg) b]
    | add x y hx hy =>
      simp only [map_add, twistedAct_eq, coeffTwist_add, Matrix.mul_add, Matrix.add_mul] at hx hy ⊢
      rw [hx, hy]
  have hout (g : Gal(M'/F')) (hg : g ∉ J') (x : L' ⊗[L] A) :
      twistedAct J' P' g (chartMap e' x) = chartMap e' (τ' x) := by
    induction x using TensorProduct.inductionOn with
    | tmul b a =>
      rw [hchart, twistedAct_smul, hP', twistedAct_chartLift_of_not_mem hι hτ e (hg ∘ (hmem g).mpr),
        apply_algebraMap_of_not_mem hι' hg, hτ'tensor, hchart]
    | add x y hx hy =>
      simp only [map_add, hτ'.1, twistedAct_eq, coeffTwist_add, Matrix.mul_add, Matrix.add_mul] at hx hy ⊢
      rw [hx, hy]
  change _ = relativeDiscriminantClass hι' hτ' e'
  rw [← relativeDiscriminantClass_eq_of_lifts hι' hτ' e' P' c' hin hout hc']
  simp only [relativeRestriction, relativeInflation, relativeDiscriminantClass,
    unitClass, groupCohomology.H2π_comp_map_apply]
  congr 1
  refine groupCohomology.cocycles₂_ext fun g h => congrArg Additive.ofMul ?_
  change transferredFactor f res (detCocycle J P c m) g h = detCocycle J' P' c' m g h
  rw [hJ]
  exact (detCocycle_transferredLift f res hres P c m g h).symm

variable [FiniteDimensional F M] [IsGalois F M] [FiniteDimensional F' M'] [IsGalois F' M']

include hιcompat hτcompat in
/-- Scalar extension of the discriminant Brauer class is the class of the extended pair
when the quadratic center remains a field. -/
theorem scalarExtension_discriminantClass_baseChange :
    Brauer.scalarExtension F' (discriminantClass hι hτ e) =
      discriminantClass hι' hτ' (baseChangeSplittingChart (A := A) L' M' e) := by
  classical
  let j : M' →ₐ[F'] SeparableClosure F' := IsSepClosed.lift
  let : Algebra M' (SeparableClosure F') := j.toRingHom.toAlgebra
  let : IsScalarTower F' M' (SeparableClosure F') := IsScalarTower.of_algHom j
  apply (brauerEquiv F').injective
  rw [brauerContinuousEquiv_discriminantClass, discriminantClass, Brauer.scalarExtension_classOf,
    brauerContinuousEquiv_at_chart F' (SeparableClosure F') _ M'
      (baseChangeSplittingChart F' M' (discriminantSplittingChart hι hτ e))]
  erw [relativeClass_baseChangeSplittingChart (A := discriminantCSA hι hτ e) F' M'
    (discriminantSplittingChart hι hτ e)]
  rw [relativeClass_discriminantSplittingChart,
    relativeDiscriminantClass_baseChange hι hι' hιcompat hτ hτ' hτcompat e]

end Langlands.UnitaryDiscriminant
