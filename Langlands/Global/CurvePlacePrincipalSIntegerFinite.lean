import Langlands.Global.CurvePlacePrincipalSInteger
import Langlands.Global.CurvePlaceSIntegerIntegralClosure
import Langlands.Global.IntegralClosureFractionTensor
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Module

noncomputable section

universe u

open IsDedekindDomain IntermediateField AlgebraicCurve
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global.FiniteConstantCurveChart Langlands.Global TensorProduct

namespace Langlands.Global

namespace CurvePlacePrincipalSIntegers

variable (k K : Type u) [Field k] [Finite k] [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  (s : K) [FiniteDimensional k⟮s⟯ K] (t : CurveModel.chartRing k ({s} : Set K))

/-- The actual normalized chart includes in its original principal outside-set integer ring. -/
def chartMap : CurveModel.chartRing k ({s} : Set K) →+*
    curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)) :=
  (CurveModel.chartRing k ({s} : Set K)).val.toRingHom.codRestrict _ fun a p hp => by
    have hs : s ∈ p.toValuationSubring := by
      by_contra hs
      exact hp ((mem_curvePlacePrincipalExceptional k K s (t : K) p).mpr (Or.inl hs))
    exact CurveModel.chartRing_le_valuationSubring p.toValuationSubring
      p.algebraMap_mem' (Set.singleton_subset_iff.mpr hs) a.property

scoped instance chartAlgebra : Algebra (CurveModel.chartRing k ({s} : Set K))
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) :=
  (chartMap k K s t).toAlgebra

scoped instance chartTower : IsScalarTower (CurveModel.chartRing k ({s} : Set K))
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) K :=
  .of_algebraMap_eq fun _ => rfl

scoped instance constantTower : IsScalarTower k (CurveModel.chartRing k ({s} : Set K))
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) :=
  .of_algebraMap_eq fun _ => rfl

variable [Fact (t ≠ 0)]

scoped instance localization : IsLocalization (Submonoid.powers t)
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) := by
  let C := CurveModel.chartRing k ({s} : Set K)
  let R := curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))
  let D := dedekindAwaySubalgebra (K := K) t (Fact.out : t ≠ 0)
  let : IsLocalization (Submonoid.powers t) D :=
    Localization.subalgebra.isLocalization_ofField K _ _
  let e : D ≃ₐ[C] R :=
    { toRingEquiv := (curvePlacePrincipalSIntegersEquiv k K s t Fact.out).symm
      commutes' a := by apply Subtype.ext; rfl }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers t) e

scoped instance fractionRing : IsFractionRing
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers t) _ K

scoped instance dedekind : IsDedekindDomain
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) :=
  IsLocalization.isDedekindDomain (CurveModel.chartRing k ({s} : Set K))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Fact.out : t ≠ 0)) _

scoped instance finiteType : Algebra.FiniteType k
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) := by
  let C := CurveModel.chartRing k ({s} : Set K)
  let R := curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))
  let : Algebra.FinitePresentation C R := IsLocalization.Away.finitePresentation t
  exact (inferInstance : Algebra.FiniteType k C).trans
    (inferInstance : Algebra.FiniteType C R)

variable (L : Type u) [Field L] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L]

scoped instance isIntegralClosure : IsIntegralClosure
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K))))
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    change x ∈ (integralClosure
      (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) L).toSubring ↔ _
    rw [curvePlaceSIntegers_integralClosure_eq]
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.property⟩

scoped instance finite : Module.Finite
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) := by
  let R := curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))
  let B := curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
    (curvePlacePrincipalExceptional k K s (t : K)))
  let : Module.Finite ℤ k := inferInstance
  let : Algebra.FiniteType ℤ k := inferInstance
  let : Algebra.FiniteType ℤ R := (inferInstance : Algebra.FiniteType ℤ k).trans
    (inferInstance : Algebra.FiniteType k R)
  let : Module.Finite R (integralClosure R L) :=
    Langlands.AlgebraicGeometry.NoetherianApproximation.finite_integralClosure_of_normal_integer_finiteType
      R K L
  exact Module.Finite.equiv (IsIntegralClosure.equiv R (integralClosure R L) L B).toLinearEquiv

scoped instance torsionFree : Module.IsTorsionFree
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) := by
  let R := curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))
  let : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  exact IsIntegralClosure.isTorsionFree R L

scoped instance projective : Module.Projective
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) := by
  let R := curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))
  let B := curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
    (curvePlacePrincipalExceptional k K s (t : K)))
  let : Module.FinitePresentation R B := Module.finitePresentation_of_finite R B
  exact Module.Flat.projective_of_finitePresentation

scoped instance upperFractionRing : IsFractionRing
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) K L _

end CurvePlacePrincipalSIntegers

open scoped CurvePlacePrincipalSIntegers

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]

/-- Every original lower prime localization of the actual upper integer module is free. -/
theorem curvePlacePrincipalSIntegers_local_free
    (p : Ideal (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))))
    [p.IsPrime] : Module.Free (Localization.AtPrime p)
      (LocalizedModule p.primeCompl
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K))))) :=
  Module.free_of_flat_of_isLocalRing

/-- The generic module rank is the degree of the original finite extension. -/
theorem curvePlacePrincipalSIntegers_finrank_eq :
    Module.finrank (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) = Module.finrank K L :=
  (IsFractionRing.finrank_eq
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) K
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) L).symm

/-- The original generic-fiber algebra of the actual curve S-integer extension. -/
def curvePlacePrincipalSIntegersFractionTensorEquiv :
    K ⊗[curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))]
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) ≃ₐ[K] L :=
  integralClosureFractionTensorEquiv
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ K L

@[simp]
theorem curvePlacePrincipalSIntegersFractionTensorEquiv_tmul (a : K)
    (b : curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) :
    curvePlacePrincipalSIntegersFractionTensorEquiv k K L s t
      (a ⊗ₜ[curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))] b) =
      algebraMap K L a * (b : L) :=
  integralClosureFractionTensorEquiv_tmul
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ K L a b

end Langlands.Global
