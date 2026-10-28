import Langlands.Algebra.LocalFlatnessCriterionStatement
import Langlands.Algebra.FiniteColengthTensorInjectivityProof
import Langlands.Algebra.ArtinReesTensorKernelBoundProof
import Langlands.Algebra.IdealTensorKernelSeparationProof
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Proof of the Noetherian local flatness criterion -/

universe u v w

namespace Langlands.Algebra

private theorem maximalIdeal_lTensor_injective
    (R : Type u) (M : Type w)
    [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    (h : Function.Injective
      (LinearMap.rTensor M (IsLocalRing.maximalIdeal R).subtype)) :
    Function.Injective
      (LinearMap.lTensor M (IsLocalRing.maximalIdeal R).subtype) :=
  (LinearMap.lTensor_inj_iff_rTensor_inj _ _).mpr h

private theorem maximalIdeal_map_le_jacobson
    (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤
      (⊥ : Ideal S).jacobson :=
  (IsLocalRing.map_maximalIdeal_le (algebraMap R S)).trans
    (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal S))

/-- Stacks Project, Lemma 10.99.7 (00MK), assembled from finite-colength
tensor injectivity, Artin–Rees kernel bounds and mixed-scalar separation. -/
theorem localFlatnessCriterion : LocalFlatnessCriterionStatement.{u, v, w} := by
  intro R S M _ _ _ _ _ _ _ _ _ _ _ _ _ h
  exact idealTensorKernelSeparation R S M (IsLocalRing.maximalIdeal R)
    (maximalIdeal_map_le_jacobson R S)
    (artinReesTensorKernelBound R M (IsLocalRing.maximalIdeal R)
      (finiteColengthTensorInjectivity R M
        (maximalIdeal_lTensor_injective R M h)))

end Langlands.Algebra
