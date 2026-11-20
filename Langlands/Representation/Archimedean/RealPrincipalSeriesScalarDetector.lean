import Langlands.Representation.Archimedean.RealBottomMinorJacquet
import Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionReduction
import Langlands.Representation.Archimedean.RealLinkedJacquetPairReduction

/-! # Scalar commutants from detecting intertwiners by a single coefficient -/

noncomputable section

open Matrix
open scoped TensorProduct

namespace Langlands.Archimedean.RealPrincipalSeriesScalarDetector

open Langlands.LocalFactor.Archimedean
open RealTemperedCommutantReduction RealBottomMinorProducts RealBottomMinorJacquet
open RealTiedMinorScalar RealTiedMinorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {ds source target : List RealBlock}

/-- A scalar-valued linear map that detects all nonzero intertwiners from
the source to the target forces scalarity in any module interposed by a
surjective and an injective intertwiner. -/
theorem hasScalarCommutant_of_linearDetector
    (hQ : RealSurjectiveIntertwinerExists n source ds)
    (hJ : RealInjectiveIntertwinerExists n ds target)
    (D : (KF n source →ₗ[ℂ] KF n target) →ₗ[ℂ] ℂ)
    (hD : ∀ U : KF n source →ₗ[ℂ] KF n target, U ≠ 0 →
      (∀ k v, U (realStandardRep n source k v) = realStandardRep n target k (U v)) →
      (∀ (X : Matrix (Fin n) (Fin n) ℝ) v,
        U (realStandardLie n source (1 ⊗ₜ X) v) =
          realStandardLie n target (1 ⊗ₜ X) (U v)) → D U ≠ 0) :
    HasScalarCommutant n ds := by
  obtain ⟨Q, hQs, hQ⟩ := hQ
  obtain ⟨J, hJi, hJ⟩ := hJ
  let L : Module.End ℂ (KF n ds) →ₗ[ℂ] (KF n source →ₗ[ℂ] KF n target) :=
    { toFun := fun E => J.comp (E.comp Q)
      map_add' := fun _ _ => LinearMap.ext fun v => by simp
      map_smul' := fun _ _ => LinearMap.ext fun v => by simp }
  have hLi : Function.Injective L := by
    intro E G h
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := hQs v
    exact hJi (DFunLike.congr_fun h w)
  have hker (E : Module.End ℂ (KF n ds))
      (hK : ∀ k v, E (realStandardRep n ds k v) = realStandardRep n ds k (E v))
      (hLie : ∀ Z v, E (realStandardLie n ds Z v) = realStandardLie n ds Z (E v))
      (h0 : D (L E) = 0) : E = 0 := by
    by_contra he
    have hL0 : L E ≠ 0 := by
      intro h
      exact he (hLi (h.trans (map_zero L).symm))
    exact hD (L E) hL0
      (by intro k v; simp only [L, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
            hQ.map_realStandardRep, hK, hJ.map_realStandardRep])
      (by intro X v; simp only [L, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
            hQ.map_realStandardLie, hLie, hJ.map_realStandardLie])
      h0
  intro E hK hLie
  let I : Module.End ℂ (KF n ds) := LinearMap.id
  by_cases hI : D (L I) = 0
  · have hIz : I = 0 := hker I (by simp [I]) (by simp [I]) hI
    refine ⟨0, fun v => ?_⟩
    have hv : v = 0 := DFunLike.congr_fun hIz v
    rw [hv, map_zero, smul_zero]
  · let c := D (L E) / D (L I)
    have h0 : D (L (E - c • I)) = 0 := by
      change (D.comp L) (E - c • I) = 0
      rw [map_sub (D.comp L), map_smul, smul_eq_mul]
      change D (L E) - (D (L E) / D (L I)) * D (L I) = 0
      rw [div_mul_cancel₀ _ hI, sub_self]
    have hz : E - c • I = 0 := hker _ (by
      intro k v
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, I, LinearMap.id_apply,
        hK, map_sub, map_smul]) (by
      intro Z v
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, I, LinearMap.id_apply,
        hLie, map_sub, map_smul]) h0
    have he : E = c • I := sub_eq_zero.mp hz
    refine ⟨c, fun v => ?_⟩
    simpa only [LinearMap.smul_apply, I, LinearMap.id_apply] using DFunLike.congr_fun he v

variable {q : ℕ} {degree : Fin q → ℕ} {es : List RealBlock}
  (hsource : IsPrincipal source) (hes : IsPrincipal es) (R : Selection n degree)
  (hBottom : ∀ t, IsBottom (R t).val)
  (hShift : ∀ a : Fin n → ℝˣ,
    principalSeriesCharacter ℝ n (realPositionCharacter source) a =
      principalSeriesCharacter ℝ n (realPositionCharacter es) a * diagonalFactor R a)

/-- Evaluation of one bottom-minor coefficient on a fixed source vector,
viewed as a linear map on the space of donor-to-receiver maps. -/
def coefficientDetector (C : Selection n degree) (T : KF n es) :
    (KF n source →ₗ[ℂ] KF n target) →ₗ[ℂ] ℂ :=
  (kFiniteEval (realStandardModule n target) 1).comp
    (LinearMap.applyₗ (multiply hsource hes R C hBottom hShift T))

theorem coefficientDetector_apply (C : Selection n degree) (T : KF n es)
    (U : KF n source →ₗ[ℂ] KF n target) :
    coefficientDetector hsource hes R hBottom hShift C T U =
      coefficientFunctional hsource hes R hBottom hShift U C T := rfl

/-- If one column configuration and one vector detect all nonzero exact
intertwiners, the standard module between the two series has scalar
commutant. -/
theorem hasScalarCommutant_of_coefficientDetector
    (hQ : RealSurjectiveIntertwinerExists n source ds)
    (hJ : RealInjectiveIntertwinerExists n ds target)
    (C : Selection n degree) (T : KF n es)
    (hD : ∀ U : KF n source →ₗ[ℂ] KF n target, U ≠ 0 →
      (∀ k v, U (realStandardRep n source k v) = realStandardRep n target k (U v)) →
      (∀ (X : Matrix (Fin n) (Fin n) ℝ) v,
        U (realStandardLie n source (1 ⊗ₜ X) v) =
          realStandardLie n target (1 ⊗ₜ X) (U v)) →
      coefficientFunctional hsource hes R hBottom hShift U C T ≠ 0) :
    HasScalarCommutant n ds :=
  hasScalarCommutant_of_linearDetector hQ hJ
    (coefficientDetector hsource hes R hBottom hShift C T) hD

end Langlands.Archimedean.RealPrincipalSeriesScalarDetector
