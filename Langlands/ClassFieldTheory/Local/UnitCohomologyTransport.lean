import Langlands.ClassFieldTheory.Local.ClosureCoefficients
import Langlands.Cohomology.Continuous.EquivalenceTransport
import Langlands.Galois.Local.AbsoluteProof

/-! # Transport of continuous field-unit cohomology -/

noncomputable section

open CategoryTheory Langlands.Continuous Langlands.LocalGalois

namespace Langlands.ClassFieldTheory.Local

universe u

section Krull

variable {K E S T : Type u} [Field K] [Field E] [Field S] [Field T]
  [Algebra K S] [Algebra E T] [Algebra.IsAlgebraic K S] [Algebra.IsAlgebraic E T]
  (b : K ≃+* E) (e : S ≃+* T)
  (he : ∀ x, e (algebraMap K S x) = algebraMap E T (b x))

/-- Conjugation by a compatible field isomorphism is an isomorphism of Krull groups. -/
def krullAutContinuousEquiv : Gal(S/K) ≃ₜ* Gal(T/E) where
  __ := semilinearAutCongr b e he
  continuous_toFun := semilinearAutCongr_continuous b e he
  continuous_invFun := by
    have hi (y : E) : e.symm (algebraMap E T y) = algebraMap K S (b.symm y) := by
      apply e.injective
      rw [e.apply_symm_apply, he, b.apply_symm_apply]
    exact semilinearAutCongr_continuous b.symm e.symm hi

omit [Algebra.IsAlgebraic K S] [Algebra.IsAlgebraic E T] in
private def unitTransportLinearEquiv : Additive Sˣ ≃ₗ[IntegerScalars.{u}] Additive Tˣ :=
  (Units.mapEquiv e.toMulEquiv).toAdditive.toIntLinearEquiv.restrictScalars IntegerScalars.{u}

theorem krullAutContinuousEquiv_apply (σ : Gal(S/K)) (x : S) :
    krullAutContinuousEquiv b e he σ (e x) = e (σ x) := by
  change e (σ (e.symm (e x))) = _
  rw [e.symm_apply_apply]

theorem krullAutContinuousEquiv_symm_apply (σ : Gal(T/E)) (x : S) :
    e ((krullAutContinuousEquiv b e he).symm σ x) = σ (e x) := by
  change e (e.symm (σ (e x))) = _
  rw [e.apply_symm_apply]

/-- Transport on the coefficient units for the conjugation of the Krull groups. -/
def discreteUnitsTransportIso :
    TopRep.res ((krullAutContinuousEquiv b e he).symm : Gal(T/E) →ₜ* Gal(S/K))
      (discreteUnitsRepresentation K S) ≅ discreteUnitsRepresentation E T where
  hom.hom' :=
    { toContinuousLinearMap :=
        { toLinearMap := (unitTransportLinearEquiv e).toLinearMap
          cont := continuous_of_discreteTopology }
      isIntertwining' σ := by
        apply ContinuousLinearMap.ext
        intro x
        apply Units.ext
        exact krullAutContinuousEquiv_symm_apply b e he σ x.val }
  inv.hom' :=
    { toContinuousLinearMap :=
        { toLinearMap := (unitTransportLinearEquiv e).symm.toLinearMap
          cont := continuous_of_discreteTopology }
      isIntertwining' σ := by
        apply ContinuousLinearMap.ext
        intro x
        apply Units.ext
        apply e.injective
        change e (e.symm (σ x.val)) =
          e ((krullAutContinuousEquiv b e he).symm σ (e.symm x.val))
        rw [krullAutContinuousEquiv_symm_apply, e.apply_symm_apply, e.apply_symm_apply] }
  hom_inv_id := by
    ext x
    exact (unitTransportLinearEquiv e).symm_apply_apply x
  inv_hom_id := by
    ext x
    exact (unitTransportLinearEquiv e).apply_symm_apply x

theorem discreteUnitsTransportIso_hom_val (x : Additive Sˣ) :
    ((discreteUnitsTransportIso b e he).hom.hom x : Additive Tˣ).val = e x.val := rfl

theorem discreteUnitsTransportIso_inv_val (x : Additive Tˣ) :
    ((discreteUnitsTransportIso b e he).inv.hom x : Additive Sˣ).val = e.symm x.val := rfl

/-- Transport of actual continuous cohomology with discrete field-unit coefficients. -/
def unitCohomologyIsoOfRingEquiv (q : ℕ) :
    continuousCohomology q (discreteUnitsRepresentation K S) ≅
      continuousCohomology q (discreteUnitsRepresentation E T) :=
  continuousCohomologyIso (krullAutContinuousEquiv b e he).symm
    (discreteUnitsTransportIso b e he) q

end Krull

end Langlands.ClassFieldTheory.Local
