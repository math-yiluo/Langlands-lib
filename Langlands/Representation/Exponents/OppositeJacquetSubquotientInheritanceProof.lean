import Langlands.Representation.Exponents.OppositeJacquetSubquotientInheritanceStatement
import Langlands.Representation.Parabolic.OppositeRefinementExactnessProof
import Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof
import Langlands.Representation.Parabolic.FlattenedOppositeJacquetComparisonProof
import Langlands.Representation.Exponents.DualJacquetFinitenessProof
import Langlands.Representation.Exponents.ScalarSubquotientDualSpectrumProof

noncomputable section

namespace Langlands

open GeneralLinear Geometric

/-- Actual refined opposite eigenfunctionals of arbitrary Jacquet subquotients
occur among the flattened opposite dual exponents. -/
theorem glOppositeJacquetSubquotientExponentInheritance.{uField, uSource, uSubquotient} :
    GLOppositeJacquetSubquotientExponentInheritanceStatement.{uField, uSource, uSubquotient} := by
  intro p hp F T
  let := T.topology
  intro n hn C A hAirr hA S hS D ψ φ hψ hφ heigen
  obtain ⟨U, q, hq⟩ := hS
  let O := CuspidalJacquetMultiplicity.oppositeJacquet T C A
  let i : U.toRepresentation.IntertwiningMap O.ρ :=
    { toLinearMap := U.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hO : IsAdmissible O.ρ :=
    Parabolic.isAdmissible_standardOppositeJacquet F T C A A.ρ hA
  let iq := T.normalizedRefinedOppositeJacquetMap C D i
  have hiq : Function.Injective iq :=
    T.normalizedRefinedOppositeJacquetMap_injective C D i hO.1 Subtype.val_injective
  let rq := T.normalizedRefinedOppositeJacquetMap C D q
  have hrq : Function.Surjective rq := by
    intro y
    obtain ⟨s, rfl⟩ := refinedOppositeJacquetMk_surjective C D S.ρ y
    obtain ⟨u, rfl⟩ := hq s
    exact ⟨refinedOppositeJacquetMk C D U.toRepresentation u, rfl⟩
  obtain ⟨Et, _⟩ :=
    Parabolic.normalizedOppositeRefinementTransitivity p F T n C D A
  obtain ⟨Ef, _⟩ :=
    Parabolic.flattenedOppositeJacquetComparison.{uField, uField, uSource}.2 p F T n C D A
  let scalars := (flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
    ((C.flatten D).blockScalarLevi F.Carrier)
  let R : Representation ℂ (Fin (C.flatten D).length → F.Carrierˣ)
      (RefinedOppositeJacquetModule C D U.toRepresentation) :=
    (T.normalizedRefinedOppositeJacquet C D U.toRepresentation).comp scalars
  let J : R.IntertwiningMap (T.splitCentreOppositeJacquet (C.flatten D) A).ρ :=
    { toLinearMap := Ef.toLinearMap.comp (Et.toLinearMap.comp iq.toLinearMap)
      isIntertwining' := by
        intro a
        apply LinearMap.ext
        intro x
        change Ef (Et (iq (T.normalizedRefinedOppositeJacquet C D U.toRepresentation
          (scalars a) x))) =
          (CuspidalJacquetMultiplicity.oppositeJacquet T (C.flatten D) A).ρ
            ((C.flatten D).blockScalarLevi F.Carrier a) (Ef (Et (iq x)))
        rw [Representation.IntertwiningMap.isIntertwining _ _ iq]
        exact (congrArg (fun y => Ef y)
          (Representation.IntertwiningMap.isIntertwining _ _ Et.toIntertwiningMap
            (scalars a) (iq x))).trans
            (Representation.IntertwiningMap.isIntertwining _ _ Ef.toIntertwiningMap
              ((C.flatten D).blockScalarLevi F.Carrier a) (Et (iq x))) }
  have hJ : Function.Injective J :=
    Ef.toLinearEquiv.injective.comp (Et.toLinearEquiv.injective.comp hiq)
  let e : RefinedOppositeJacquetModule C D U.toRepresentation ≃ₗ[ℂ] J.range.toSubmodule :=
    LinearEquiv.ofInjective J.toLinearMap hJ
  have he (a : Fin (C.flatten D).length → F.Carrierˣ)
      (x : RefinedOppositeJacquetModule C D U.toRepresentation) :
      e (R a x) = J.range.toRepresentation a (e x) := by
    apply Subtype.ext
    exact DFunLike.congr_fun (J.isIntertwining' a) x
  have heigen' (a : Fin (C.flatten D).length → F.Carrierˣ)
      (y : RefinedOppositeJacquetModule C D S.ρ) :
      φ (T.normalizedRefinedOppositeJacquet C D S.ρ (scalars a) y) =
        (ψ a : ℂ) * φ y := by
    obtain ⟨s, rfl⟩ := refinedOppositeJacquetMk_surjective C D S.ρ y
    exact heigen a s
  let f : J.range.toSubmodule →ₗ[ℂ] ℂ :=
    (φ.comp rq.toLinearMap).comp e.symm.toLinearMap
  have hf : Function.Surjective f :=
    (LinearMap.surjective_iff_ne_zero.mpr hφ).comp (hrq.comp e.symm.surjective)
  have hscalar (a : Fin (C.flatten D).length → F.Carrierˣ)
      (u : J.range.toSubmodule) :
      f (J.range.toRepresentation a u) = (ψ a : ℂ) • f u := by
    obtain ⟨x, rfl⟩ := e.surjective u
    rw [← he]
    change φ (rq (e.symm (e (R a x)))) =
      (ψ a : ℂ) * φ (rq (e.symm (e x)))
    simp only [LinearEquiv.symm_apply_apply]
    change φ (rq (T.normalizedRefinedOppositeJacquet C D U.toRepresentation
      (scalars a) x)) = (ψ a : ℂ) * φ (rq x)
    rw [Representation.IntertwiningMap.isIntertwining _ _ rq]
    exact heigen' a (rq x)
  have hspan := (glDualJacquetFiniteness p F T n hn (C.flatten D) A hAirr hA).2.2
  have hdet := scalarSubquotientDualSpectrum ℂ
    (Fin (C.flatten D).length → F.Carrierˣ)
    (T.splitCentreOppositeJacquet (C.flatten D) A)
    (T.splitCentreOppositeJacquet (C.flatten D) A).ρ
    (T.IsDualJacquetExponent (C.flatten D) A) hspan ψ J.range ℂ f hf hscalar
  exact ⟨hψ, hdet.2⟩

end Langlands
