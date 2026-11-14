import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport

/-! # Transport of actual special-fibre quotients -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

namespace SpecialFibreQuotientData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G G' : GroupScheme (Spec (CommRingCat.of K))}
  {D : RelativeComponentModelData R K G} {D' : RelativeComponentModelData R K G'}

/-- Transport supplied radical and quotient data through an actual isomorphism
of neutral special fibres, retaining the same radical and quotient schemes. -/
def transportSpecialFibreIso (Q : SpecialFibreQuotientData D)
    (e : D.neutral.specialFibre ≅ D'.neutral.specialFibre) :
    SpecialFibreQuotientData D' where
  radical := Q.radical
  radicalInclusion := Q.radicalInclusion ≫ e.hom
  quotient := Q.quotient
  projection := e.inv ≫ Q.projection

@[simp] theorem transportSpecialFibreIso_radical (Q : SpecialFibreQuotientData D)
    (e : D.neutral.specialFibre ≅ D'.neutral.specialFibre) :
    (Q.transportSpecialFibreIso e).radical = Q.radical := rfl

@[simp] theorem transportSpecialFibreIso_radicalInclusion (Q : SpecialFibreQuotientData D)
    (e : D.neutral.specialFibre ≅ D'.neutral.specialFibre) :
    (Q.transportSpecialFibreIso e).radicalInclusion = Q.radicalInclusion ≫ e.hom := rfl

@[simp] theorem transportSpecialFibreIso_quotient (Q : SpecialFibreQuotientData D)
    (e : D.neutral.specialFibre ≅ D'.neutral.specialFibre) :
    (Q.transportSpecialFibreIso e).quotient = Q.quotient := rfl

@[simp] theorem transportSpecialFibreIso_projection (Q : SpecialFibreQuotientData D)
    (e : D.neutral.specialFibre ≅ D'.neutral.specialFibre) :
    (Q.transportSpecialFibreIso e).projection = e.inv ≫ Q.projection := rfl

/-- An actual neutral-special-fibre isomorphism preserves the radical,
fppf-quotient and connected-reductivity conditions. -/
theorem isReductiveQuotient_transportSpecialFibreIso (Q : SpecialFibreQuotientData D)
    (e : D.neutral.specialFibre ≅ D'.neutral.specialFibre)
    (hQ : Q.IsReductiveQuotient) : (Q.transportSpecialFibreIso e).IsReductiveQuotient := by
  refine ⟨hQ.1.comp_iso e, ?_, hQ.2.2⟩
  change RelativeRoot.IsFppfQuotient
    (SubgroupFunctor.range (Q.radicalInclusion ≫ e.hom)) (e.inv ≫ Q.projection)
  rw [SubgroupFunctor.range_comp_iso]
  exact hQ.2.1.comapIso e

/-- The transported projection recovers the original projection through the
specified neutral-special-fibre isomorphism. -/
@[simp, reassoc]
theorem transportSpecialFibreIso_hom_projection (Q : SpecialFibreQuotientData D)
    (e : D.neutral.specialFibre ≅ D'.neutral.specialFibre) :
    e.hom ≫ (Q.transportSpecialFibreIso e).projection = Q.projection := by
  simp only [transportSpecialFibreIso_projection, Iso.hom_inv_id_assoc]

/-- A torus-inclusion square induces exactly the same map to the retained
quotient scheme. -/
theorem transportSpecialFibreIso_torus_projection (Q : SpecialFibreQuotientData D)
    (e : D.neutral.specialFibre ≅ D'.neutral.specialFibre)
    {T : CommGroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    (t : T.toGrp ⟶ D.neutral.specialFibre)
    (t' : T.toGrp ⟶ D'.neutral.specialFibre) (ht : t ≫ e.hom = t') :
    t' ≫ (Q.transportSpecialFibreIso e).projection = t ≫ Q.projection := by
  rw [← ht, Category.assoc, transportSpecialFibreIso_hom_projection]

end SpecialFibreQuotientData
end Langlands.BruhatTits.IntegralModels
