import Langlands.LocalFactor.Ramification.InertiaPresentationStatement
import Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof
import Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof

/-!
# Inertia surjectivity, finite presentations and conductor independence: proof

This module proves
`Langlands.Ramification.Padic.InertiaSurjectivityPresentationAndConductorIndependenceStatement`
at independent universe levels for the p-adic field and the two representation carriers.
Clauses 1–5 and the refinement clause are published theorems. The compositum clause
identifies the two pullbacks with descents at refined presentations. The equivalence
clause transports a presentation of `A` along the equivalence to a presentation of `B`
on the same finite field, and then compares two presentations of `B`.
-/

noncomputable section

namespace Langlands.Ramification.Padic

open Weil.Local

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Any two finite inertia presentations of the same Weil representation give the same
Artin and Swan sums. -/
theorem finiteInertiaConductorIndependence
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) :
    FiniteInertiaConductorIndependenceStatement F A :=
  fun P Q hP hQ => presentation_conductors_eq F A P Q hP hQ

/-- The pullbacks of two presentations to the compositum of their fields have the Artin
and Swan sums of the original presentations. -/
theorem finiteInertiaConductorCompositum
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)) :
    FiniteInertiaConductorCompositumStatement F A := by
  intro P Q hP hQ
  have hR := HerbrandBridge.weilInertiaRestriction_surjective F (P.extension ⊔ Q.extension)
  have hl : (FiniteInertiaCommonRefinement.compositum F A P Q).leftRepresentation hP =
      (P.refine (P.extension ⊔ Q.extension) le_sup_left).representation hR :=
    (P.representation_refine hP (P.extension ⊔ Q.extension) le_sup_left hR).symm
  have hr : (FiniteInertiaCommonRefinement.compositum F A P Q).rightRepresentation hQ =
      (Q.refine (P.extension ⊔ Q.extension) le_sup_right).representation hR :=
    (Q.representation_refine hQ (P.extension ⊔ Q.extension) le_sup_right hR).symm
  obtain ⟨hPa, hPs⟩ := finiteInertiaConductorRefinement F A P _ le_sup_left hP hR
  obtain ⟨hQa, hQs⟩ := finiteInertiaConductorRefinement F A Q _ le_sup_right hQ hR
  exact ⟨(congrArg (inertiaArtinConductor _ F.Carrier) hl).trans hPa,
    (congrArg (inertiaSwanConductor _ F.Carrier) hl).trans hPs,
    (congrArg (inertiaArtinConductor _ F.Carrier) hr).trans hQa,
    (congrArg (inertiaSwanConductor _ F.Carrier) hr).trans hQs⟩

/-- An equivalence of Weil representations restricts to an equivalence of their
restrictions to the local Weil inertia group, with the same linear map. -/
def localInertiaRepresentationEquiv
    {A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)}
    {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
    (e : FiniteRepresentation.Equiv A B) :
    (localInertiaRepresentation F A).Equiv (localInertiaRepresentation F B) :=
  Representation.Equiv.mk e.toLinearEquiv fun g => e.isIntertwining' g

/-- Equivalent Weil representations, presented on arbitrary finite fields, have the same
Artin and Swan sums. -/
theorem finiteInertiaConductorEquivalence
    (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))
    (B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)) :
    FiniteInertiaConductorEquivalenceStatement F A B := by
  intro e P Q hP hQ
  let T := (absoluteFiniteExtension F P.extension).canonicalTopologicalData
  let π := (weilInertiaRestriction F P.extension).toMonoidHom
  let e' := localInertiaRepresentationEquiv F e
  have hB : π.ker ≤ (localInertiaRepresentation F B).ker :=
    kernel_le_of_equiv T F.Carrier π P.kernel_le e'
  let P' : FiniteInertiaPresentation F B := ⟨P.extension, hB⟩
  obtain ⟨ha, hs⟩ := presentation_conductors_eq F B P' Q hP hQ
  exact ⟨(artinConductorOfQuotient_equiv T F.Carrier π hP P.kernel_le hB e').trans ha,
    (swanConductorOfQuotient_equiv T F.Carrier π hP P.kernel_le hB e').trans hs⟩

/-- The nine clauses of the inertia surjectivity, presentation and conductor
independence statement, at independent field and carrier universes. -/
theorem inertiaSurjectivityPresentationAndConductorIndependence :
    InertiaSurjectivityPresentationAndConductorIndependenceStatement.{uF, uV, uW} := by
  intro p _ F
  exact ⟨HerbrandBridge.absoluteInertiaRestriction_surjective F,
    HerbrandBridge.weilInertiaRestriction_surjective F,
    HerbrandBridge.finiteInertiaRestriction_surjective F,
    fun A => ⟨HerbrandBridge.continuousWeilFiniteInertiaImage F A,
      HerbrandBridge.continuousWeilFiniteInertiaPresentation F A,
      finiteInertiaConductorRefinement F A,
      finiteInertiaConductorCompositum F A,
      finiteInertiaConductorIndependence F A⟩,
    fun A B => finiteInertiaConductorEquivalence F A B⟩

end Langlands.Ramification.Padic
