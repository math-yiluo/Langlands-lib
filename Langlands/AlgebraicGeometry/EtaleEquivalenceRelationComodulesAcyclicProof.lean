import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationComodulesAcyclicStatement
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationFiniteEffectiveCover
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationRingFormProof
import Langlands.AlgebraicGeometry.GroupoidCoactionFiniteCoverVanishing

/-! # Acyclicity from finite effective covering data -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- The ring-level vanishing property yields acyclicity for an actual
finite surjective cartesian cover with affine quotient. -/
theorem EtaleEquivalenceRelation.comodulesAcyclic_of_finiteCoveredRelationsVanishing
    (E : EtaleEquivalenceRelation.{u}) [IsAffine E.U] [IsNoetherian E.U]
    [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]
    (hcover : E.HasFiniteSurjectiveCoverWithAffineQuotient)
    (hvan : GroupoidCoaction.FiniteCoveredRelationsVanishing Γ(E.U, ⊤)) :
    E.ComodulesAcyclic := by
  let : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  let : IsNoetherianRing Γ(E.U, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top E.U⟩
  obtain ⟨E', f, g, h, hf, hsurj, hQ⟩ := hcover
  let : IsFinite f := hf
  let : Surjective f := hsurj
  let X := EtaleEquivalenceRelation.finiteEffectiveCover E' E f g h hQ
  have hE : RingEtaleEquivalenceRelation E.t.appTop.hom :=
    etaleEquivalenceRelationRingForm E inferInstance inferInstance inferInstance
  intro M _ _ θ
  exact GroupoidCoaction.isAcyclic_of_finiteCoveredRelationsVanishing hE X hvan θ

/-- Every module on a finitely covered Noetherian affine étale
equivalence relation is acyclic. -/
theorem etaleEquivalenceRelationComodulesAcyclic :
    EtaleEquivalenceRelationComodulesAcyclicStatement.{u} := by
  intro E hU hN hR hj hcover
  let : IsAffine E.U := hU
  let : IsNoetherian E.U := hN
  let : IsAffine E.R := hR
  let : IsClosedImmersion (prod.lift E.t E.s) := hj
  let : IsNoetherianRing Γ(E.U, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top E.U⟩
  apply E.comodulesAcyclic_of_finiteCoveredRelationsVanishing hcover
  apply GroupoidCoaction.finiteCoveredRelationsVanishing_of_quotientCovers ?_ Γ(E.U, ⊤)
  intro S C _ _ _ t X I hI
  exact ⟨X.quotient hI⟩

end Langlands.AlgebraicGeometry
