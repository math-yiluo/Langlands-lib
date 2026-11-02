import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineQuotientPresentation
import Langlands.AlgebraicGeometry.GroupoidCoactionPushforwardCocycle

/-! # Acyclic induced modules pushed from an affine quotient cover -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E' E : EtaleEquivalenceRelation.{u}) [IsAffine E'.U] [IsAffine E.U]
  [IsAffine E.R] (f : E'.U ⟶ E.U) (g : E'.R ⟶ E.R)
  (h : E'.IsCartesianHom E f g)
  (hclosed : IsClosedImmersion (prod.lift E.t E.s)) (hQ : E'.HasAffineQuotient)

variable (N : Type v) [AddCommGroup N]
  [Module (letI : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
    GroupoidCoaction.invariantRing E'.t.appTop.hom) N]

/-- The coaction on an induced covering module, restricted to the base object
ring through the source-cartesian scheme square. -/
noncomputable def coverInduced :
    letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
    letI : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
    letI : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
    GroupoidCoaction E.t.appTop.hom
      (Γ(E'.U, ⊤) ⊗[GroupoidCoaction.invariantRing E'.t.appTop.hom] N) := by
  letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  letI : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
  letI : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(E.U, ⊤) Γ(E'.R, ⊤) :=
    ((algebraMap Γ(E'.U, ⊤) Γ(E'.R, ⊤)).comp
      (algebraMap Γ(E.U, ⊤) Γ(E'.U, ⊤))).toAlgebra
  letI : IsScalarTower Γ(E.U, ⊤) Γ(E'.U, ⊤) Γ(E'.R, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact GroupoidCoaction.pushforward (sourceTensorEquiv E' E f g h)
    (sourceTensorEquiv_target E' E f g h) (GroupoidCoaction.induced E'.t.appTop.hom N)
    (etaleEquivalenceRelationRingForm E inferInstance inferInstance hclosed)
    (ringRelation_of_hasAffineQuotient E' hQ)

/-- The induced covering coaction has degree-one vanishing after pushforward. -/
theorem coverInduced_oneCohomologyVanishes :
    let : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
    let : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
    let : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
    (coverInduced E' E f g h hclosed hQ N).OneCohomologyVanishes := by
  let : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  let : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
  let : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(E.U, ⊤) Γ(E'.R, ⊤) :=
    ((algebraMap Γ(E'.U, ⊤) Γ(E'.R, ⊤)).comp
      (algebraMap Γ(E.U, ⊤) Γ(E'.U, ⊤))).toAlgebra
  let : IsScalarTower Γ(E.U, ⊤) Γ(E'.U, ⊤) Γ(E'.R, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hff, e, he⟩ := invariantPresentation_of_hasAffineQuotient E' hQ
  let : Module.FaithfullyFlat (GroupoidCoaction.invariantRing E'.t.appTop.hom)
    Γ(E'.U, ⊤) := hff
  exact GroupoidCoaction.pushforward_induced_oneCohomologyVanishes
    (sourceTensorEquiv E' E f g h) (sourceTensorEquiv_target E' E f g h)
    (etaleEquivalenceRelationRingForm E inferInstance inferInstance hclosed)
    (ringRelation_of_hasAffineQuotient E' hQ) e he N

/-- The pushed induced module satisfies the published invariant-lifting definition of acyclicity. -/
theorem coverInduced_isAcyclic :
    let : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
    let : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
    let : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
    (coverInduced E' E f g h hclosed hQ N).IsAcyclic := by
  let : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  let : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
  let : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(E.U, ⊤) Γ(E'.R, ⊤) :=
    ((algebraMap Γ(E'.U, ⊤) Γ(E'.R, ⊤)).comp
      (algebraMap Γ(E.U, ⊤) Γ(E'.U, ⊤))).toAlgebra
  let : IsScalarTower Γ(E.U, ⊤) Γ(E'.U, ⊤) Γ(E'.R, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hff, e, he⟩ := invariantPresentation_of_hasAffineQuotient E' hQ
  let : Module.FaithfullyFlat (GroupoidCoaction.invariantRing E'.t.appTop.hom)
    Γ(E'.U, ⊤) := hff
  exact GroupoidCoaction.pushforward_induced_isAcyclic
    (sourceTensorEquiv E' E f g h) (sourceTensorEquiv_target E' E f g h)
    (etaleEquivalenceRelationRingForm E inferInstance inferInstance hclosed)
    (ringRelation_of_hasAffineQuotient E' hQ) e he N

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
