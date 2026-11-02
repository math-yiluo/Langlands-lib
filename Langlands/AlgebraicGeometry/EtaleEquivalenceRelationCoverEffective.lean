import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineQuotientPresentation
import Langlands.AlgebraicGeometry.GroupoidCoactionEffectiveDescent
import Langlands.AlgebraicGeometry.GroupoidCoactionPushforwardCocycle

/-! # Arbitrary coactions pushed from an affine quotient cover -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E' E : EtaleEquivalenceRelation.{u}) [IsAffine E'.U] [IsAffine E.U]
  [IsAffine E.R] (f : E'.U ⟶ E.U) (g : E'.R ⟶ E.R)
  (h : E'.IsCartesianHom E f g)
  (hclosed : IsClosedImmersion (prod.lift E.t E.s)) (hQ : E'.HasAffineQuotient)
variable (M : Type (max u v)) [AddCommGroup M] [Module Γ(E'.U, ⊤) M]
variable (θ :
  letI : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
  GroupoidCoaction E'.t.appTop.hom M)

include hQ in
/-- Every coaction on an affine relation with an actual affine quotient has
degree-one vanishing. -/
theorem affineQuotient_oneCohomologyVanishes :
    letI : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
    θ.OneCohomologyVanishes := by
  letI : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
  obtain ⟨hff, e, he⟩ := invariantPresentation_of_hasAffineQuotient E' hQ
  letI : Module.FaithfullyFlat (GroupoidCoaction.invariantRing E'.t.appTop.hom)
    Γ(E'.U, ⊤) := hff
  exact GroupoidCoaction.oneCohomologyVanishes_of_faithfullyFlat_presentation
    (ringRelation_of_hasAffineQuotient E' hQ) θ e.symm
    (fun b => by rw [← he b, e.symm_apply_apply])

/-- Restrict an arbitrary covering coaction to the base object ring. -/
noncomputable def coverPushforward :
    letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
    letI : Module Γ(E.U, ⊤) M := Module.compHom M f.appTop.hom
    GroupoidCoaction E.t.appTop.hom M := by
  letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  letI : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
  letI : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(E.U, ⊤) Γ(E'.R, ⊤) :=
    ((algebraMap Γ(E'.U, ⊤) Γ(E'.R, ⊤)).comp
      (algebraMap Γ(E.U, ⊤) Γ(E'.U, ⊤))).toAlgebra
  letI : IsScalarTower Γ(E.U, ⊤) Γ(E'.U, ⊤) Γ(E'.R, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module Γ(E.U, ⊤) M := Module.compHom M f.appTop.hom
  letI : IsScalarTower Γ(E.U, ⊤) Γ(E'.U, ⊤) M :=
    ⟨fun b d m => by change (f.appTop.hom b * d) • m = _; exact mul_smul _ _ _⟩
  exact GroupoidCoaction.pushforward (sourceTensorEquiv E' E f g h)
    (sourceTensorEquiv_target E' E f g h) θ
    (etaleEquivalenceRelationRingForm E inferInstance inferInstance hclosed)
    (ringRelation_of_hasAffineQuotient E' hQ)

/-- An arbitrary covering coaction is acyclic after source-cartesian pushforward. -/
theorem coverPushforward_oneCohomologyVanishes :
    letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
    letI : Module Γ(E.U, ⊤) M := Module.compHom M f.appTop.hom
    (coverPushforward E' E f g h hclosed hQ M θ).OneCohomologyVanishes := by
  letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  letI : Algebra Γ(E'.U, ⊤) Γ(E'.R, ⊤) := E'.s.appTop.hom.toAlgebra
  letI : Algebra Γ(E.U, ⊤) Γ(E'.U, ⊤) := f.appTop.hom.toAlgebra
  letI : Algebra Γ(E.U, ⊤) Γ(E'.R, ⊤) :=
    ((algebraMap Γ(E'.U, ⊤) Γ(E'.R, ⊤)).comp
      (algebraMap Γ(E.U, ⊤) Γ(E'.U, ⊤))).toAlgebra
  letI : IsScalarTower Γ(E.U, ⊤) Γ(E'.U, ⊤) Γ(E'.R, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module Γ(E.U, ⊤) M := Module.compHom M f.appTop.hom
  letI : IsScalarTower Γ(E.U, ⊤) Γ(E'.U, ⊤) M :=
    ⟨fun b d m => by change (f.appTop.hom b * d) • m = _; exact mul_smul _ _ _⟩
  exact GroupoidCoaction.pushforward_oneCohomologyVanishes
    (sourceTensorEquiv E' E f g h) (sourceTensorEquiv_target E' E f g h) θ
    (etaleEquivalenceRelationRingForm E inferInstance inferInstance hclosed)
    (ringRelation_of_hasAffineQuotient E' hQ)
    (affineQuotient_oneCohomologyVanishes E' hQ M θ)

/-- The pushforward satisfies the published invariant-lifting acyclicity predicate. -/
theorem coverPushforward_isAcyclic :
    letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
    letI : Module Γ(E.U, ⊤) M := Module.compHom M f.appTop.hom
    (coverPushforward E' E f g h hclosed hQ M θ).IsAcyclic := by
  letI : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  letI : Module Γ(E.U, ⊤) M := Module.compHom M f.appTop.hom
  letI : Module.Flat Γ(E.U, ⊤) Γ(E.R, ⊤) := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp
      (etaleEquivalenceRelationRingForm E inferInstance inferInstance hclosed).etale_algebraMap).1
  exact GroupoidCoaction.isAcyclic_of_oneCohomologyVanishes _
    (coverPushforward_oneCohomologyVanishes E' E f g h hclosed hQ M θ)

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
