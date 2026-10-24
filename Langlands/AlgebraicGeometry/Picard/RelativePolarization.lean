import Langlands.AlgebraicGeometry.Picard.FieldPolarization
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChange
import Langlands.AbelianScheme.IsogenySpecialization
import Langlands.AbelianScheme.MultiplicationSign

/-! # Relative polarizations on geometric fibres -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (square : MumfordBundlePicardZeroStatement.{u})
variable (universality : PicardZeroUniversalBaseChangeStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)
variable (geometryA : DualSchemeGeometry A hA)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (stability : PicardZeroPullbackStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

/-- A relative polarization is an isogeny with an ample Mumford presentation
at every geometric fibre, after a possible extension of that fibre's field. -/
def IsPolarization (lam : A ⟶ DA) : Prop :=
  IsIsogeny lam ∧
    ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Scheme.Spec.obj (Opposite.op (CommRingCat.of K)) ⟶ S),
      HasFieldAmpleMumfordPresentation preservation square universality K ((baseChange s).obj A)
        (hasDualScheme_baseChange universality s A hA)
        (dualBaseChangeMap A hA universality s (groupHom lam).hom.hom)

/-- A principal relative polarization is a polarization which is an isomorphism. -/
def IsPrincipalPolarization (lam : A ⟶ DA) : Prop :=
  IsPolarization preservation square universality A hA geometryA MA evaluationA stability
    composition unitCoherence associativity comparison symmetry lam ∧ IsIso lam

variable (compatibility : DualAbelianBaseChangeStatement.{u})
variable (K : Type u) [Field K] [IsAlgClosed K]
variable (s : Scheme.Spec.obj (Opposite.op (CommRingCat.of K)) ⟶ S)
variable (hF : HasDualScheme ((baseChange s).obj A))
variable (geometryF : DualSchemeGeometry ((baseChange s).obj A) hF)
variable (MF : LineBundle ((relativeSpace ((baseChange s).obj A).X.hom).obj
  (dualScheme ((baseChange s).obj A) hF)))
variable (evaluationF : tensorObj (poincareFamily ((baseChange s).obj A) hF).obj.carrier MF.obj ≅
  structureSheaf ((relativeSpace ((baseChange s).obj A).X.hom).obj
    (dualScheme ((baseChange s).obj A) hF)))

/-- Each canonically transported geometric-fibre homomorphism is a field polarization. -/
lemma IsPolarization.geometricFibre {lam : A ⟶ DA}
    (h : IsPolarization preservation square universality A hA geometryA MA evaluationA stability
      composition unitCoherence associativity comparison symmetry lam) :
    IsFieldPolarization preservation square universality K ((baseChange s).obj A) hF geometryF
      MF evaluationF stability composition unitCoherence associativity comparison symmetry
      (dualAbelianBaseChangeMap preservation stability composition unitCoherence associativity
        comparison symmetry universality compatibility s A hA geometryA MA evaluationA
        hF geometryF MF evaluationF lam) := by
  let e := dualAbelianBaseChangeIso preservation stability composition unitCoherence associativity
    comparison symmetry universality compatibility s A hA geometryA MA evaluationA
    hF geometryF MF evaluationF
  let eg : ((baseChange s).obj DA).toGrp ≅
      (dualAbelianSchemeFromEvaluation ((baseChange s).obj A) hF geometryF preservation MF
        evaluationF stability composition unitCoherence associativity comparison symmetry).toGrp :=
    { hom := groupHom e.hom
      inv := groupHom e.inv
      hom_inv_id := congrArg (fun f => groupHom f) e.hom_inv_id
      inv_hom_id := congrArg (fun f => groupHom f) e.inv_hom_id }
  letI : IsIso eg.hom := eg.isIso_hom
  have he : IsIsogeny e.hom := Langlands.GroupScheme.isIsogeny_of_isIso eg.hom
  refine ⟨(h.1.baseChange s).comp he, ?_⟩
  rw [dualAbelianBaseChangeMap_hom]
  exact h.2 K s

end Langlands.AbelianScheme
