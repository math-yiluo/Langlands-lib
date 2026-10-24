import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeStatement
import Langlands.AlgebraicGeometry.Picard.AmpleMumfordBaseChange

/-! # Conditional canonical base change of dual abelian schemes -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable (universality : PicardZeroUniversalBaseChangeStatement.{u})
variable (compatibility : DualAbelianBaseChangeStatement.{u})
variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)
variable (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (hA' : HasDualScheme ((baseChange b).obj A))
variable (geometryA' : DualSchemeGeometry ((baseChange b).obj A) hA')
variable (MA' : LineBundle ((relativeSpace ((baseChange b).obj A).X.hom).obj
  (dualScheme ((baseChange b).obj A) hA')))
variable (evaluationA' : tensorObj (poincareFamily ((baseChange b).obj A) hA').obj.carrier
  MA'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj A).X.hom).obj
    (dualScheme ((baseChange b).obj A) hA')))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry

/-- The lift of the canonical scheme comparison supplied by the named compatibility theorem. -/
def dualAbelianBaseChangeIso : (baseChange b).obj DA ≅ (dualAbelianSchemeFromEvaluation ((baseChange b).obj A) hA' geometryA'
      preservation MA' evaluationA' stability composition unitCoherence associativity comparison symmetry) :=
  Classical.choose (compatibility preservation stability composition unitCoherence associativity
    comparison symmetry universality S S' b A hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA')

/-- The chosen abelian-scheme comparison has the prescribed canonical underlying map. -/
lemma dualAbelianBaseChangeIso_hom :
    (groupHom (dualAbelianBaseChangeIso preservation stability composition unitCoherence
      associativity comparison symmetry universality compatibility b A hA geometryA MA evaluationA
      hA' geometryA' MA' evaluationA').hom).hom.hom =
        (dualSchemeBaseChangeIso universality b A hA hA').hom :=
  Classical.choose_spec (compatibility preservation stability composition unitCoherence associativity
    comparison symmetry universality S S' b A hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA')

/-- Faithfulness of the underlying map makes the lift unique. -/
lemma dualAbelianBaseChangeIso_unique (e : (baseChange b).obj DA ≅ (dualAbelianSchemeFromEvaluation ((baseChange b).obj A) hA' geometryA'
      preservation MA' evaluationA' stability composition unitCoherence associativity comparison symmetry))
    (he : (groupHom e.hom).hom.hom =
      (dualSchemeBaseChangeIso universality b A hA hA').hom) :
    e = dualAbelianBaseChangeIso preservation stability composition unitCoherence associativity
      comparison symmetry universality compatibility b A hA geometryA MA evaluationA
      hA' geometryA' MA' evaluationA' := by
  apply Iso.ext
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact he.trans (dualAbelianBaseChangeIso_hom preservation stability composition unitCoherence
    associativity comparison symmetry universality compatibility b A hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA').symm

/-- Base change a homomorphism to the dual and identify its target by the canonical lift. -/
def dualAbelianBaseChangeMap (lam : A ⟶ DA) : (baseChange b).obj A ⟶ (dualAbelianSchemeFromEvaluation ((baseChange b).obj A) hA' geometryA'
      preservation MA' evaluationA' stability composition unitCoherence associativity comparison symmetry) :=
  (baseChange b).map lam ≫
    (dualAbelianBaseChangeIso preservation stability composition unitCoherence associativity
      comparison symmetry universality compatibility b A hA geometryA MA evaluationA
      hA' geometryA' MA' evaluationA').hom

/-- The transported homomorphism has the previously defined underlying scheme map. -/
lemma dualAbelianBaseChangeMap_hom (lam : A ⟶ DA) :
    (groupHom (dualAbelianBaseChangeMap preservation stability composition unitCoherence
      associativity comparison symmetry universality compatibility b A hA geometryA MA evaluationA
      hA' geometryA' MA' evaluationA' lam)).hom.hom =
        dualBaseChangeMap A hA universality b (groupHom lam).hom.hom := by
  change (Over.pullback b).map (groupHom lam).hom.hom ≫ _ = _
  rw [dualAbelianBaseChangeIso_hom]
  rfl

end Langlands.AbelianScheme
