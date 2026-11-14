import Langlands.GroupScheme.RelativeLevi.TorusLeviOverlap
import Langlands.GroupScheme.RelativeLevi.TorusLeviDescent
import Langlands.GroupScheme.RelativeLevi.TorusLeviGluing
import Langlands.GroupScheme.RelativeLevi.TorusLeviStatement

/-! # Reduction of the prescribed-torus Levi theorem to structure inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeLevi

/-- Construct the unique Levi witness containing a prescribed maximal torus
from the three explicit relative structure statements. -/
def torusLeviWitness
    (hPresentation : RelativeTorusDynamicPresentationStatement.{u})
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u})
    {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    (i : P ⟶ G) (t : T.toGrp ⟶ P) (hG : IsReductive G)
    (hP : IsRelativeParabolicSubgroup i) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t) :
    TorusLeviWitness t := by
  let : IsAffineHom P.X.hom := hP.isAffineHom
  let D := torusLeviEtaleData hPresentation hDynamic hRadical i t hG hP hT ht hmax
  exact D.witnessOfLeviRepresentative
    (D.leviRepresentative hDynamic hRadical hG hP (D.isMatching hDynamic hRadical hG))

/-- The three structure statements imply the unchanged arbitrary-base
prescribed-torus Levi proposition. -/
theorem relativeTorusLevi_of_structureStatements
    (hPresentation : RelativeTorusDynamicPresentationStatement.{u})
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u}) :
    RelativeTorusLeviStatement.{u} := by
  intro S G P i T t hG hP hT ht hmax
  let w := torusLeviWitness hPresentation hDynamic hRadical i t hG hP hT ht hmax
  exact ⟨w.group, w.inclusion, w.isLevi, w.contains, w.unique⟩

end Langlands.GroupScheme.RelativeLevi
