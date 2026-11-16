import Langlands.BruhatTits.IntegralModels.IntegralRootFiltration
import Langlands.BruhatTits.IntegralModels.IntegralTorus
import Langlands.BruhatTits.IntegralModels.Transport.Model

/-! # The supplied split integral torus as torus data of a component-model pair -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme

section SplitTorus

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}

/-- A split integral torus of the neutral model of a model pair, regarded as
integral torus data of the pair: the same torus and inclusion, with the generic
identification on underlying group schemes. -/
def IntegralSplitTorusData.toIntegralTorusData {D : RelativeComponentModelData R K G}
    (A : IntegralSplitTorusData D.neutral i) : IntegralTorusData D S i where
  torus := A.torus
  genericIso := underlyingTorusIso A.genericIso
  inclusion := A.inclusion
  generic_comm := A.generic_comm

namespace IntegralSplitTorusData

variable {D : RelativeComponentModelData R K G} (A : IntegralSplitTorusData D.neutral i)

@[simp] theorem toIntegralTorusData_torus : A.toIntegralTorusData.torus = A.torus := rfl

@[simp] theorem toIntegralTorusData_inclusion :
    A.toIntegralTorusData.inclusion = A.inclusion := rfl

theorem toIntegralTorusData_genericIso_hom :
    A.toIntegralTorusData.genericIso.hom = CommGroupScheme.groupHom A.genericIso.hom := rfl

theorem toIntegralTorusData_genericIso_inv :
    A.toIntegralTorusData.genericIso.inv = CommGroupScheme.groupHom A.genericIso.inv := rfl

end IntegralSplitTorusData

end SplitTorus

end Langlands.BruhatTits.IntegralModels
