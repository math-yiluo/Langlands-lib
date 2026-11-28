import Langlands.GroupScheme.AutomorphicAction.SemidirectFactorization
import Langlands.GroupScheme.Dynamic.CentralizerAdjointAction
import Langlands.GroupScheme.Rational.LeviMultiplication

/-! # The semidirect product decomposition of represented dynamic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} {χ : (Gm S).toGrp ⟶ G}
  [IsSeparated G.X.hom] {P Z U : GroupScheme S}
  {iP : P ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
  (hP : (parabolic χ).IsRepresentedBy iP) (hZ : (centralizer χ).IsRepresentedBy iZ)
  (hU : (unipotent χ).IsRepresentedBy iU)

private def semidirectProductIsoWithHom :
    { e : (centralizerAdjointAction hZ hU).semidirectProduct ≅ P //
      e.hom.hom.hom = multiplication hP hZ hU } := by
  let levi := centralizerToParabolic hP hZ
  let unipotentInclusion := (unipotentIsoKernel (hP := hP) (hZ := hZ) hU).hom ≫
    kernelι (limitGroupHom hP hZ)
  have hLevi : levi ≫ iP = iZ := centralizerToParabolic_comp hP hZ
  have hUnipotent : unipotentInclusion ≫ iP = iU := by
    simpa only [unipotentInclusion, Category.assoc] using
      unipotentIsoKernel_hom_comp (hP := hP) (hZ := hZ) hU
  have hAction (T : Over S) (z : T ⟶ Z.X) (u : T ⟶ U.X) :
      (centralizerAdjointAction hZ hU).act z u ≫ unipotentInclusion.hom.hom =
        (z ≫ levi.hom.hom) * (u ≫ unipotentInclusion.hom.hom) * (z ≫ levi.hom.hom)⁻¹ := by
    have hLevi' : levi.hom.hom ≫ iP.hom.hom = iZ.hom.hom :=
      congrArg (fun f => f.hom.hom) hLevi
    have hUnipotent' : unipotentInclusion.hom.hom ≫ iP.hom.hom = iU.hom.hom :=
      congrArg (fun f => f.hom.hom) hUnipotent
    apply hP.1.right_cancellation
    simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hLevi', hUnipotent',
      centralizerAdjointAction_act_comp]
  have hMultiplication :=
    subgroupMultiplication_eq_multiplication hP hZ hU levi unipotentInclusion hLevi hUnipotent
  letI : IsIso (subgroupMultiplication unipotentInclusion levi) := by
    rw [hMultiplication]
    exact isIso_multiplication hP hZ hU
  refine ⟨AutomorphicAction.semidirectFactorIso (centralizerAdjointAction hZ hU)
    unipotentInclusion levi hAction, ?_⟩
  rw [AutomorphicAction.semidirectFactorIso_hom, AutomorphicAction.semidirectFactorHom_hom,
    hMultiplication]

/-- The represented dynamic parabolic is the semidirect product of the identity-limit
subgroup by the centralizer acting by conjugation. -/
def semidirectProductIso : (centralizerAdjointAction hZ hU).semidirectProduct ≅ P :=
  (semidirectProductIsoWithHom hP hZ hU).val

/-- The underlying map of the dynamic semidirect product isomorphism multiplies
the unipotent factor followed by the centralizer factor. -/
@[simp] theorem semidirectProductIso_hom :
    (semidirectProductIso hP hZ hU).hom.hom.hom = multiplication hP hZ hU :=
  (semidirectProductIsoWithHom hP hZ hU).property

end Langlands.GroupScheme.Dynamic
