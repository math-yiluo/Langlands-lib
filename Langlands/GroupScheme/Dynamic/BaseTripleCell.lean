import Langlands.GroupScheme.Dynamic.BaseOppositeCellProof
import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Absolute.TripleCell

/-! # The dynamic triple cell over an arbitrary base -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

set_option maxHeartbeats 800000 in
/-- The dynamic triple cell is an open immersion over any base scheme. -/
theorem isOpenImmersion_tripleCellMultiplication_overBase
    {S : Scheme.{u}} {G : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) {M Z U : GroupScheme S}
    {iM : M ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
    (hM : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom S (-1)) ≫ χ)).IsRepresentedBy iM)
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU) :
    IsOpenImmersion (tripleCellMultiplication iM iZ iU).left := by
  obtain ⟨P, iP, -, -, hP⟩ := (dynamicBaseRepresentability S G χ).1
  let e := parabolicProductIso χ hZ hU hP
  have : IsIso (M.X ◁ e.hom).left :=
    (inferInstance : IsIso ((Over.forget _).mapIso (whiskerLeftIso M.X e)).hom)
  have : IsOpenImmersion (SubgroupFunctor.cellMultiplication iM iP).left :=
    dynamicBaseOppositeCell S G χ M P iM iP hM hP
  have h : IsOpenImmersion
      ((M.X ◁ e.hom) ≫ SubgroupFunctor.cellMultiplication iM iP).left := by
    change IsOpenImmersion
      ((M.X ◁ e.hom).left ≫ (SubgroupFunctor.cellMultiplication iM iP).left)
    infer_instance
  rw [whiskerLeft_parabolicProductIso_comp_cellMultiplication χ iM hZ hU hP] at h
  exact h


end Langlands.GroupScheme.Dynamic
