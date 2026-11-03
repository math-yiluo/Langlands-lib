import Langlands.GroupScheme.Dynamic.AdjointDeterminantExistenceStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates

/-! # Existence of the actual adjoint determinant on P and M -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {R : CommRingCat.{u}} {H K U : GroupScheme (Spec R)}
  [IsAffineHom U.X.hom] (a : AutomorphicAction H U) {d : ℕ}
  (c : Lie.FiniteCoordinates U d) [IsAffine H.X.left] [IsAffine K.X.left]

/-- Restricting the determinant character along a homomorphism `j : K ⟶ H` gives the
determinant character of the restricted action, in the same coordinates. -/
theorem characterRestrict_determinantCharacter (j : K ⟶ H) :
    characterRestrict j (a.determinantCharacter c) =
      (a.restrict j).determinantCharacter c := by
  apply rationalCharacters.ext_characterEval
  intro T x
  obtain ⟨⟨B⟩, ⟨e⟩⟩ := (essImage_algSpec (G := K.X)).mpr inferInstance
  have hx : x = (x ≫ e.inv) ≫ e.hom := by simp
  rw [hx, characterEval_naturality, characterEval_naturality,
    characterEval_characterRestrict, determinantCharacter_eval_affine,
    determinantCharacter_eval_affine, differential_restrict]

end AutomorphicAction

/-- Existence of coordinates, the actual differential representation of `P` on `Lie(U)` and
its determinant characters on `P` and `M`. -/
theorem dynamicAdjointDeterminantExistence : DynamicAdjointDeterminantExistenceStatement.{u} := by
  intro k _ G hG χ P M U iP iM iU hP hM hU
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hPc : IsClosedSubgroup iP := by
    rw [← SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hP
      (Dynamic.Affine.isRepresentedBy_parabolicHom χ)]
    exact IsClosedSubgroup.iso_comp _ (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)
  have hMc : IsClosedSubgroup iM := by
    rw [← SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hM
      (Dynamic.Affine.isRepresentedBy_centralizerHom χ)]
    exact IsClosedSubgroup.iso_comp _ (Dynamic.Affine.isClosedSubgroup_centralizerHom χ)
  have hUc : IsClosedSubgroup iU := by
    rw [← SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp hU
      (Dynamic.Affine.isRepresentedBy_unipotentHom χ)]
    exact IsClosedSubgroup.iso_comp _ (Dynamic.Affine.isClosedSubgroup_unipotentHom χ)
  have hPa : IsAffineHom P.X.hom := hPc.isAffineHom
  have hMa : IsAffineHom M.X.hom := hMc.isAffineHom
  have hUa : IsAffineHom U.X.hom := hUc.isAffineHom
  refine ⟨hPa, hMa, hUa, ?_⟩
  have : IsAffine P.X.left := isAffine_of_isAffineHom P.X.hom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : LocallyOfFiniteType U.X.hom := by
    have : IsClosedImmersion iU.hom.hom.left := hUc
    rw [← Over.w iU.hom.hom]
    infer_instance
  have hres : (Dynamic.parabolicAdjointAction hP hU).restrict
      (Dynamic.centralizerToParabolic hP hM) = Dynamic.centralizerAdjointAction hM hU := by
    apply Dynamic.eq_centralizerAdjointAction
    intro T m u
    rw [AutomorphicAction.restrict_act, Dynamic.parabolicAdjointAction_act_comp,
      Category.assoc, ← Grp.comp_hom_hom, Dynamic.centralizerToParabolic_comp]
  let c := Lie.finiteCoordinates U
  refine ⟨_, c, (Dynamic.parabolicAdjointAction hP hU).finiteRepresentation c,
    Dynamic.adjointDeterminantCharacter hP hU c,
    (Dynamic.centralizerAdjointAction hM hU).determinantCharacter c,
    rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · rw [Dynamic.adjointDeterminantCharacter,
      AutomorphicAction.characterRestrict_determinantCharacter, hres]
  · exact fun A p x =>
      AutomorphicAction.finiteRepresentation_affineAction _ c A p x
  · exact fun A p => Dynamic.adjointDeterminantCharacter_affinePoints hP hU c A p
  · exact fun A m => AutomorphicAction.determinantCharacter_affinePoints _ c A m

end Langlands.GroupScheme
