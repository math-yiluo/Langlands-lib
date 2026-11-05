import Langlands.Global.AdelicSpreadExistenceStatement
import Langlands.Global.AdelicSIntegersColimitProof
import Langlands.AlgebraicGeometry.SchemeFilteredModelExistenceProof
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Existence of actual arithmetic spreads in both characteristics -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.SchemeLimitModel

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the initial algebra base preserves the filtered colimit.
The resulting model is compared with the actual pullback over its vertex. -/
private theorem finiteTypeScheme_model
    (R : Type u) [CommRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (A : J ⥤ CommAlgCat.{u} R) (c : Cocone A) (hc : IsColimit c)
    [IsNoetherianRing c.pt]
    (Y : Over (Spec (CommRingCat.of c.pt)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    ∃ (j : J) (M : Over (Spec (CommRingCat.of (A.obj j)))),
      LocallyOfFiniteType M.hom ∧ QuasiCompact M.hom ∧
        Nonempty ((Over.pullback
          (Spec.map (CommRingCat.ofHom (c.ι.app j).hom.toRingHom))).obj M ≅ Y) := by
  let Q : CommAlgCat.{u} R ⥤ CommRingCat.{u} :=
    (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙
      Under.forget (CommRingCat.of R)
  let c' : Cocone (A ⋙ Q) := Q.mapCocone c
  let hc' : IsColimit c' := isColimitOfPreserves Q hc
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let : LocallyOfFinitePresentation Y.hom := inferInstance
  let : QuasiSeparated Y.hom := inferInstance
  obtain ⟨j, Xj, gj, π, hfp, hqc, _, hpb⟩ :=
    @schemeFilteredModelExistence.{u} J _ _ (A ⋙ Q) c' hc' Y.left Y.hom
      ‹QuasiCompact Y.hom› ‹QuasiSeparated Y.hom› ‹LocallyOfFinitePresentation Y.hom›
  let : LocallyOfFinitePresentation gj := hfp
  exact ⟨j, Over.mk gj, inferInstanceAs (LocallyOfFiniteType gj), hqc,
    ⟨Over.isoMk hpb.isoPullback.symm hpb.isoPullback_inv_snd⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Descend along the literal integer subrings of the original function
field, retaining its specified field and constant-field structures. -/
theorem curvePlaceSpreadExistence : CurvePlaceSpreadExistenceStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S Y _ _
  let : IsNoetherianRing (curvePlaceSIntegersOverCocone k F S).pt :=
    inferInstanceAs (IsNoetherianRing F)
  exact finiteTypeScheme_model (curvePlaceSIntegers k F S)
    (curvePlaceSIntegersOverDiagram k F S) (curvePlaceSIntegersOverCocone k F S)
    (curvePlaceSIntegersOverIsColimit k F S) Y

set_option backward.isDefEq.respectTransparency false in
/-- Descend to an actual outside-set integer ring of the original number field. -/
theorem numberFieldSpreadExistence : NumberFieldSpreadExistenceStatement.{u} := by
  intro K _ _ S Y _ _
  let : IsNoetherianRing (numberFieldSIntegersOverCocone K S).pt :=
    inferInstanceAs (IsNoetherianRing K)
  exact finiteTypeScheme_model ((S : Set (FinitePlace K)).integer K)
    (numberFieldSIntegersOverDiagram K S) (numberFieldSIntegersOverCocone K S)
    (numberFieldSIntegersOverIsColimit K S) Y

/-- Actual finite-type arithmetic models exist in both arithmetic branches. -/
theorem adelicSpreadExistence : AdelicSpreadExistenceStatement.{u} :=
  ⟨curvePlaceSpreadExistence, numberFieldSpreadExistence⟩

end Langlands.Global
