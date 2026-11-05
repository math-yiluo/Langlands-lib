import Langlands.Global.AdelicSpreadProperMapStatement
import Langlands.Global.AdelicSpreadProperExistenceProof
import Langlands.Global.AdelicFixedModelProperMapProof
import Langlands.Global.AdelicSpreadTopologyIndependenceProof

/-! # Proper maps on actual adelic generic-fibre points -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F] [Finite k]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (S : Finset (AlgebraicCurve.Place k F))
  (X Z : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

private lemma curve_spread_proper_of_model
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (Y W : Over (Spec (CommRingCat.of F)))
    (e : curvePlaceModelGenericFiber k F S X ≅ Y)
    (f : curvePlaceModelGenericFiber k F S Z ≅ W)
    (g : Y ⟶ W) (fi : X ⟶ Z) [IsProper fi.left]
    (h : (Over.pullback
        (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))).map fi ≫
        f.hom = e.hom ≫ g) :
    @IsProperMap (CurvePlaceAdelePoints k F Y) (CurvePlaceAdelePoints k F W)
      (curvePlaceSpreadAdelePointTopology k F S X Y e)
      (curvePlaceSpreadAdelePointTopology k F S Z W f)
      (fun p => p ≫ g) := by
  let := curvePlaceFixedModelAdelePointTopology k F S X
  let := curvePlaceFixedModelAdelePointTopology k F S Z
  let := curvePlaceSpreadAdelePointTopology k F S X Y e
  let := curvePlaceSpreadAdelePointTopology k F S Z W f
  let eX := curvePlaceSpreadAdelePointHomeomorph k F S X Y e
  let eZ := curvePlaceSpreadAdelePointHomeomorph k F S Z W f
  have hn (p : CurvePlaceFixedModelAdelePoints k F S X) :
      eZ (p ≫ fi) = eX p ≫ g := by
    change curvePlaceGenericFiberAdelePointEquiv k F S Z (p ≫ fi) ≫ f.hom =
      (curvePlaceGenericFiberAdelePointEquiv k F S X p ≫ e.hom) ≫ g
    rw [curvePlaceGenericFiberAdelePointEquiv_natural]
    simpa only [Category.assoc] using congrArg
      (fun q => curvePlaceGenericFiberAdelePointEquiv k F S X p ≫ q) h
  have hc := eZ.isProperMap.comp
    ((curvePlaceFixedModel_proper k F S X Z fi).comp
      eX.symm.isProperMap)
  have heq : (fun p => p ≫ g) = (eZ ∘ (fun p => p ≫ fi) ∘ eX.symm) := by
    funext p
    change p ≫ g = eZ (eX.symm p ≫ fi)
    rw [hn, eX.apply_symm_apply]
  exact heq.symm ▸ hc

end Curve

/-- Proper field maps induce proper maps for any independently supplied spreads. -/
theorem curvePlaceSpreadProperMap : CurvePlaceSpreadProperMapStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S U X Z _ _ _ _ Y W e f _ g _
  let : LocallyOfFiniteType (curvePlaceModelGenericFiber k F U Z).hom := by
    dsimp [curvePlaceModelGenericFiber]
    infer_instance
  let : QuasiCompact (curvePlaceModelGenericFiber k F U Z).hom := by
    dsimp [curvePlaceModelGenericFiber]
    infer_instance
  let : LocallyOfFiniteType W.hom := by
    rw [← Over.w f.inv]
    infer_instance
  let : QuasiCompact W.hom := by
    rw [← Over.w f.inv]
    infer_instance
  obtain ⟨T, M, N, hMft, hMqc, hMsep, hNft, hNqc, hNsep, eT, fT, gm, hgm, hm⟩ :=
    curvePlaceSpreadProperExistence k F S Y W g
  let : LocallyOfFiniteType M.hom := hMft
  let : QuasiCompact M.hom := hMqc
  let : IsSeparated M.hom := hMsep
  let : LocallyOfFiniteType N.hom := hNft
  let : QuasiCompact N.hom := hNqc
  let : IsSeparated N.hom := hNsep
  let : IsProper gm.left := hgm
  have hX := curvePlaceSpreadTopologyIndependence k F S T.val X M Y e eT
  have hZ := curvePlaceSpreadTopologyIndependence k F U T.val Z N W f fT
  rw [hX, hZ]
  exact curve_spread_proper_of_model k F T.val M N Y W eT fT g gm hm

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
  (X Z : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

private lemma number_spread_proper_of_model
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (Y W : Over (Spec (CommRingCat.of K)))
    (e : numberFieldModelGenericFiber K S X ≅ Y)
    (f : numberFieldModelGenericFiber K S Z ≅ W)
    (g : Y ⟶ W) (fi : X ⟶ Z) [IsProper fi.left]
    (h : (Over.pullback
        (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))).map fi ≫
        f.hom = e.hom ≫ g) :
    @IsProperMap (NumberFieldAdelePoints K Y) (NumberFieldAdelePoints K W)
      (numberFieldSpreadAdelePointTopology K S X Y e)
      (numberFieldSpreadAdelePointTopology K S Z W f)
      (fun p => p ≫ g) := by
  let := numberFieldFixedModelAdelePointTopology K S X
  let := numberFieldFixedModelAdelePointTopology K S Z
  let := numberFieldSpreadAdelePointTopology K S X Y e
  let := numberFieldSpreadAdelePointTopology K S Z W f
  let eX := numberFieldSpreadAdelePointHomeomorph K S X Y e
  let eZ := numberFieldSpreadAdelePointHomeomorph K S Z W f
  have hn (p : NumberFieldFixedModelAdelePoints K S X) :
      eZ (p ≫ fi) = eX p ≫ g := by
    change numberFieldGenericFiberAdelePointEquiv K S Z (p ≫ fi) ≫ f.hom =
      (numberFieldGenericFiberAdelePointEquiv K S X p ≫ e.hom) ≫ g
    rw [numberFieldGenericFiberAdelePointEquiv_natural]
    simpa only [Category.assoc] using congrArg
      (fun q => numberFieldGenericFiberAdelePointEquiv K S X p ≫ q) h
  have hc := eZ.isProperMap.comp
    ((numberFieldFixedModel_proper K S X Z fi).comp
      eX.symm.isProperMap)
  have heq : (fun p => p ≫ g) = (eZ ∘ (fun p => p ≫ fi) ∘ eX.symm) := by
    funext p
    change p ≫ g = eZ (eX.symm p ≫ fi)
    rw [hn, eX.apply_symm_apply]
  exact heq.symm ▸ hc

end NumberField

/-- The analogous properness for the full number-field adele ring. -/
theorem numberFieldSpreadProperMap : NumberFieldSpreadProperMapStatement.{u} := by
  intro K _ _ S U X Z _ _ _ _ Y W e f _ g _
  let : LocallyOfFiniteType (numberFieldModelGenericFiber K U Z).hom := by
    dsimp [numberFieldModelGenericFiber]
    infer_instance
  let : QuasiCompact (numberFieldModelGenericFiber K U Z).hom := by
    dsimp [numberFieldModelGenericFiber]
    infer_instance
  let : LocallyOfFiniteType W.hom := by
    rw [← Over.w f.inv]
    infer_instance
  let : QuasiCompact W.hom := by
    rw [← Over.w f.inv]
    infer_instance
  obtain ⟨T, M, N, hMft, hMqc, hMsep, hNft, hNqc, hNsep, eT, fT, gm, hgm, hm⟩ :=
    numberFieldSpreadProperExistence K S Y W g
  let : LocallyOfFiniteType M.hom := hMft
  let : QuasiCompact M.hom := hMqc
  let : IsSeparated M.hom := hMsep
  let : LocallyOfFiniteType N.hom := hNft
  let : QuasiCompact N.hom := hNqc
  let : IsSeparated N.hom := hNsep
  let : IsProper gm.left := hgm
  have hX := numberFieldSpreadTopologyIndependence K S T.val X M Y e eT
  have hZ := numberFieldSpreadTopologyIndependence K U T.val Z N W f fT
  rw [hX, hZ]
  exact number_spread_proper_of_model K T.val M N Y W eT fT g gm hm

/-- The exact two-arithmetic-case proper-map target. -/
theorem adelicSpreadProperMap : AdelicSpreadProperMapStatement.{u} :=
  ⟨curvePlaceSpreadProperMap, numberFieldSpreadProperMap⟩

end Langlands.Global
