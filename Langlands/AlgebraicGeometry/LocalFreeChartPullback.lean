import Langlands.AlgebraicGeometry.ModuleLocalHomPullback
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.CategoryTheory.Sites.Spaces

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

namespace Langlands.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- Actual module pullback on the open chart, expressed on the over-sites. -/
def chartPullback :
    SheafOfModules (Y.ringCatSheaf.over U) ⥤
      SheafOfModules (X.ringCatSheaf.over (f ⁻¹ᵁ U)) :=
  (AlgebraicGeometry.Scheme.Modules.overEquiv U).functor ⋙
    AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U) ⋙
      (AlgebraicGeometry.Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).inverse

instance : PreservesColimitsOfSize.{u, u} (chartPullback f U) := by
  dsimp [chartPullback]
  infer_instance

/-- Identify chart pullback of a restricted module with restriction of its actual pullback. -/
def chartPullbackIso (M : Y.Modules) :
    (chartPullback f U).obj (M.over U) ≅
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U) :=
  (AlgebraicGeometry.Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).inverse.mapIso
    ((AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U)).mapIso
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app M) ≪≫
      ((restrictPullbackNatIso f U).app M).symm ≪≫
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).app
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)).symm) ≪≫
    ((AlgebraicGeometry.Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).unitIso.app
      (((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U))).symm

/-- The comparison identifies pullback of local morphisms with the published construction. -/
@[reassoc]
lemma chartPullbackIso_naturality {M N : Y.Modules} (h : LocalHom M N U) :
    (chartPullback f U).map h ≫ (chartPullbackIso f U N).hom =
      (chartPullbackIso f U M).hom ≫ localHomPullback f U h := by
  let E := AlgebraicGeometry.Scheme.Modules.overEquiv (f ⁻¹ᵁ U)
  have hh : (AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.map h =
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app M).hom ≫
        internalHomSectionsEquiv M N U h ≫
        ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app N).inv := by
    simp [internalHomSectionsEquiv, internalHomOverEquiv, Iso.homCongr]
    rfl
  have ht : E.functor.map (localHomPullback f U h) =
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).app
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)).hom ≫
        internalHomSectionsEquiv _ _ _ (localHomPullback f U h) ≫
        ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).app
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N)).inv := by
    simp [E, internalHomSectionsEquiv, internalHomOverEquiv, Iso.homCongr]
    rfl
  let P := AlgebraicGeometry.Scheme.Modules.pullback (f ∣_ U)
  let c (L : Y.Modules) := P.mapIso
    ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app L) ≪≫
      ((restrictPullbackNatIso f U).app L).symm ≪≫
      ((AlgebraicGeometry.Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).app
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L)).symm
  have hc : P.map ((AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.map h) ≫
      (c N).hom = (c M).hom ≫ E.functor.map (localHomPullback f U h) := by
    dsimp only [c, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [ht, hh, internalHomSectionsEquiv_localHomPullback]
    simp [P, Functor.map_comp, Category.assoc]
  have hn : E.inverse.map (E.functor.map (localHomPullback f U h)) ≫
      (E.unitIso.app (((AlgebraicGeometry.Scheme.Modules.pullback f).obj N).over
        (f ⁻¹ᵁ U))).inv =
      (E.unitIso.app (((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over
        (f ⁻¹ᵁ U))).inv ≫ localHomPullback f U h :=
    E.unitIso.inv.naturality (localHomPullback f U h)
  have hmap := congrArg (fun k => E.inverse.map k ≫
    (E.unitIso.app (((AlgebraicGeometry.Scheme.Modules.pullback f).obj N).over
      (f ⁻¹ᵁ U))).inv) hc
  simp only [Functor.map_comp, Category.assoc] at hmap
  rw [hn] at hmap
  simp only [chartPullback, chartPullbackIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.comp_map, Category.assoc]
  simpa only [E, P, c, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc] using hmap

/-- Choose the chart's unit comparison from the actual global pullback of the structure module. -/
def chartPullbackUnitIso :
    SheafOfModules.unit (X.ringCatSheaf.over (f ⁻¹ᵁ U)) ≅
      (chartPullback f U).obj (SheafOfModules.unit (Y.ringCatSheaf.over U)) :=
  ((SheafOfModules.overFunctor X.ringCatSheaf (f ⁻¹ᵁ U)).mapIso
    (pullbackUnitIso f).symm) ≪≫
      (chartPullbackIso f U (SheafOfModules.unit Y.ringCatSheaf)).symm

variable {I : Type u} [Fintype I] {M : Y.Modules}

/-- A finite free chart on the actual pulled-back module, constructed from the source chart. -/
def chartFreePullbackIso
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U) :
    SheafOfModules.free (R := X.ringCatSheaf.over (f ⁻¹ᵁ U)) I ≅
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).over (f ⁻¹ᵁ U) :=
  SheafOfModules.mapFreeIso (chartPullback f U) I (chartPullbackUnitIso f U) ≪≫
    (chartPullback f U).mapIso e ≪≫ chartPullbackIso f U M

/-- The new chart's generators are actual local pullbacks of the source generators. -/
@[reassoc]
lemma chartFreePullbackIso_generator
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U) (i : I) :
    SheafOfModules.ιFree i ≫ (chartFreePullbackIso f U e).hom =
      (pullbackUnitIso f).inv.over (f ⁻¹ᵁ U) ≫
        localHomPullback f U (SheafOfModules.ιFree i ≫ e.hom) := by
  have hn := chartPullbackIso_naturality f U
    (M := SheafOfModules.unit Y.ringCatSheaf) (N := M)
    (SheafOfModules.ιFree i ≫ e.hom)
  simp only [chartFreePullbackIso, Iso.trans_hom, Functor.mapIso_hom,
    SheafOfModules.ιFree_mapFreeIso_hom_assoc, ← Functor.map_comp_assoc,
    chartPullbackUnitIso, Iso.symm_hom, Category.assoc]
  erw [hn, Iso.inv_hom_id_assoc]

end Langlands.Scheme.Modules
