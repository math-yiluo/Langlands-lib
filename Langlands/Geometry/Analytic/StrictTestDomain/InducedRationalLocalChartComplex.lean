import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalChartComplex
import Mathlib.Algebra.Category.ModuleCat.Ulift

/-! # Local-spectrum chart complexes and module homology retracts -/

noncomputable section

universe u v r w t

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type r} [CommRing R]
  {ι : Type t}

namespace OpenSubgroupTransport.CompactSections

variable (X : ρ.OpenSubgroupTransport)

/-- Actual locally constant coefficient modules on the local rational spectrum. -/
def localSpectrumCoefficientFunctor :
    SmoothRep.{r, v, w} R G ⥤ ModuleCat.{max u w} R where
  obj M := ModuleCat.of R (LocallyConstant X.LocalSpectrum M)
  map b := ModuleCat.ofHom (LocallyConstant.mapₗ R (SmoothRep.hom b).toLinearMap)
  map_id _ := by
    ext s z
    rfl
  map_comp _ _ := by
    ext s z
    rfl

instance localSpectrumCoefficientFunctor_additive :
    (localSpectrumCoefficientFunctor.{u, v, r, w} (R := R) X).Additive where
  map_add := by
    intro M N b d
    ext s
    rfl

/-- Lift only the carrier universe to compare with functions on induced charts. -/
def liftedLocalSpectrumCoefficientFunctor :
    SmoothRep.{r, v, w} R G ⥤ ModuleCat.{max u v w} R :=
  localSpectrumCoefficientFunctor X ⋙ ModuleCat.uliftFunctor.{v} R

instance liftedLocalSpectrumCoefficientFunctor_additive :
    (liftedLocalSpectrumCoefficientFunctor.{u, v, r, w} (R := R) X).Additive := by
  dsimp [liftedLocalSpectrumCoefficientFunctor]
  infer_instance

/-- The constructed chart homeomorphism identifies the actual coefficient modules. -/
def localChartCoefficientIso (a : G) :
    liftedLocalSpectrumCoefficientFunctor.{u, v, r, w} (R := R) X ≅
      chartCoefficientFunctor X a where
  hom :=
    { app M := ModuleCat.ofHom <|
        (LocallyConstant.comapₗ R
          ⟨(X.inducedChartHomeomorph a).symm,
            (X.inducedChartHomeomorph a).symm.continuous⟩).comp
              (ULift.moduleEquiv (R := R)
                (M := LocallyConstant X.LocalSpectrum M)).toLinearMap
      naturality M N b := by
        ext s
        rfl }
  inv :=
    { app M := ModuleCat.ofHom <|
        (ULift.moduleEquiv (R := R)
          (M := LocallyConstant X.LocalSpectrum M)).symm.toLinearMap.comp
          (LocallyConstant.comapₗ R
            ⟨X.inducedChartHomeomorph a, (X.inducedChartHomeomorph a).continuous⟩)
      naturality M N b := by
        ext s
        rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext M
    ext s
    apply ULift.ext
    apply LocallyConstant.ext
    intro z
    exact LocallyConstant.congr_arg s.down
      ((X.inducedChartHomeomorph a).symm_apply_apply z)
  inv_hom_id := by
    apply NatTrans.ext
    funext M
    ext s
    apply LocallyConstant.ext
    intro z
    exact LocallyConstant.congr_arg s ((X.inducedChartHomeomorph a).apply_symm_apply z)

@[simp]
theorem localChartCoefficientIso_hom_apply (a : G) (M : SmoothRep.{r, v, w} R G)
    (s : LocallyConstant X.LocalSpectrum M) (z : X.inducedChartDomain a) :
    LocallyConstant.toFun (((localChartCoefficientIso X a).hom.app M).hom (ULift.up s)) z =
      s ((X.inducedChartHomeomorph a).symm z) := rfl

@[simp]
theorem localChartCoefficientIso_inv_apply (a : G) (M : SmoothRep.{r, v, w} R G)
    (s : LocallyConstant (X.inducedChartDomain a) M) (z : X.LocalSpectrum) :
    LocallyConstant.toFun ((((localChartCoefficientIso X a).inv.app M).hom s).down) z =
      s (X.inducedChartHomeomorph a z) := rfl

/-- The actual local-spectrum coefficient complex, with its carrier universe lifted. -/
def localSpectrumComplexFunctor (c : ComplexShape ι) :
    HomologicalComplex (SmoothRep.{r, v, w} R G) c ⥤
      HomologicalComplex (ModuleCat.{max u v w} R) c :=
  (liftedLocalSpectrumCoefficientFunctor X).mapHomologicalComplex c

/-- Chart coordinates give a natural chain isomorphism for all supplied complexes. -/
def localChartComplexIso (a : G) (c : ComplexShape ι) :
    localSpectrumComplexFunctor.{u, v, r, w, t} (R := R) X c ≅
      chartComplexFunctor X a c :=
  NatIso.mapHomologicalComplex (localChartCoefficientIso X a) c

@[simp]
theorem localSpectrumComplex_d_apply (c : ComplexShape ι)
    (C : HomologicalComplex (SmoothRep.{r, v, w} R G) c) (i j : ι)
    (s : LocallyConstant X.LocalSpectrum (C.X i)) (z : X.LocalSpectrum) :
    LocallyConstant.toFun
      (((((localSpectrumComplexFunctor X c).obj C).d i j).hom (ULift.up s)).down) z =
      SmoothRep.hom (C.d i j) (s z) := rfl

/-- Extend actual local cochains through chart coordinates and then by zero. -/
def localChartComplexExtension (a : G) (c : ComplexShape ι) :
    localSpectrumComplexFunctor.{u, v, r, w, t} (R := R) X c ⟶
      supportedModuleComplexFunctor X c :=
  (localChartComplexIso X a c).hom ≫ chartComplexExtension X a c

/-- Restrict supported cochains and express them on the actual local spectrum. -/
def localChartComplexRestriction (a : G) (c : ComplexShape ι) :
    supportedModuleComplexFunctor.{u, v, r, w, t} (R := R) X c ⟶
      localSpectrumComplexFunctor X c :=
  chartComplexRestriction X a c ≫ (localChartComplexIso X a c).inv

@[simp]
theorem localChartComplexExtension_apply (a : G) (c : ComplexShape ι)
    (C : HomologicalComplex (SmoothRep.{r, v, w} R G) c) (i : ι)
    (s : LocallyConstant X.LocalSpectrum (C.X i)) :
    (((localChartComplexExtension X a c).app C).f i).hom (ULift.up s) =
      localChartExtension X a s := rfl

@[simp]
theorem localChartComplexRestriction_apply (a : G) (c : ComplexShape ι)
    (C : HomologicalComplex (SmoothRep.{r, v, w} R G) c) (i : ι)
    (s : Functions (R := R) (V := C.X i) X) (z : X.LocalSpectrum) :
    LocallyConstant.toFun
      (((((localChartComplexRestriction X a c).app C).f i).hom s).down) z =
      s.val (X.inducedChart a z) := rfl

@[simp]
theorem localChartComplexExtension_restriction (a : G) (c : ComplexShape ι) :
    localChartComplexExtension.{u, v, r, w, t} (R := R) X a c ≫
        localChartComplexRestriction X a c = 𝟙 (localSpectrumComplexFunctor X c) := by
  simp [localChartComplexExtension, localChartComplexRestriction, Category.assoc,
    ← Category.assoc (chartComplexExtension X a c) (chartComplexRestriction X a c)]

/-- Changing to local coordinates does not change the supported chart projection. -/
theorem localChartComplexRestriction_extension (a : G) (c : ComplexShape ι) :
    localChartComplexRestriction.{u, v, r, w, t} (R := R) X a c ≫
        localChartComplexExtension X a c = chartComplexProjection X a c := by
  simp [localChartComplexExtension, localChartComplexRestriction,
    chartComplexProjection, Category.assoc,
    ← Category.assoc (localChartComplexIso X a c).inv (localChartComplexIso X a c).hom]

/-- Homology of the actual supported complex after forgetting the group action. -/
def supportedModuleHomologyFunctor (c : ComplexShape ι) (i : ι) :
    HomologicalComplex (SmoothRep.{r, v, w} R G) c ⥤ ModuleCat.{max u v w} R :=
  supportedModuleComplexFunctor X c ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) c i

/-- Homology of the actual chart coefficient complex in the module category. -/
def chartHomologyFunctor (a : G) (c : ComplexShape ι) (i : ι) :
    HomologicalComplex (SmoothRep.{r, v, w} R G) c ⥤ ModuleCat.{max u v w} R :=
  chartComplexFunctor X a c ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) c i

/-- Homology of the lifted local-spectrum coefficient complex. -/
def localSpectrumHomologyFunctor (c : ComplexShape ι) (i : ι) :
    HomologicalComplex (SmoothRep.{r, v, w} R G) c ⥤ ModuleCat.{max u v w} R :=
  localSpectrumComplexFunctor X c ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) c i

/-- The local/chart chain isomorphism gives the genuine induced homology isomorphism. -/
def localChartHomologyIso (a : G) (c : ComplexShape ι) (i : ι) :
    localSpectrumHomologyFunctor.{u, v, r, w, t} (R := R) X c i ≅
      chartHomologyFunctor X a c i :=
  Functor.isoWhiskerRight (localChartComplexIso X a c)
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) c i)

/-- The actual map on module homology induced by local zero extension. -/
def localChartHomologyExtension (a : G) (c : ComplexShape ι) (i : ι) :
    localSpectrumHomologyFunctor.{u, v, r, w, t} (R := R) X c i ⟶
      supportedModuleHomologyFunctor X c i :=
  Functor.whiskerRight (localChartComplexExtension X a c)
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) c i)

/-- The actual map on module homology induced by local chart restriction. -/
def localChartHomologyRestriction (a : G) (c : ComplexShape ι) (i : ι) :
    supportedModuleHomologyFunctor.{u, v, r, w, t} (R := R) X c i ⟶
      localSpectrumHomologyFunctor X c i :=
  Functor.whiskerRight (localChartComplexRestriction X a c)
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) c i)

@[simp]
theorem localChartHomologyExtension_restriction (a : G) (c : ComplexShape ι) (i : ι) :
    localChartHomologyExtension.{u, v, r, w, t} (R := R) X a c i ≫
        localChartHomologyRestriction X a c i =
      𝟙 (localSpectrumHomologyFunctor X c i) := by
  change Functor.whiskerRight (localChartComplexExtension X a c) _ ≫
      Functor.whiskerRight (localChartComplexRestriction X a c) _ = _
  rw [← Functor.whiskerRight_comp, localChartComplexExtension_restriction]
  exact Functor.whiskerRight_id' _

/-- The supported chart projection induces an actual projection on module homology. -/
def chartHomologyProjection (a : G) (c : ComplexShape ι) (i : ι) :
    supportedModuleHomologyFunctor.{u, v, r, w, t} (R := R) X c i ⟶
      supportedModuleHomologyFunctor X c i :=
  Functor.whiskerRight (chartComplexProjection X a c)
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) c i)

theorem localChartHomologyRestriction_extension (a : G) (c : ComplexShape ι) (i : ι) :
    localChartHomologyRestriction.{u, v, r, w, t} (R := R) X a c i ≫
        localChartHomologyExtension X a c i = chartHomologyProjection X a c i := by
  change Functor.whiskerRight (localChartComplexRestriction X a c) _ ≫
      Functor.whiskerRight (localChartComplexExtension X a c) _ = _
  rw [← Functor.whiskerRight_comp, localChartComplexRestriction_extension]
  rfl

@[simp]
theorem chartHomologyProjection_idempotent (a : G) (c : ComplexShape ι) (i : ι) :
    chartHomologyProjection.{u, v, r, w, t} (R := R) X a c i ≫
        chartHomologyProjection X a c i = chartHomologyProjection X a c i := by
  change Functor.whiskerRight (chartComplexProjection X a c) _ ≫
      Functor.whiskerRight (chartComplexProjection X a c) _ = _
  rw [← Functor.whiskerRight_comp, chartComplexProjection_idempotent]
  rfl

theorem chartHomologyProjection_orthogonal
    (d e : G ⧸ X.subgroup.toSubgroup) (hde : d ≠ e) (c : ComplexShape ι) (i : ι) :
    chartHomologyProjection.{u, v, r, w, t} (R := R) X e.out c i ≫
        chartHomologyProjection X d.out c i = 0 := by
  apply NatTrans.ext
  funext C
  change (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R) c i).map _ ≫
      (HomologicalComplex.homologyFunctor _ c i).map _ = _
  rw [← Functor.map_comp]
  have h := congrArg (fun b => b.app C)
    (chartComplexProjection_orthogonal (R := R) X d e hde c)
  change ((chartComplexProjection X e.out c).app C ≫
    (chartComplexProjection X d.out c).app C) = 0 at h
  rw [h, Functor.map_zero]
  rfl

end OpenSubgroupTransport.CompactSections

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
