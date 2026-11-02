import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCompactComplex

/-! # Actual rational-chart maps of supported coefficient complexes -/

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

/-- The existing smooth supported coefficient functor with its action forgotten. -/
def supportedModuleFunctor :
    SmoothRep.{r, v, w} R G ⥤ ModuleCat.{max u v w} R :=
  coefficientFunctor X ⋙ SmoothRep.toRep ⋙ forget₂ (Rep R G) (ModuleCat R)

instance supportedModuleFunctor_additive :
    (supportedModuleFunctor.{u, v, r, w} (R := R) X).Additive := by
  dsimp [supportedModuleFunctor]
  infer_instance

/-- Locally constant module coefficients on one actual compact clopen chart. -/
def chartCoefficientFunctor (a : G) :
    SmoothRep.{r, v, w} R G ⥤ ModuleCat.{max u v w} R where
  obj M := ModuleCat.of R (LocallyConstant (X.inducedChartDomain a) M)
  map b := ModuleCat.ofHom (LocallyConstant.mapₗ R (SmoothRep.hom b).toLinearMap)
  map_id _ := by
    ext s z
    rfl
  map_comp _ _ := by
    ext s z
    rfl

instance chartCoefficientFunctor_additive (a : G) :
    (chartCoefficientFunctor.{u, v, r, w} (R := R) X a).Additive where
  map_add := by
    intro M N b d
    ext s
    rfl

/-- Extension by zero is natural in smooth coefficients, as a module map. -/
def chartExtensionNatTrans (a : G) :
    chartCoefficientFunctor.{u, v, r, w} (R := R) X a ⟶ supportedModuleFunctor X where
  app M := ModuleCat.ofHom (chartExtensionLinear (R := R) (V := M) X a)
  naturality M N b := by
    ext s
    exact (coefficientMap_chartExtension X b a s).symm

/-- Actual chart restriction is natural in smooth coefficients. -/
def chartRestrictionNatTrans (a : G) :
    supportedModuleFunctor.{u, v, r, w} (R := R) X ⟶ chartCoefficientFunctor X a where
  app M := ModuleCat.ofHom (chartRestrictionLinear (R := R) (V := M) X a)
  naturality M N b := by
    ext s
    rfl

@[simp]
theorem chartExtension_restriction (a : G) :
    chartExtensionNatTrans.{u, v, r, w} (R := R) X a ≫ chartRestrictionNatTrans X a =
      𝟙 (chartCoefficientFunctor X a) := by
  apply NatTrans.ext
  funext M
  ext s
  exact chartRestriction_extension X a s

/-- The supported module complex obtained from the same coefficient complex. -/
def supportedModuleComplexFunctor (c : ComplexShape ι) :
    HomologicalComplex (SmoothRep.{r, v, w} R G) c ⥤
      HomologicalComplex (ModuleCat.{max u v w} R) c :=
  (supportedModuleFunctor X).mapHomologicalComplex c

/-- The actual supported smooth complex has this underlying module complex. -/
theorem supportedModuleComplexFunctor_eq (c : ComplexShape ι) :
    supportedModuleComplexFunctor.{u, v, r, w, t} (R := R) X c =
      supportedComplexFunctor X c ⋙
        (SmoothRep.toRep ⋙ forget₂ (Rep R G) (ModuleCat R)).mapHomologicalComplex c := rfl

/-- Pointwise coefficient complexes on an actual compact clopen chart. -/
def chartComplexFunctor (a : G) (c : ComplexShape ι) :
    HomologicalComplex (SmoothRep.{r, v, w} R G) c ⥤
      HomologicalComplex (ModuleCat.{max u v w} R) c :=
  (chartCoefficientFunctor X a).mapHomologicalComplex c

/-- The chain map which extends each chart cochain by zero. -/
def chartComplexExtension (a : G) (c : ComplexShape ι) :
    chartComplexFunctor.{u, v, r, w, t} (R := R) X a c ⟶
      supportedModuleComplexFunctor X c :=
  (chartExtensionNatTrans X a).mapHomologicalComplex c

/-- The chain map which restricts each supported cochain to the actual chart. -/
def chartComplexRestriction (a : G) (c : ComplexShape ι) :
    supportedModuleComplexFunctor.{u, v, r, w, t} (R := R) X c ⟶
      chartComplexFunctor X a c :=
  (chartRestrictionNatTrans X a).mapHomologicalComplex c

@[simp]
theorem chartComplexExtension_restriction (a : G) (c : ComplexShape ι) :
    chartComplexExtension.{u, v, r, w, t} (R := R) X a c ≫
        chartComplexRestriction X a c = 𝟙 (chartComplexFunctor X a c) := by
  change NatTrans.mapHomologicalComplex (chartExtensionNatTrans X a) c ≫
      NatTrans.mapHomologicalComplex (chartRestrictionNatTrans X a) c = _
  rw [← NatTrans.mapHomologicalComplex_comp, chartExtension_restriction]
  exact NatTrans.mapHomologicalComplex_id c _

/-- The chain projection to the part supported on one actual chart. -/
def chartComplexProjection (a : G) (c : ComplexShape ι) :
    supportedModuleComplexFunctor.{u, v, r, w, t} (R := R) X c ⟶
      supportedModuleComplexFunctor X c :=
  chartComplexRestriction X a c ≫ chartComplexExtension X a c

@[simp]
theorem chartComplexProjection_apply (a : G) (c : ComplexShape ι)
    (C : HomologicalComplex (SmoothRep.{r, v, w} R G) c) (i : ι)
    (s : Functions (R := R) (V := C.X i) X) :
    (((chartComplexProjection X a c).app C).f i).hom s = chartPart X a s := rfl

@[simp]
theorem chartComplexProjection_idempotent (a : G) (c : ComplexShape ι) :
    chartComplexProjection.{u, v, r, w, t} (R := R) X a c ≫
        chartComplexProjection X a c = chartComplexProjection X a c := by
  apply NatTrans.ext
  funext C
  ext i s
  exact chartPart_idempotent X a s

theorem chartComplexProjection_orthogonal
    (d e : G ⧸ X.subgroup.toSubgroup) (hde : d ≠ e) (c : ComplexShape ι) :
    chartComplexProjection.{u, v, r, w, t} (R := R) X e.out c ≫
        chartComplexProjection X d.out c = 0 := by
  apply NatTrans.ext
  funext C
  ext i s
  exact chartPart_out_orthogonal X d e hde s

/-- Any finite set containing the actual support reconstructs that degree vector. -/
theorem sum_chartComplexProjection_eq (c : ComplexShape ι)
    (C : HomologicalComplex (SmoothRep.{r, v, w} R G) c) (i : ι)
    (s : Functions (R := R) (V := C.X i) X)
    (S : Finset (G ⧸ X.subgroup.toSubgroup))
    (hS : componentSupport X s.val ⊆ (S : Set (G ⧸ X.subgroup.toSubgroup))) :
    (∑ d ∈ S, (((chartComplexProjection X d.out c).app C).f i).hom s) = s :=
  sum_chartPart_eq X s S hS

/-- Every degree vector has its own finite actual chart reconstruction. -/
theorem exists_sum_chartComplexProjection (c : ComplexShape ι)
    (C : HomologicalComplex (SmoothRep.{r, v, w} R G) c) (i : ι)
    (s : Functions (R := R) (V := C.X i) X) :
    ∃ S : Finset (G ⧸ X.subgroup.toSubgroup),
      (∑ d ∈ S, (((chartComplexProjection X d.out c).app C).f i).hom s) = s :=
  exists_sum_chartPart X s

end OpenSubgroupTransport.CompactSections

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
