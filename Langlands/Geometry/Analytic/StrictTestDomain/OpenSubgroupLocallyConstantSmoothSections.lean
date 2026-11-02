import Langlands.Geometry.Analytic.StrictTestDomain.OpenSubgroupLocallyConstantSheaf
import Langlands.Geometry.Analytic.StrictTestDomain.OpenSubgroupTransportSections
import Langlands.Geometry.Analytic.StrictTestDomain.SpectralGlobalAction
import Langlands.Representation.LocallyConstant.CompactAction
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Cohomology.HyperextScalarExtension
import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits

/-! # Full smooth local sections on the finite rational transport site -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r w

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory CategoryTheory.Limits Opposite Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type r} [CommRing R]

namespace OpenSubgroupTransport

local instance subgroupIsTopologicalGroup (X : ρ.OpenSubgroupTransport) :
    IsTopologicalGroup X.subgroup :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype X.subgroup)

/-- The original ambient point operators restricted to the invariant locus. -/
@[instance_reducible]
def locusMulAction (X : ρ.OpenSubgroupTransport) :
    MulAction X.subgroup X.domain.obj.locus where
  smul k x := ⟨ρ.toMonoidHom (k : G) • x.val, by
    have hk := X.domain.property k.property
    rw [mem_locusOpenSubgroup] at hk
    exact hk.le (Set.mem_image_of_mem _ x.property)⟩
  one_smul x := by
    apply Subtype.ext
    change ρ.toMonoidHom (1 : G) • x.val = x.val
    simp only [map_one, one_smul]
  mul_smul k l x := by
    apply Subtype.ext
    change ρ.toMonoidHom ((k : G) * (l : G)) • x.val =
      ρ.toMonoidHom (k : G) • (ρ.toMonoidHom (l : G) • x.val)
    simp only [map_mul, mul_smul]

attribute [local instance] locusMulAction locusCompactSpace

@[simp]
theorem locus_smul_val (X : ρ.OpenSubgroupTransport) (k : X.subgroup)
    (x : X.domain.obj.locus) :
    (k • x).val = ρ.toMonoidHom (k : G) • x.val := rfl

/-- Joint continuity is inherited from the actual global spectrum action. -/
instance locusContinuousSMul (X : ρ.OpenSubgroupTransport) :
    ContinuousSMul X.subgroup X.domain.obj.locus where
  continuous_smul := by
    apply Continuous.subtype_mk
    exact ρ.continuous_globalSpectrumAction.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))

/-- The action obtained by evaluating the actual sheaf has the original
diagonal coefficient and inverse-point formula. -/
@[simp]
theorem locallyConstantSectionRepresentation_apply (M : Rep.{w} R G)
    (X : ρ.OpenSubgroupTransport) (k : X.subgroup)
    (s : LocallyConstant X.domain.obj.locus M) (x : X.domain.obj.locus) :
    LocallyConstant.toFun
        (((sectionRepresentation R X).obj (locallyConstantSheaf M)).ρ k s) x =
      M.ρ (k : G) (s (k⁻¹ • x)) := by
  change M.ρ ((k : G)⁻¹)⁻¹ (s ((X.operator k).locusMap x)) = _
  rw [inv_inv]
  rfl

/-- Equality of the actual evaluated representation and the compact diagonal
representation, on the entire locally constant module. -/
theorem locallyConstantSectionRepresentation_eq_diagonal (M : Rep.{w} R G)
    (X : ρ.OpenSubgroupTransport) :
    ((sectionRepresentation R X).obj (locallyConstantSheaf M)).ρ =
      CompactAction.LocallyConstantModule.diagonalRepresentation
        (X := X.domain.obj.locus) (M.ρ.comp (SubgroupClass.subtype X.subgroup)) := by
  apply MonoidHom.ext
  intro k
  apply LinearMap.ext
  intro s
  apply LocallyConstant.ext
  intro x
  exact locallyConstantSectionRepresentation_apply M X k s x

/-- Smooth ambient coefficients and compactness prove smoothness of every
section of the original module sheaf, without shrinking its carrier. -/
theorem locallyConstantSectionRepresentation_isSmooth
    (M : SmoothRep.{r, v, w} R G) (X : ρ.OpenSubgroupTransport) :
    IsSmooth ((sectionRepresentation R X).obj (locallyConstantSheaf M.obj)).ρ := by
  rw [locallyConstantSectionRepresentation_eq_diagonal]
  exact CompactAction.LocallyConstantModule.diagonalRepresentation_isSmooth _
    (isSmooth_comp (SubgroupClass.subtype X.subgroup) continuous_subtype_val M.isSmooth)

/-- Smoothness of all original full section representations at their own
actual open subgroups. -/
def locallySmoothProperty :
    ObjectProperty (ModuleSheaf.{u, v, r, w} (ρ := ρ) R) :=
  fun F => ∀ X : ρ.OpenSubgroupTransport, IsSmooth ((sectionRepresentation R X).obj F).ρ

/-- Actual module sheaves with smooth full sections at every rational test. -/
abbrev LocallySmoothModuleSheaf :=
  (locallySmoothProperty (ρ := ρ) (R := R)).FullSubcategory

/-- Retain the actual module sheaf and every original sheaf morphism. -/
abbrev locallySmoothInclusion :
    LocallySmoothModuleSheaf.{u, v, r, w} (ρ := ρ) (R := R) ⥤
      ModuleSheaf.{u, v, r, w} (ρ := ρ) R :=
  (locallySmoothProperty (ρ := ρ) (R := R)).ι

/-- Subobjects retain smoothness on every original rational test. -/
instance locallySmoothProperty_isClosedUnderSubobjects :
    (locallySmoothProperty.{u, v, r, w} (ρ := ρ) (R := R)).IsClosedUnderSubobjects where
  prop_of_mono f _ hF X := by
    have : Mono ((sectionRepresentation R X).map f) := inferInstance
    exact isSmooth_of_injective ((sectionRepresentation R X).map f).hom
      ((Rep.mono_iff_injective _).mp inferInstance) (hF X)

/-- The local smoothness condition is invariant under actual sheaf isomorphisms. -/
theorem locallySmoothProperty_iff_of_iso
    {F E : ModuleSheaf.{u, v, r, w} (ρ := ρ) R} (e : F ≅ E) :
    locallySmoothProperty F ↔ locallySmoothProperty E :=
  (locallySmoothProperty (ρ := ρ) (R := R)).prop_iff_of_iso e

/-- Finite limits remain smooth on every test, using actual section evaluation
and finite-limit preservation of the inclusion of smooth representations. -/
instance locallySmoothProperty_isClosedUnderFiniteLimits :
    (locallySmoothProperty.{u, v, r, w} (ρ := ρ) (R := R)).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape J _ _ :=
    ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
      rintro _ ⟨F, hF⟩ X
      let E := (sectionRepresentation R X :
        ModuleSheaf.{u, v, r, w} (ρ := ρ) R ⥤ Rep.{w} R X.subgroup)
      let D := (smoothRepProperty R X.subgroup).lift (F ⋙ E) (fun j => hF j X)
      let : PreservesFiniteLimits
          (SmoothRep.toRep : SmoothRep.{r, v, w} R X.subgroup ⥤ Rep.{w} R X.subgroup) :=
        Functor.preservesFiniteLimits_of_preservesHomology _
      exact (smoothRepProperty R X.subgroup).prop_of_iso
        ((isLimitOfPreserves SmoothRep.toRep (limit.isLimit D)).conePointUniqueUpToIso
          (isLimitOfPreserves E (limit.isLimit F))) (limit D).property)

instance locallySmoothModuleSheaf_hasFiniteLimits :
    HasFiniteLimits (LocallySmoothModuleSheaf.{u, v, r, w} (ρ := ρ) (R := R)) :=
  inferInstance

instance locallySmoothInclusion_preservesFiniteLimits :
    PreservesFiniteLimits
      (locallySmoothInclusion.{u, v, r, w} (ρ := ρ) (R := R)) :=
  inferInstance

/-- Evaluation keeps all sections and bundles the proved smooth local action. -/
def smoothSectionRepresentation (X : ρ.OpenSubgroupTransport) :
    LocallySmoothModuleSheaf.{u, v, r, w} (ρ := ρ) (R := R) ⥤
      SmoothRep.{r, v, w} R X.subgroup :=
  (smoothRepProperty R X.subgroup).lift
    (locallySmoothInclusion ⋙ sectionRepresentation R X) (fun F => F.property X)

/-- Forgetting the smoothness proof recovers the original full representation. -/
def smoothSectionRepresentationForgetIso (X : ρ.OpenSubgroupTransport) :
    smoothSectionRepresentation (R := R) X ⋙ SmoothRep.toRep ≅
      locallySmoothInclusion ⋙ sectionRepresentation R X :=
  Iso.refl _

instance smoothSectionRepresentation_additive (X : ρ.OpenSubgroupTransport) :
    (smoothSectionRepresentation (R := R) X :
      LocallySmoothModuleSheaf.{u, v, r, w} (ρ := ρ) (R := R) ⥤ _).Additive where
  map_add {F E} f g := by
    apply ObjectProperty.hom_ext
    exact (sectionRepresentation R X).map_add (f := f.hom) (g := g.hom)

instance smoothSectionRepresentation_preservesFiniteLimits
    (X : ρ.OpenSubgroupTransport) :
    PreservesFiniteLimits (smoothSectionRepresentation (R := R) X :
      LocallySmoothModuleSheaf.{u, v, r, w} (ρ := ρ) (R := R) ⥤ _) := by
  have : PreservesFiniteLimits
      ((smoothSectionRepresentation (R := R) X :
        LocallySmoothModuleSheaf.{u, v, r, w} (ρ := ρ) (R := R) ⥤ _) ⋙
          SmoothRep.toRep) :=
    preservesFiniteLimits_of_natIso (smoothSectionRepresentationForgetIso X).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ SmoothRep.toRep

/-- Restriction of smooth representations along an original arrow's continuous
conjugation homomorphism, retaining carriers and linear maps. -/
def smoothConjugationRestriction {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y) :
    SmoothRep.{r, v, w} R Y.subgroup ⥤ SmoothRep.{r, v, w} R X.subgroup :=
  (smoothRepProperty R X.subgroup).lift
    (SmoothRep.toRep ⋙ Rep.resFunctor f.groupHom.toMonoidHom)
    (fun M => isSmooth_comp f.groupHom.toMonoidHom f.groupHom.continuous M.isSmooth)

/-- Every original labelled restriction remains the actual smooth intertwiner
after the required conjugation of subgroups. -/
def smoothRepresentationRestriction {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y) :
    smoothSectionRepresentation (R := R) Y ⋙ smoothConjugationRestriction f ⟶
      (smoothSectionRepresentation X :
        LocallySmoothModuleSheaf.{u, v, r, w} (ρ := ρ) (R := R) ⥤ _) where
  app F := ObjectProperty.homMk ((representationRestriction R f).app F.obj)
  naturality {F E} a := by
    apply ObjectProperty.hom_ext
    exact (representationRestriction R f).naturality a.hom

@[simp]
theorem smoothRepresentationRestriction_app_hom
    {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y)
    (F : LocallySmoothModuleSheaf.{u, v, r, w} (ρ := ρ) (R := R)) :
    (SmoothRep.hom ((smoothRepresentationRestriction (R := R) f).app F)).toLinearMap =
      (F.obj.obj.map f.op).hom := rfl

@[simp]
theorem smoothRepresentationRestriction_id_hom (X : ρ.OpenSubgroupTransport)
    (F : LocallySmoothModuleSheaf.{u, v, r, w} (ρ := ρ) (R := R)) :
    (SmoothRep.hom ((smoothRepresentationRestriction (R := R) (𝟙 X)).app F)).toLinearMap =
      LinearMap.id :=
  representationRestriction_id_hom R X F.obj

/-- Composite arrows retain the original contravariant linear restrictions. -/
theorem smoothRepresentationRestriction_comp_hom {X Y Z : ρ.OpenSubgroupTransport}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : LocallySmoothModuleSheaf.{u, v, r, w} (ρ := ρ) (R := R)) :
    (SmoothRep.hom ((smoothRepresentationRestriction (R := R) (f ≫ g)).app F)).toLinearMap =
      (SmoothRep.hom ((smoothRepresentationRestriction (R := R) f).app F)).toLinearMap.comp
        (SmoothRep.hom ((smoothRepresentationRestriction (R := R) g).app F)).toLinearMap :=
  representationRestriction_comp_hom R f g F.obj

/-- Arbitrary ambient smooth coefficients give actual locally smooth module
sheaves on the original site, with every coefficient intertwiner. -/
def locallyConstantSmoothSheafFunctor :
    SmoothRep.{r, v, w} R G ⥤
      LocallySmoothModuleSheaf.{u, v, r, max u w} (ρ := ρ) (R := R) :=
  (locallySmoothProperty (ρ := ρ) (R := R)).lift
    (SmoothRep.toRep ⋙ locallyConstantSheafFunctor)
    (fun M X => locallyConstantSectionRepresentation_isSmooth M X)

/-- Forgetting local smoothness is the actual constructed locally constant
module sheaf functor on the unchanged rational transport site. -/
def locallyConstantSmoothSheafForgetIso :
    locallyConstantSmoothSheafFunctor (ρ := ρ) (R := R) ⋙ locallySmoothInclusion ≅
      SmoothRep.toRep ⋙ locallyConstantSheafFunctor :=
  Iso.refl _

/-- The entire locally constant section module with its proved smooth action,
functorial in the ambient smooth coefficients. -/
abbrev locallyConstantSmoothSections (X : ρ.OpenSubgroupTransport) :
    SmoothRep.{r, v, w} R G ⥤ SmoothRep.{r, v, max u w} R X.subgroup :=
  locallyConstantSmoothSheafFunctor ⋙ smoothSectionRepresentation X

@[simp]
theorem locallyConstantSmoothSections_action_apply (X : ρ.OpenSubgroupTransport)
    (M : SmoothRep.{r, v, w} R G) (k : X.subgroup)
    (s : LocallyConstant X.domain.obj.locus M) (x : X.domain.obj.locus) :
    LocallyConstant.toFun
        (((locallyConstantSmoothSections (R := R) X).obj M).representation k s) x =
      M.representation (k : G) (s (k⁻¹ • x)) :=
  locallyConstantSectionRepresentation_apply M.obj X k s x

@[simp]
theorem locallyConstantSmoothSections_map_apply (X : ρ.OpenSubgroupTransport)
    {M N : SmoothRep.{r, v, w} R G} (a : M ⟶ N)
    (s : LocallyConstant X.domain.obj.locus M) (x : X.domain.obj.locus) :
    LocallyConstant.toFun
        (SmoothRep.hom ((locallyConstantSmoothSections (R := R) X).map a) s) x =
      SmoothRep.hom a (s x) := rfl

/-- The original labelled pullback for all smooth coefficients, natural in
coefficients and with the original varying subgroups retained. -/
def locallyConstantSmoothRestriction {X Y : ρ.OpenSubgroupTransport} (f : X ⟶ Y) :
    locallyConstantSmoothSections (R := R) Y ⋙ smoothConjugationRestriction f ⟶
      (locallyConstantSmoothSections X :
        SmoothRep.{r, v, w} R G ⥤ SmoothRep.{r, v, max u w} R X.subgroup) :=
  Functor.whiskerLeft locallyConstantSmoothSheafFunctor
    (smoothRepresentationRestriction f)

@[simp]
theorem locallyConstantSmoothRestriction_apply {X Y : ρ.OpenSubgroupTransport}
    (f : X ⟶ Y) (M : SmoothRep.{r, v, w} R G)
    (s : LocallyConstant Y.domain.obj.locus M) (x : X.domain.obj.locus) :
    LocallyConstant.toFun
        (SmoothRep.hom ((locallyConstantSmoothRestriction (R := R) f).app M) s) x =
      M.representation f.label⁻¹ (s (f.locusMap x)) := rfl

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
