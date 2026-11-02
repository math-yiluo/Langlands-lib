import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCompactCharts
import Langlands.Representation.LocallyConstant.CompactSupport

/-! # Compactly supported smooth sections on actual induced rational spectra -/

noncomputable section

universe u v r w

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type r} [CommRing R]

namespace OpenSubgroupTransport

namespace CompactSections

open Langlands.CompactAction.LocallyConstantModule

variable (X : ρ.OpenSubgroupTransport) {V : Type w} [AddCommGroup V] [Module R V]

/-- The full compact-support module on the actual balanced quotient spectrum. -/
abbrev Functions := CompactSupport.Functions R X.InducedSpectrum V

/-- The coset components at which the function has a nonzero value. -/
def componentSupport (f : LocallyConstant X.InducedSpectrum V) :
    Set (G ⧸ X.subgroup.toSubgroup) :=
  X.inducedComponent '' Function.support f

/-- Local constancy closes the support without any topology on the coefficients. -/
theorem tsupport_eq_support (f : LocallyConstant X.InducedSpectrum V) :
    tsupport f = Function.support f :=
  (f.isLocallyConstant.isOpen_fiber 0).isClosed_compl.closure_eq

/-- Compact support is precisely finiteness of the actual nonzero coset components. -/
theorem hasCompactSupport_iff_finite_componentSupport
    (f : LocallyConstant X.InducedSpectrum V) :
    HasCompactSupport f ↔ (componentSupport X f).Finite := by
  change IsCompact (tsupport f) ↔ _
  rw [tsupport_eq_support X f, X.isCompact_iff_isClosed_finite_inducedComponent_image]
  exact and_iff_right (f.isLocallyConstant.isOpen_fiber 0).isClosed_compl

theorem finite_componentSupport (f : Functions (R := R) (V := V) X) :
    (componentSupport X f.val).Finite :=
  (hasCompactSupport_iff_finite_componentSupport X f.val).mp f.property

theorem exists_finite_chart_cover (f : Functions (R := R) (V := V) X) :
    ∃ C : Finset (G ⧸ X.subgroup.toSubgroup),
      tsupport f.val ⊆ ⋃ c ∈ C, (X.inducedChartDomain c.out : Set X.InducedSpectrum) :=
  X.exists_finite_inducedChart_cover_of_isCompact f.property

/-- Every compactly supported locally constant function has the proved smooth
diagonal action of the full operator group. -/
def smoothRepresentation (M : SmoothRep.{r, v, w} R G) :
    SmoothRep.{r, v, max u v w} R G :=
  CompactSupport.smoothRepresentation (X := X.InducedSpectrum) M

@[simp]
theorem smoothRepresentation_apply (M : SmoothRep.{r, v, w} R G) (g : G)
    (f : Functions (R := R) (V := M) X) (z : X.InducedSpectrum) :
    ((smoothRepresentation X M).representation g f).val z =
      M.representation g (f.val (g⁻¹ • z)) := rfl

/-- The actual induced-spectrum compact-support construction is functorial in
all smooth module coefficients. -/
def coefficientFunctor :
    SmoothRep.{r, v, w} R G ⥤ SmoothRep.{r, v, max u v w} R G :=
  CompactSupport.coefficientFunctor (X := X.InducedSpectrum)

@[simp]
theorem coefficientFunctor_map_apply {M N : SmoothRep.{r, v, w} R G} (b : M ⟶ N)
    (f : Functions (R := R) (V := M) X) (z : X.InducedSpectrum) :
    (SmoothRep.hom ((coefficientFunctor X).map b) f).val z =
      SmoothRep.hom b (f.val z) := rfl

/-- Extension by zero from one actual compact clopen chart. -/
def chartExtension (a : G) (f : LocallyConstant (X.inducedChartDomain a) V) :
    Functions (R := R) (V := V) X := by
  let e : X.InducedSpectrum → V := Subtype.val.extend f 0
  have hf : HasCompactSupport f := HasCompactSupport.of_compactSpace f
  refine ⟨⟨e, ?_⟩, hf.extend_zero continuous_subtype_val⟩
  let : TopologicalSpace V := ⊥
  let : DiscreteTopology V := discreteTopology_bot V
  exact (IsLocallyConstant.iff_continuous e).mpr
    (hf.continuous_extend_zero (X.inducedChartDomain a).isOpen f.continuous)

@[simp]
theorem chartExtension_apply (a : G) (f : LocallyConstant (X.inducedChartDomain a) V)
    (z : X.inducedChartDomain a) :
    (chartExtension (R := R) X a f).val z = f z :=
  Function.Injective.extend_apply Subtype.val_injective f 0 z

theorem chartExtension_apply_of_not_mem (a : G)
    (f : LocallyConstant (X.inducedChartDomain a) V) {z : X.InducedSpectrum}
    (hz : z ∉ X.inducedChartDomain a) :
    (chartExtension (R := R) X a f).val z = 0 := by
  apply Function.extend_apply'
  rintro ⟨x, rfl⟩
  exact hz x.property

theorem tsupport_chartExtension_subset (a : G)
    (f : LocallyConstant (X.inducedChartDomain a) V) :
    tsupport (chartExtension (R := R) X a f).val ⊆
      (X.inducedChartDomain a : Set X.InducedSpectrum) := by
  rw [tsupport_eq_support]
  intro z hz
  by_contra hn
  exact hz (chartExtension_apply_of_not_mem X a f hn)

/-- Chart extension is an actual linear map, without any covariance condition. -/
def chartExtensionLinear (a : G) :
    LocallyConstant (X.inducedChartDomain a) V →ₗ[R] Functions (R := R) (V := V) X where
  toFun := chartExtension X a
  map_add' f g := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro z
    by_cases hz : z ∈ X.inducedChartDomain a
    · change (chartExtension (R := R) X a (f + g)).val z =
        (chartExtension (R := R) X a f).val z +
          (chartExtension (R := R) X a g).val z
      rw [chartExtension_apply X a (f + g) ⟨z, hz⟩,
        chartExtension_apply X a f ⟨z, hz⟩,
        chartExtension_apply X a g ⟨z, hz⟩]
      rfl
    · simp [chartExtension_apply_of_not_mem X a _ hz]
  map_smul' c f := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro z
    by_cases hz : z ∈ X.inducedChartDomain a
    · change (chartExtension (R := R) X a (c • f)).val z =
        c • (chartExtension (R := R) X a f).val z
      rw [chartExtension_apply X a (c • f) ⟨z, hz⟩,
        chartExtension_apply X a f ⟨z, hz⟩]
      rfl
    · simp [chartExtension_apply_of_not_mem X a _ hz]

/-- Restriction to an actual chart, on the full compact-support module. -/
def chartRestrictionLinear (a : G) :
    Functions (R := R) (V := V) X →ₗ[R] LocallyConstant (X.inducedChartDomain a) V :=
  (LocallyConstant.comapₗ R ⟨Subtype.val, continuous_subtype_val⟩).comp
    (CompactSupport.submodule R X.InducedSpectrum V).subtype

@[simp]
theorem chartRestrictionLinear_apply (a : G)
    (f : Functions (R := R) (V := V) X) (z : X.inducedChartDomain a) :
    chartRestrictionLinear X a f z = f.val z := rfl

@[simp]
theorem chartRestriction_extension (a : G)
    (f : LocallyConstant (X.inducedChartDomain a) V) :
    chartRestrictionLinear (R := R) X a (chartExtensionLinear X a f) = f := by
  apply LocallyConstant.ext
  intro z
  exact chartExtension_apply (R := R) X a f z

/-- A chart section on the actual local rational quotient spectrum extends
by zero along the constructed chart homeomorphism. -/
def localChartExtension (a : G) :
    LocallyConstant X.LocalSpectrum V →ₗ[R] Functions (R := R) (V := V) X :=
  (chartExtensionLinear X a).comp
    (LocallyConstant.comapₗ R
      ⟨(X.inducedChartHomeomorph a).symm,
        (X.inducedChartHomeomorph a).symm.continuous⟩)

@[simp]
theorem localChartExtension_apply (a : G) (f : LocallyConstant X.LocalSpectrum V)
    (x : X.LocalSpectrum) :
    (localChartExtension (R := R) X a f).val (X.inducedChart a x) = f x := by
  change (chartExtension (R := R) X a
    (f.comap ⟨(X.inducedChartHomeomorph a).symm,
      (X.inducedChartHomeomorph a).symm.continuous⟩)).val
        (X.inducedChartHomeomorph a x) = _
  rw [chartExtension_apply]
  exact congrArg f ((X.inducedChartHomeomorph a).symm_apply_apply x)

/-- The linear projection to sections supported in one actual chart. -/
def chartPart (a : G) :
    Functions (R := R) (V := V) X →ₗ[R] Functions (R := R) (V := V) X :=
  (chartExtensionLinear X a).comp (chartRestrictionLinear X a)

@[simp]
theorem chartPart_apply (a : G) (f : Functions (R := R) (V := V) X)
    (z : X.inducedChartDomain a) :
    (chartPart X a f).val z = f.val z :=
  chartExtension_apply X a _ z

theorem chartPart_apply_of_not_mem (a : G) (f : Functions (R := R) (V := V) X)
    {z : X.InducedSpectrum} (hz : z ∉ X.inducedChartDomain a) :
    (chartPart X a f).val z = 0 :=
  chartExtension_apply_of_not_mem X a _ hz

open scoped Classical in
theorem chartPart_out_apply (c : G ⧸ X.subgroup.toSubgroup)
    (f : Functions (R := R) (V := V) X) (z : X.InducedSpectrum) :
    (chartPart X c.out f).val z =
      if X.inducedComponent z = c then f.val z else 0 := by
  classical
  have hm : z ∈ X.inducedChartDomain c.out ↔ X.inducedComponent z = c := by
    rw [X.mem_inducedChartDomain_iff, QuotientGroup.out_eq']
  by_cases h : X.inducedComponent z = c
  · rw [ite_eq_left h]
    exact chartPart_apply X c.out f ⟨z, hm.mpr h⟩
  · rw [ite_eq_right h]
    exact chartPart_apply_of_not_mem X c.out f (fun hz => h (hm.mp hz))

@[simp]
theorem chartPart_idempotent (a : G) (f : Functions (R := R) (V := V) X) :
    chartPart X a (chartPart X a f) = chartPart X a f := by
  change chartExtensionLinear X a
    (chartRestrictionLinear X a (chartExtensionLinear X a
      (chartRestrictionLinear X a f))) = _
  rw [chartRestriction_extension]
  rfl

theorem chartPart_out_orthogonal (c d : G ⧸ X.subgroup.toSubgroup) (hcd : c ≠ d)
    (f : Functions (R := R) (V := V) X) :
    chartPart X c.out (chartPart X d.out f) = 0 := by
  classical
  apply Subtype.ext
  apply LocallyConstant.ext
  intro z
  simp only [chartPart_out_apply]
  by_cases hc : X.inducedComponent z = c
  · simp [hc, hcd]
  · simp [hc]

/-- Finitely many actual chart projections reconstruct every section whose
nonzero component set they contain. -/
theorem sum_chartPart_eq (f : Functions (R := R) (V := V) X)
    (C : Finset (G ⧸ X.subgroup.toSubgroup))
    (hC : componentSupport X f.val ⊆ (C : Set (G ⧸ X.subgroup.toSubgroup))) :
    (∑ c ∈ C, chartPart X c.out f) = f := by
  classical
  apply Subtype.ext
  apply LocallyConstant.ext
  intro z
  let ev : Functions (R := R) (V := V) X →ₗ[R] V :=
    (LocallyConstant.evalₗ R z).comp
      (CompactSupport.submodule R X.InducedSpectrum V).subtype
  change ev (∑ c ∈ C, chartPart X c.out f) = ev f
  rw [map_sum]
  change (∑ c ∈ C, (chartPart X c.out f).val z) = f.val z
  simp only [chartPart_out_apply]
  by_cases hz : X.inducedComponent z ∈ C
  · rw [Finset.sum_eq_single (X.inducedComponent z)]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · exact fun h => (h hz).elim
  · have hzero : f.val z = 0 := by
      by_contra hn
      exact hz (hC ⟨z, hn, rfl⟩)
    simp [hzero]

/-- Every compactly supported section is a finite sum of its actual chart sections. -/
theorem exists_sum_chartPart (f : Functions (R := R) (V := V) X) :
    ∃ C : Finset (G ⧸ X.subgroup.toSubgroup),
      (∑ c ∈ C, chartPart X c.out f) = f := by
  classical
  exact ⟨(finite_componentSupport X f).toFinset,
    sum_chartPart_eq X f _ (by simp)⟩

/-- Coefficient maps commute with extension on every actual chart. -/
theorem coefficientMap_chartExtension {M N : SmoothRep.{r, v, w} R G}
    (b : M ⟶ N) (a : G) (f : LocallyConstant (X.inducedChartDomain a) M) :
    SmoothRep.hom ((coefficientFunctor X).map b) (chartExtension X a f) =
      chartExtension X a (LocallyConstant.mapₗ R (SmoothRep.hom b).toLinearMap f) := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro z
  rw [coefficientFunctor_map_apply]
  by_cases hz : z ∈ X.inducedChartDomain a
  · rw [chartExtension_apply X a f ⟨z, hz⟩,
      chartExtension_apply X a _ ⟨z, hz⟩]
    rfl
  · rw [chartExtension_apply_of_not_mem X a f hz,
      chartExtension_apply_of_not_mem X a _ hz]
    exact map_zero (SmoothRep.hom b)

end CompactSections

namespace Hom

open CompactSections

variable {X Y Z : ρ.OpenSubgroupTransport}

theorem isProperMap_inducedMap_id (X : ρ.OpenSubgroupTransport) :
    IsProperMap (𝟙 X : X ⟶ X).inducedMap := by
  have h : ⇑(𝟙 X : X ⟶ X).inducedMap = id := funext (inducedMap_id X)
  rw [h]
  exact isProperMap_id

theorem isProperMap_inducedMap_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap) :
    IsProperMap (f ≫ g).inducedMap := by
  have h : ⇑(f ≫ g).inducedMap = g.inducedMap ∘ f.inducedMap :=
    funext (inducedMap_comp f g)
  rw [h]
  exact hg.comp hf

/-- Only a proved proper induced transport map gives compact-support pullback. -/
def compactSupportPullback (f : X ⟶ Y) (hf : IsProperMap f.inducedMap)
    (M : SmoothRep.{r, v, w} R G) :
    smoothRepresentation Y M ⟶ smoothRepresentation X M :=
  Langlands.CompactAction.LocallyConstantModule.CompactSupport.smoothPullback
    M f.inducedMap hf f.inducedMap_smul

@[simp]
theorem compactSupportPullback_apply (f : X ⟶ Y) (hf : IsProperMap f.inducedMap)
    (M : SmoothRep.{r, v, w} R G)
    (s : Functions (R := R) (V := M) Y) (z : X.InducedSpectrum) :
    (SmoothRep.hom (f.compactSupportPullback hf M) s).val z =
      s.val (f.inducedMap z) := rfl

theorem compactSupportPullback_naturality (f : X ⟶ Y)
    (hf : IsProperMap f.inducedMap)
    {M N : SmoothRep.{r, v, w} R G} (b : M ⟶ N) :
    (coefficientFunctor Y).map b ≫ f.compactSupportPullback hf N =
      f.compactSupportPullback hf M ≫ (coefficientFunctor X).map b := by
  ext s
  apply Subtype.ext
  apply LocallyConstant.ext
  intro z
  rfl

@[simp]
theorem compactSupportPullback_id (M : SmoothRep.{r, v, w} R G) :
    (𝟙 X : X ⟶ X).compactSupportPullback (isProperMap_inducedMap_id X) M =
      𝟙 (smoothRepresentation X M) := by
  ext s
  apply Subtype.ext
  apply LocallyConstant.ext
  intro z
  exact congrArg s.val (inducedMap_id X z)

theorem compactSupportPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsProperMap f.inducedMap) (hg : IsProperMap g.inducedMap)
    (M : SmoothRep.{r, v, w} R G) :
    (f ≫ g).compactSupportPullback (isProperMap_inducedMap_comp f g hf hg) M =
      g.compactSupportPullback hg M ≫ f.compactSupportPullback hf M := by
  ext s
  apply Subtype.ext
  apply LocallyConstant.ext
  intro z
  exact congrArg s.val (inducedMap_comp f g z)

end Hom

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
