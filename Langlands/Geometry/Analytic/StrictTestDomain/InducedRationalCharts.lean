import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSpectrum
import Langlands.Topology.GroupAction.InducedCharts
import Mathlib.Topology.Sets.Opens

/-! # Open charts and coset coordinates for actual induced rational spectra -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

variable (X : ρ.OpenSubgroupTransport)

/-- Each translate of the actual rational quotient spectrum is a continuous chart. -/
def inducedChart (a : G) : C(X.LocalSpectrum, X.InducedSpectrum) :=
  ⟨TopologicalInduction.chart X.subgroup.toSubgroup a,
    TopologicalInduction.continuous_chart X.subgroup.toSubgroup a⟩

@[simp]
theorem inducedChart_apply (a : G) (x : X.LocalSpectrum) :
    X.inducedChart a x = X.inducedMk a x := rfl

@[simp]
theorem inducedChart_one : X.inducedChart 1 = X.inducedUnit := rfl

/-- The left-coset component of a point of the actual induced spectrum. -/
def inducedComponent : C(X.InducedSpectrum, G ⧸ X.subgroup.toSubgroup) :=
  ⟨TopologicalInduction.component X.subgroup.toSubgroup,
    TopologicalInduction.continuous_component X.subgroup.toSubgroup⟩

@[simp]
theorem inducedComponent_mk (a : G) (x : X.LocalSpectrum) :
    X.inducedComponent (X.inducedMk a x) = (a : G ⧸ X.subgroup.toSubgroup) := rfl

theorem isOpenEmbedding_inducedChart (a : G) : IsOpenEmbedding (X.inducedChart a) :=
  TopologicalInduction.isOpenEmbedding_chart X.subgroup.toSubgroup X.subgroup.isOpen' a

theorem range_inducedChart_eq_fiber (a : G) :
    Set.range (X.inducedChart a) =
      X.inducedComponent ⁻¹' {(a : G ⧸ X.subgroup.toSubgroup)} :=
  TopologicalInduction.range_chart_eq_fiber X.subgroup.toSubgroup a

theorem isClopen_range_inducedChart (a : G) : IsClopen (Set.range (X.inducedChart a)) :=
  TopologicalInduction.isClopen_range_chart X.subgroup.toSubgroup X.subgroup.isOpen' a

theorem iUnion_range_inducedChart :
    (⋃ a : G, Set.range (X.inducedChart a)) = Set.univ :=
  TopologicalInduction.iUnion_range_chart X.subgroup.toSubgroup

/-- The actual open subset occupied by a translated rational quotient spectrum. -/
def inducedChartDomain (a : G) : TopologicalSpace.Opens X.InducedSpectrum :=
  ⟨Set.range (X.inducedChart a), (X.isOpenEmbedding_inducedChart a).isOpen_range⟩

theorem mem_inducedChartDomain_iff (a : G) (z : X.InducedSpectrum) :
    z ∈ X.inducedChartDomain a ↔
      X.inducedComponent z = (a : G ⧸ X.subgroup.toSubgroup) := by
  change z ∈ Set.range (X.inducedChart a) ↔ _
  rw [X.range_inducedChart_eq_fiber]
  rfl

/-- Each open chart domain is homeomorphic to the actual rational quotient spectrum. -/
def inducedChartHomeomorph (a : G) : X.LocalSpectrum ≃ₜ X.inducedChartDomain a :=
  (X.isOpenEmbedding_inducedChart a).isEmbedding.toHomeomorph

@[simp]
theorem inducedChartHomeomorph_apply_coe (a : G) (x : X.LocalSpectrum) :
    (X.inducedChartHomeomorph a x : X.InducedSpectrum) = X.inducedChart a x := rfl

/-- Representative changes are the actual constructed subgroup action. -/
theorem inducedChart_mul_subgroup (a : G) (h : X.subgroup) (x : X.LocalSpectrum) :
    X.inducedChart (a * (h : G)) x = X.inducedChart a (h • x) :=
  TopologicalInduction.chart_mul_subgroup X.subgroup.toSubgroup a h x

@[simp]
theorem ambientMap_inducedChart (a : G) (x : X.LocalSpectrum) :
    X.ambientMap (X.inducedChart a x) = a • X.localToAmbient x := rfl

/-- Coset copies of the actual rational quotient spectrum, with the sum topology. -/
abbrev InducedCosetCopies := Σ _c : G ⧸ X.subgroup.toSubgroup, X.LocalSpectrum

/-- The coset-copy model of the actual induced rational spectrum. -/
def inducedCosetHomeomorph : X.InducedCosetCopies ≃ₜ X.InducedSpectrum :=
  TopologicalInduction.cosetCopiesHomeomorph X.subgroup.toSubgroup X.subgroup.isOpen'

@[simp]
theorem inducedCosetHomeomorph_apply (c : G ⧸ X.subgroup.toSubgroup) (x : X.LocalSpectrum) :
    X.inducedCosetHomeomorph ⟨c, x⟩ = X.inducedChart c.out x := rfl

@[simp]
theorem inducedComponent_inducedCosetHomeomorph (p : X.InducedCosetCopies) :
    X.inducedComponent (X.inducedCosetHomeomorph p) = p.1 :=
  TopologicalInduction.component_ofCosetCopies X.subgroup.toSubgroup p

theorem smul_inducedCosetHomeomorph (a : G) (c d : G ⧸ X.subgroup.toSubgroup)
    (h : X.subgroup) (he : a * c.out = d.out * (h : G)) (x : X.LocalSpectrum) :
    a • X.inducedCosetHomeomorph ⟨c, x⟩ =
      X.inducedCosetHomeomorph ⟨d, h • x⟩ :=
  TopologicalInduction.smul_cosetCopiesHomeomorph
    X.subgroup.toSubgroup X.subgroup.isOpen' a c d h he x

namespace Hom

variable {X Y Z : ρ.OpenSubgroupTransport}

/-- A transport label induces the right-inverse-label map on left cosets. -/
def cosetMap (f : X ⟶ Y) :
    C(G ⧸ X.subgroup.toSubgroup, G ⧸ Y.subgroup.toSubgroup) where
  toFun := Quotient.lift (fun a : G => (a * f.label⁻¹ : G ⧸ Y.subgroup.toSubgroup)) (by
    intro a b hab
    apply QuotientGroup.eq.mpr
    have h : a⁻¹ * b ∈ X.subgroup := QuotientGroup.leftRel_apply.mp hab
    have ht := (f.groupHom ⟨a⁻¹ * b, h⟩).property
    simpa [groupHom_apply, mul_assoc] using ht)
  continuous_toFun :=
    (QuotientGroup.continuous_mk.comp (continuous_id.mul_const f.label⁻¹)).quotient_lift _

@[simp]
theorem cosetMap_mk (f : X ⟶ Y) (a : G) :
    f.cosetMap (a : G ⧸ X.subgroup.toSubgroup) =
      (a * f.label⁻¹ : G ⧸ Y.subgroup.toSubgroup) := rfl

@[simp]
theorem cosetMap_id (X : ρ.OpenSubgroupTransport) (c : G ⧸ X.subgroup.toSubgroup) :
    (𝟙 X : X ⟶ X).cosetMap c = c := by
  induction c using Quotient.inductionOn with
  | h a => simp

@[simp]
theorem cosetMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (c : G ⧸ X.subgroup.toSubgroup) :
    (f ≫ g).cosetMap c = g.cosetMap (f.cosetMap c) := by
  induction c using Quotient.inductionOn with
  | h a => simp [mul_assoc]

theorem inducedComponent_inducedMap (f : X ⟶ Y) (z : X.InducedSpectrum) :
    Y.inducedComponent (f.inducedMap z) = f.cosetMap (X.inducedComponent z) := by
  induction z using Quotient.inductionOn with
  | h p =>
    change Y.inducedComponent (f.inducedMap (X.inducedMk p.1 p.2)) =
      f.cosetMap (X.inducedComponent (X.inducedMk p.1 p.2))
    rw [inducedMap_mk, inducedComponent_mk, inducedComponent_mk, cosetMap_mk]

/-- Transport acts on every chart by the actual bounded-pullback spectrum map. -/
theorem inducedMap_chart (f : X ⟶ Y) (a : G) (x : X.LocalSpectrum) :
    f.inducedMap (X.inducedChart a x) =
      Y.inducedChart (a * f.label⁻¹) (f.localSpectrumMap x) :=
  f.inducedMap_mk a x

theorem mapsTo_inducedChartDomain (f : X ⟶ Y) (a : G) :
    Set.MapsTo f.inducedMap (X.inducedChartDomain a)
      (Y.inducedChartDomain (a * f.label⁻¹)) := by
  intro z hz
  change z ∈ Set.range (X.inducedChart a) at hz
  obtain ⟨x, rfl⟩ := hz
  exact ⟨f.localSpectrumMap x, (f.inducedMap_chart a x).symm⟩

/-- Restrict an actual induced transport arrow to its source and target charts. -/
def chartRestriction (f : X ⟶ Y) (a : G) :
    C(X.inducedChartDomain a, Y.inducedChartDomain (a * f.label⁻¹)) :=
  ⟨fun z => ⟨f.inducedMap z, f.mapsTo_inducedChartDomain a z.property⟩,
    (f.inducedMap.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem chartRestriction_inducedChartHomeomorph (f : X ⟶ Y) (a : G)
    (x : X.LocalSpectrum) :
    f.chartRestriction a (X.inducedChartHomeomorph a x) =
      Y.inducedChartHomeomorph (a * f.label⁻¹) (f.localSpectrumMap x) := by
  apply Subtype.ext
  exact f.inducedMap_chart a x

/-- The actual transport map in chosen coset-copy coordinates. -/
def inducedCoordinates (f : X ⟶ Y) : C(X.InducedCosetCopies, Y.InducedCosetCopies) :=
  ⟨fun p => Y.inducedCosetHomeomorph.symm
      (f.inducedMap (X.inducedCosetHomeomorph p)),
    Y.inducedCosetHomeomorph.symm.continuous.comp
      (f.inducedMap.continuous.comp X.inducedCosetHomeomorph.continuous)⟩

@[simp]
theorem inducedCosetHomeomorph_inducedCoordinates (f : X ⟶ Y) (p : X.InducedCosetCopies) :
    Y.inducedCosetHomeomorph (f.inducedCoordinates p) =
      f.inducedMap (X.inducedCosetHomeomorph p) :=
  Y.inducedCosetHomeomorph.apply_symm_apply _

theorem inducedCoordinates_fst (f : X ⟶ Y) (p : X.InducedCosetCopies) :
    (f.inducedCoordinates p).1 = f.cosetMap p.1 := by
  rw [← Y.inducedComponent_inducedCosetHomeomorph (f.inducedCoordinates p),
    inducedCosetHomeomorph_inducedCoordinates, inducedComponent_inducedMap,
    inducedComponent_inducedCosetHomeomorph]

/-- Once representatives are compared, the coordinate is the subgroup action
on comap by the actual bounded rational pullback. -/
theorem inducedCoordinates_apply_of_eq (f : X ⟶ Y)
    (c : G ⧸ X.subgroup.toSubgroup) (d : G ⧸ Y.subgroup.toSubgroup)
    (h : Y.subgroup) (he : c.out * f.label⁻¹ = d.out * (h : G)) (x : X.LocalSpectrum) :
    f.inducedCoordinates ⟨c, x⟩ = ⟨d, h • f.localSpectrumMap x⟩ := by
  apply Y.inducedCosetHomeomorph.injective
  rw [inducedCosetHomeomorph_inducedCoordinates, inducedCosetHomeomorph_apply,
    inducedMap_chart, he, inducedCosetHomeomorph_apply, inducedChart_mul_subgroup]

@[simp]
theorem inducedCoordinates_id (X : ρ.OpenSubgroupTransport) (p : X.InducedCosetCopies) :
    (𝟙 X : X ⟶ X).inducedCoordinates p = p := by
  change X.inducedCosetHomeomorph.symm
    ((𝟙 X : X ⟶ X).inducedMap (X.inducedCosetHomeomorph p)) = p
  rw [inducedMap_id, Homeomorph.symm_apply_apply]

@[simp]
theorem inducedCoordinates_comp (f : X ⟶ Y) (g : Y ⟶ Z) (p : X.InducedCosetCopies) :
    (f ≫ g).inducedCoordinates p = g.inducedCoordinates (f.inducedCoordinates p) := by
  change Z.inducedCosetHomeomorph.symm
    ((f ≫ g).inducedMap (X.inducedCosetHomeomorph p)) =
    Z.inducedCosetHomeomorph.symm
      (g.inducedMap (Y.inducedCosetHomeomorph
        (Y.inducedCosetHomeomorph.symm (f.inducedMap (X.inducedCosetHomeomorph p)))))
  rw [inducedMap_comp, Homeomorph.apply_symm_apply]

end Hom

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
