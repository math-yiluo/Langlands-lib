import Langlands.Geometry.Analytic.GeneralizedAffinoid.CoordinateContinuity
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormStabilizer
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralTests
import Mathlib.Analysis.Normed.Ring.Units

/-! # Norm-continuous rational section actions and positive spectral tests -/

noncomputable section

universe u v w t

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory Filter
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}

/-- The actual new quotient coordinate of a weighted rational chart. -/
abbrev fractionCoordinate (d : RationalChart K A) (j : Fin d.arity) : d.algebra :=
  RationalPresentation.fraction K A d.radii d.denominator d.numerators j

theorem baseMap_denominator_mul_fractionCoordinate (d : RationalChart K A)
    (j : Fin d.arity) :
    d.baseMap d.denominatorClass * d.fractionCoordinate j =
      d.baseMap (d.numeratorClass j) :=
  RationalPresentation.fraction_equation K A d.radii d.denominator d.numerators j

/-- Any bounded algebra map preserves the proved unit rational denominator. -/
theorem isUnit_map_denominator (d : RationalChart K A)
    {B : PresentedAffinoidAlgebra K} (φ : BoundedAlgHom K d.algebra B) :
    IsUnit (φ (d.baseMap d.denominatorClass)) :=
  (RationalPresentation.isUnit_baseMap_denominator K A d.radii d.denominator
    d.numerators d.generates).map φ.toAlgHom

/-- Fraction images are determined by the actual unit denominator and numerator. -/
theorem map_fractionCoordinate_eq_inverse_mul (d : RationalChart K A)
    {B : PresentedAffinoidAlgebra K} (φ : BoundedAlgHom K d.algebra B)
    (j : Fin d.arity) :
    φ (d.fractionCoordinate j) = Ring.inverse (φ (d.baseMap d.denominatorClass)) *
      φ (d.baseMap (d.numeratorClass j)) := by
  rw [← d.baseMap_denominator_mul_fractionCoordinate j, map_mul]
  exact (Ring.inverse_mul_cancel_left _ _ (d.isUnit_map_denominator φ)).symm

variable [CompleteSpace K]

/-- Continuity on base sections gives quotient-norm continuity of every new
fraction coordinate, by continuity of ring inversion at a unit. -/
theorem continuousAt_map_fractionCoordinate (d : RationalChart K A)
    {T : Type v} [TopologicalSpace T] {x : T}
    {B : PresentedAffinoidAlgebra K} (φ : T → BoundedAlgHom K d.algebra B)
    (hb : ∀ a : A, ContinuousAt (fun t => φ t (d.baseMap a)) x)
    (j : Fin d.arity) :
    ContinuousAt (fun t => φ t (d.fractionCoordinate j)) x := by
  obtain ⟨z, hz⟩ := d.isUnit_map_denominator (φ x)
  have hi : ContinuousAt
      (fun t => Ring.inverse (φ t (d.baseMap d.denominatorClass))) x := by
    have h : ContinuousAt Ring.inverse (φ x (d.baseMap d.denominatorClass)) :=
      hz ▸ NormedRing.inverse_continuousAt z
    exact h.comp (f := fun t => φ t (d.baseMap d.denominatorClass)) (hb d.denominatorClass)
  simp_rw [d.map_fractionCoordinate_eq_inverse_mul]
  exact hi.mul (hb (d.numeratorClass j))

/-- Continuity on the base gives continuity on both finite coordinate blocks
of the actual weighted rational quotient presentation. -/
theorem continuousAt_map_coordinates (d : RationalChart K A)
    {T : Type v} [TopologicalSpace T] {x : T}
    {B : PresentedAffinoidAlgebra K} (φ : T → BoundedAlgHom K d.algebra B)
    (hb : ∀ a : A, ContinuousAt (fun t => φ t (d.baseMap a)) x)
    (i : Fin d.algebra.arity) :
    ContinuousAt (fun t => φ t (coordinate K d.algebra i)) x := by
  change Fin (A.arity + d.arity) at i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have heq : d.baseMap (coordinate K A i) =
        coordinate K d.algebra (Fin.castAdd d.arity i) :=
      RationalPresentation.baseMap_coordinate K A d.radii d.denominator d.numerators i
    simpa only [heq] using hb (coordinate K A i)
  · exact d.continuousAt_map_fractionCoordinate φ hb j

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* Aut A)
  (hρ : ∀ a : A, Continuous (fun g : G => (ρ g).hom.toAlgHom a))

/-- The actual bounded section action becomes a norm-continuous action from
the base orbits, with its full original quotient algebra and operator maps. -/
def normContinuousSectionAction (d : RationalChart K A) :
    NormContinuousAction K (normOpenStabilizer ρ hρ d) := by
  let H := normOpenStabilizer ρ hρ d
  letI : IsTopologicalGroup H :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)
  apply normContinuousActionOfCoordinates d.algebra (normSectionAction ρ hρ d)
  intro i
  apply d.continuousAt_map_coordinates
    (fun g : H => (normSectionAction ρ hρ d g).hom)
  intro a
  have hc : Continuous (fun g : H =>
      (normSectionAction ρ hρ d g).hom.toAlgHom (d.baseMap a)) := by
    simp_rw [normSectionAction_baseMap]
    exact d.baseMap.continuous.comp ((hρ a).comp continuous_subtype_val)
  exact hc.continuousAt

@[simp]
theorem normContinuousSectionAction_algebra (d : RationalChart K A) :
    (normContinuousSectionAction ρ hρ d).obj.V = d.algebra := rfl

@[simp]
theorem normContinuousSectionAction_actionAut (d : RationalChart K A) :
    (normContinuousSectionAction ρ hρ d).actionAut = normSectionAction ρ hρ d := by
  simp only [normContinuousSectionAction, normContinuousActionOfCoordinates_actionAut]
  rfl

/-- Every actual quotient section has a norm-continuous orbit in the original
open stabilizer topology. -/
theorem continuous_normSectionAction (d : RationalChart K A) (b : d.algebra) :
    Continuous (fun g : normOpenStabilizer ρ hρ d =>
      (normSectionAction ρ hρ d g).hom.toAlgHom b) :=
  (normContinuousSectionAction ρ hρ d).property b

/-- Positive displacement tolerances are met in quotient norm near identity. -/
theorem eventually_normSectionAction_sub_lt (d : RationalChart K A)
    (b : d.algebra) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ g in 𝓝 (1 : normOpenStabilizer ρ hρ d),
      ‖(normSectionAction ρ hρ d g).hom.toAlgHom b - b‖ < r := by
  have hc : Continuous (fun g : normOpenStabilizer ρ hρ d =>
      ‖(normSectionAction ρ hρ d g).hom.toAlgHom b - b‖) :=
    ((continuous_normSectionAction ρ hρ d b).sub continuous_const).norm
  have hz : ‖(normSectionAction ρ hρ d 1).hom.toAlgHom b - b‖ < r := by
    rw [map_one]
    change ‖b - b‖ < r
    simpa only [sub_self, norm_zero] using hr
  exact hc.continuousAt.eventually (gt_mem_nhds hz)

include hρ in
/-- Each actual represented rational-domain spectral test pulls back to a
neighborhood in the original ambient group. -/
theorem normDomainSpectralSubgroup_mem_nhds (d : RationalChart K A)
    (b : d.algebra) (r : ℝ) (hr : 0 < r) :
    ρ ⁻¹' (DomainAutomorphism.domainSpectralSubgroup d.toDomain b r hr.le :
      Set (Aut A)) ∈ 𝓝 (1 : G) := by
  let H := normOpenStabilizer ρ hρ d
  have ht : ∀ᶠ g in 𝓝 (1 : H),
      ρ g.val ∈ DomainAutomorphism.domainSpectralSubgroup d.toDomain b r hr.le := by
    filter_upwards [eventually_normSectionAction_sub_lt ρ hρ d b r hr] with g hg
    apply (DomainAutomorphism.mem_domainSpectralSubgroup d.toDomain b r hr.le
      (ρ g.val)).mpr
    refine ⟨g.property, fun x => ?_⟩
    exact (x.le_norm _).trans hg.le
  have hmap : Filter.map (fun g : H => (g : G)) (𝓝 (1 : H)) = 𝓝 (1 : G) :=
    H.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq (1 : H)
  rw [← hmap]
  exact ht

/-- Bundle the full pullback of a positive rational-domain spectral test as an
open subgroup of the original group, with openness derived from norm orbits. -/
def normSpectralOpenSubgroup (d : RationalChart K A)
    (b : d.algebra) (r : ℝ) (hr : 0 < r) : OpenSubgroup G where
  toSubgroup := (DomainAutomorphism.domainSpectralSubgroup d.toDomain b r hr.le).comap ρ
  isOpen' := by
    apply Subgroup.isOpen_of_mem_nhds
    exact normDomainSpectralSubgroup_mem_nhds ρ hρ d b r hr

@[simp]
theorem mem_normSpectralOpenSubgroup (d : RationalChart K A)
    (b : d.algebra) (r : ℝ) (hr : 0 < r) (g : G) :
    g ∈ normSpectralOpenSubgroup ρ hρ d b r hr ↔
      ∃ hg : g ∈ normOpenStabilizer ρ hρ d,
        ∀ x : BanachSpectrum d.algebra,
          x ((normSectionAction ρ hρ d ⟨g, hg⟩).hom.toAlgHom b - b) ≤ r := by
  exact DomainAutomorphism.mem_domainSpectralSubgroup d.toDomain b r hr.le (ρ g)

/-- Finite positive local tests give a common original-group open subgroup
inside any prescribed open subgroup, retaining all actual local sections. -/
def finiteNormSpectralOpenSubgroup {ι : Type t} [Finite ι]
    (d : ι → RationalChart K A) (b : ∀ i, (d i).algebra)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (U : OpenSubgroup G) : OpenSubgroup G :=
  U ⊓ OpenSubgroup.iInfOfFinite (fun i => normSpectralOpenSubgroup ρ hρ (d i) (b i) (r i) (hr i))

@[simp]
theorem mem_finiteNormSpectralOpenSubgroup {ι : Type t} [Finite ι]
    (d : ι → RationalChart K A) (b : ∀ i, (d i).algebra)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (U : OpenSubgroup G) (g : G) :
    g ∈ finiteNormSpectralOpenSubgroup ρ hρ d b r hr U ↔
      g ∈ U ∧ ∀ i, ∃ hi : g ∈ normOpenStabilizer ρ hρ (d i),
        ∀ x : BanachSpectrum (d i).algebra,
          x ((normSectionAction ρ hρ (d i) ⟨g, hi⟩).hom.toAlgHom (b i) - b i) ≤ r i := by
  change (g ∈ U ∧ g ∈
    (⨅ i, (normSpectralOpenSubgroup ρ hρ (d i) (b i) (r i) (hr i)).toSubgroup)) ↔ _
  simp only [Subgroup.mem_iInf, OpenSubgroup.mem_toSubgroup, mem_normSpectralOpenSubgroup]

theorem finiteNormSpectralOpenSubgroup_le {ι : Type t} [Finite ι]
    (d : ι → RationalChart K A) (b : ∀ i, (d i).algebra)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (U : OpenSubgroup G) :
    finiteNormSpectralOpenSubgroup ρ hρ d b r hr U ≤ U := inf_le_left

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
