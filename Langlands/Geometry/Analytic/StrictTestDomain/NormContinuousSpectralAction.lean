import Langlands.Geometry.Analytic.StrictTestDomain.SpectralAction
import Langlands.Geometry.Analytic.StrictTestDomain.RationalStabilizerProof
import Langlands.Geometry.Analytic.StrictTestDomain.RationalSectionContinuityProof

/-! # Rational spectral actions from norm-continuous base orbits -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism

open CategoryTheory Filter
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Norm-continuous base orbits satisfy every positive rational spectral test
on a neighborhood of the identity. -/
theorem rationalSpectralSubgroup_mem_nhds_of_normContinuous
    (ρ : G →* Aut P)
    (hb : ∀ a : P, Continuous (fun g : G => (ρ g).hom.toAlgHom a))
    (d : RationalData K P) (b : d.algebra) (r : ℝ) (hr : 0 < r) :
    ρ ⁻¹' (rationalSpectralSubgroup d b r hr.le : Set (Aut P)) ∈ 𝓝 (1 : G) := by
  let H : Subgroup G := (locusStabilizer d).comap ρ
  have hH : IsOpen (H : Set G) := isOpen_rationalLocusStabilizer ρ hb d
  let σ : H →* locusStabilizer d :=
    { toFun := fun g => ⟨ρ g, g.property⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun g h => Subtype.ext (map_mul ρ (g : G) (h : G)) }
  have hσ (a : P) :
      Continuous (fun g : H => (σ g : Aut P).hom.toAlgHom a) :=
    (hb a).comp continuous_subtype_val
  have hc : Continuous (fun g : H =>
      ‖(stabilizerSectionAction d (σ g)).hom.toAlgHom b - b‖) :=
    ((continuous_section_orbit d σ hσ b).sub continuous_const).norm
  have hz : ‖(stabilizerSectionAction d (σ (1 : H))).hom.toAlgHom b - b‖ < r := by
    rw [map_one, map_one]
    change ‖b - b‖ < r
    simpa only [sub_self, norm_zero] using hr
  have hsmall : ∀ᶠ g in 𝓝 (1 : H),
      ‖(stabilizerSectionAction d (σ g)).hom.toAlgHom b - b‖ < r :=
    hc.continuousAt.eventually (gt_mem_nhds hz)
  have htest : ∀ᶠ (g : H) in 𝓝 (1 : H),
      ρ g ∈ rationalSpectralSubgroup d b r hr.le := by
    filter_upwards [hsmall] with g hg
    apply (mem_rationalSpectralSubgroup d b r hr.le (ρ g)).mpr
    refine ⟨g.property, fun x => ?_⟩
    exact (x.le_norm _).trans hg.le
  have hmap : Filter.map (fun g : H => (g : G)) (𝓝 (1 : H)) = 𝓝 (1 : G) := by
    exact hH.isOpenEmbedding_subtypeVal.map_nhds_eq (1 : H)
  rw [← hmap]
  exact htest

/-- Norm-continuous forward base orbits give continuity for the restricted
rational spectral topology on actual bounded algebra automorphisms. -/
theorem continuous_rationalSpectralTopology_of_normContinuous
    (ρ : G →* Aut P)
    (hb : ∀ a : P, Continuous (fun g : G => (ρ g).hom.toAlgHom a)) :
    @Continuous G (Aut P) _ (rationalSpectralTopology P) ρ := by
  apply (continuous_rationalSpectralTopology_iff P ρ).mpr
  intro ι hι tests
  have ht : ∀ᶠ g in 𝓝 (1 : G), ∀ i,
      ρ g ∈ rationalSpectralSubgroup (tests i).domain (tests i).element
        (tests i).radius (tests i).radius_pos.le :=
    Filter.eventually_all.mpr (fun i =>
      rationalSpectralSubgroup_mem_nhds_of_normContinuous ρ hb
        (tests i).domain (tests i).element (tests i).radius (tests i).radius_pos)
  filter_upwards [ht] with g hg
  exact Subgroup.mem_iInf.mpr hg

namespace RationalSpectralAction

/-- Construct a rational spectral action from norm-continuous forward orbits
on the base affinoid algebra, retaining the given algebraic action. -/
def ofNormContinuous (ρ : G →* Aut P)
    (hb : ∀ a : P, Continuous (fun g : G => (ρ g).hom.toAlgHom a)) :
    RationalSpectralAction G P :=
  ⟨ρ, continuous_rationalSpectralTopology_of_normContinuous ρ hb⟩

@[simp] theorem ofNormContinuous_toMonoidHom (ρ : G →* Aut P)
    (hb : ∀ a : P, Continuous (fun g : G => (ρ g).hom.toAlgHom a)) :
    (ofNormContinuous ρ hb).toMonoidHom = ρ := rfl

end RationalSpectralAction

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism
