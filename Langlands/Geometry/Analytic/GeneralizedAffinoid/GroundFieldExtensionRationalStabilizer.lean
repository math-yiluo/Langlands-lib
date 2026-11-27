import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRationalCoverProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionCoefficientAction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormStabilizer

/-! # Open stabilizers of domains under coefficient automorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

open Set Filter
open scoped Topology Pointwise

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (A : PresentedAffinoidAlgebra K)

local notation "B" => algebra K L A
local notation "Γ" => isometricAutomorphisms K L

/-- Inverse pullback for coefficient automorphisms on an extended affinoid spectrum. -/
def coefficientSpectrumMap (σ : Γ) :
    BanachSpectrum B → BanachSpectrum B :=
  BanachSpectrum.comap (coefficientHom K L A σ⁻¹).toBoundedRingHom

@[instance_reducible]
private def coefficientSpectrumMulAction : MulAction Γ (BanachSpectrum B) where
  smul := coefficientSpectrumMap K L A
  one_smul x := by
    apply BanachSpectrum.ext
    intro b
    change x (coefficientHom K L A ((1 : Γ)⁻¹) b) = x b
    rw [inv_one, coefficientHom_one, BoundedAlgHom.id_apply]
  mul_smul σ τ x := by
    apply BanachSpectrum.ext
    intro b
    change x (coefficientHom K L A (σ * τ)⁻¹ b) =
      x (coefficientHom K L A τ⁻¹ (coefficientHom K L A σ⁻¹ b))
    rw [mul_inv_rev, coefficientHom_mul, BoundedAlgHom.comp_apply]

omit [CompleteSpace L] in
private theorem comap_mem_rational_locus (d : RationalChart L B) {ε : ℝ}
    (hε : ∀ x ∈ d.locus, ε ≤ x d.denominatorClass)
    (φ : BoundedRingHom B B)
    (hb : ‖φ d.denominatorClass - d.denominatorClass‖ < ε)
    (hf : ∀ j, ‖φ (d.numeratorClass j) - d.numeratorClass j‖ < d.radii j * ε)
    {x : BanachSpectrum B} (hx : x ∈ d.locus) :
    BanachSpectrum.comap φ x ∈ d.locus := by
  have hsmall : x.toMulRingSeminorm (φ d.denominatorClass - d.denominatorClass) <
      x.toMulRingSeminorm d.denominatorClass :=
    (x.le_norm _).trans_lt (hb.trans_le (hε x hx))
  have heq : x (φ d.denominatorClass) = x d.denominatorClass := by
    simpa only [sub_add_cancel] using
      (x.isNonarchimedean (K := L)).add_eq_right_of_lt
        (map_neg_eq_map x.toMulRingSeminorm) hsmall
  intro j
  change x (φ (d.numeratorClass j)) ≤ d.radii j * x (φ d.denominatorClass)
  rw [heq]
  have hnum := x.isNonarchimedean (K := L)
    (φ (d.numeratorClass j) - d.numeratorClass j) (d.numeratorClass j)
  simpa only [sub_add_cancel] using hnum.trans
    (max_le ((x.le_norm _).trans ((hf j).le.trans
      (mul_le_mul_of_nonneg_left (hε x hx) (d.radii.positive j).le))) (hx j))

variable {G : Type w} [Group G] [TopologicalSpace G]
variable (ρ : G →* ↥(isometricAutomorphisms K L))
variable (hρ : ∀ c : L, Continuous (fun g : G => ((ρ g).val c : L)))

private def locusStabilizer (ρ : G →* ↥(isometricAutomorphisms K L))
    (U : Set (BanachSpectrum B)) : Subgroup G := by
  letI := coefficientSpectrumMulAction K L A
  exact (MulAction.stabilizer Γ U).comap ρ

include ρ hρ in
private theorem norm_displacement_eventually (b : B) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ g in 𝓝 (1 : G), ‖coefficientHom K L A (ρ g) b - b‖ < δ := by
  have hc : Continuous (fun g : G => ‖coefficientHom K L A (ρ g) b - b‖) :=
    ((show Continuous (fun g : G => coefficientHom K L A (ρ g) b) from
      continuous_coefficientOrbit K L A ρ hρ b).sub continuous_const).norm
  have h : ‖coefficientHom K L A (ρ 1) b - b‖ < δ := by
    simpa only [map_one, coefficientHom_one, BoundedAlgHom.id_apply, sub_self, norm_zero] using hδ
  exact hc.continuousAt.eventually (gt_mem_nhds h)

variable [IsTopologicalGroup G]

include ρ hρ in
private theorem isOpen_rationalStabilizer (d : RationalChart L B) :
    IsOpen (locusStabilizer K L A ρ d.locus : Set G) := by
  obtain ⟨ε, hε, hbound⟩ := d.exists_pos_le_denominator
  have hsmall : ∀ᶠ g in 𝓝 (1 : G),
      ‖coefficientHom K L A (ρ g) d.denominatorClass - d.denominatorClass‖ < ε ∧
      ∀ j, ‖coefficientHom K L A (ρ g) (d.numeratorClass j) - d.numeratorClass j‖ <
        d.radii j * ε :=
    (norm_displacement_eventually K L A ρ hρ d.denominatorClass hε).and
      (Filter.eventually_all.mpr (fun j => norm_displacement_eventually K L A ρ hρ
        (d.numeratorClass j) (mul_pos (d.radii.positive j) hε)))
  have hi : Tendsto (fun g : G => g⁻¹) (𝓝 (1 : G)) (𝓝 (1 : G)) := by
    simpa only [inv_one] using (continuous_inv.continuousAt (x := (1 : G))).tendsto
  apply Subgroup.isOpen_of_mem_nhds
  filter_upwards [hsmall, hi.eventually hsmall] with g hg hg'
  change (coefficientSpectrumMap K L A (ρ g)) '' d.locus = d.locus
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [map_inv] at hg'
    exact comap_mem_rational_locus K L A d hbound
      (coefficientHom K L A (ρ g)⁻¹).toBoundedRingHom hg'.1 hg'.2 hx
  · intro x hx
    let := coefficientSpectrumMulAction K L A
    refine ⟨(ρ g)⁻¹ • x, ?_, smul_inv_smul (ρ g) x⟩
    change BanachSpectrum.comap (coefficientHom K L A ((ρ g)⁻¹)⁻¹).toBoundedRingHom x ∈ d.locus
    rw [inv_inv]
    exact comap_mem_rational_locus K L A d hbound
      (coefficientHom K L A (ρ g)).toBoundedRingHom hg.1 hg.2 hx

/-- The full setwise stabilizer of a weighted rational chart is open for
norm-continuous scalar orbits. The coefficient action may be semilinear. -/
def rationalOpenStabilizer (d : RationalChart L B) : OpenSubgroup G :=
  ⟨locusStabilizer K L A ρ d.locus, isOpen_rationalStabilizer K L A ρ hρ d⟩

@[simp]
theorem mem_rationalOpenStabilizer (d : RationalChart L B) (g : G) :
    g ∈ rationalOpenStabilizer K L A ρ hρ d ↔
      coefficientSpectrumMap K L A (ρ g) '' d.locus = d.locus :=
  Iff.rfl

include ρ hρ in
private theorem isOpen_domainStabilizer (U : Domain L B) :
    IsOpen (locusStabilizer K L A ρ U.locus : Set G) := by
  obtain ⟨n, D, f, hcover⟩ := Domain.finiteRationalCover L B U
  have hU : U.locus = ⋃ j, (D j).locus := by
    apply Set.Subset.antisymm
    · intro x hx
      exact mem_iUnion.mpr (hcover x hx)
    · exact iUnion_subset fun j => (f j).subset
  have hsub : (⨅ j, (rationalOpenStabilizer K L A ρ hρ (D j)).toSubgroup) ≤
      locusStabilizer K L A ρ U.locus := by
    intro g hg
    rw [Subgroup.mem_iInf] at hg
    change coefficientSpectrumMap K L A (ρ g) '' U.locus = U.locus
    rw [hU, Set.image_iUnion]
    exact iUnion_congr fun j => (mem_rationalOpenStabilizer K L A ρ hρ (D j) g).mp (hg j)
  let H := OpenSubgroup.iInfOfFinite (fun j => rationalOpenStabilizer K L A ρ hρ (D j))
  exact (locusStabilizer K L A ρ U.locus).isOpen_of_mem_nhds <|
    Filter.mem_of_superset (H.isOpen.mem_nhds H.one_mem) hsub

/-- The full setwise stabilizer of any represented affinoid domain in an
extended affinoid algebra is open for norm-continuous scalar orbits. -/
def domainOpenStabilizer (U : Domain L B) : OpenSubgroup G :=
  ⟨locusStabilizer K L A ρ U.locus, isOpen_domainStabilizer K L A ρ hρ U⟩

@[simp]
theorem mem_domainOpenStabilizer (U : Domain L B) (g : G) :
    g ∈ domainOpenStabilizer K L A ρ hρ U ↔
      coefficientSpectrumMap K L A (ρ g) '' U.locus = U.locus :=
  Iff.rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
