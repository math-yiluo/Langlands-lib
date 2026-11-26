import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionCoefficientAction
import Langlands.Geometry.Analytic.GroundFieldExtensionAtlas
import Langlands.Geometry.Analytic.Spectrum.JointContinuityProof

/-! # The coefficient action on the scalar-extended analytic atlas -/

noncomputable section

universe u u' v w z

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open Set Topology PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

local notation "C" => chartSystem K L a
local notation "Γ" => isometricAutomorphisms K L

/-- Inverse pullback by the coefficient automorphism of an extended chart. -/
def coefficientChartAction (σ : Γ) (i : a.Index) :
    BanachSpectrum ((C).algebra i) → BanachSpectrum ((C).algebra i) :=
  BanachSpectrum.comap (coefficientHom K L (a.algebra i) σ⁻¹).toBoundedRingHom

@[simp] theorem coefficientChartAction_one (i : a.Index) (x : BanachSpectrum ((C).algebra i)) :
    coefficientChartAction K L a 1 i x = x := by
  apply BanachSpectrum.ext
  intro b
  change x (coefficientHom K L (a.algebra i) ((1 : Γ)⁻¹) b) = x b
  rw [inv_one, coefficientHom_one, BoundedAlgHom.id_apply]

theorem coefficientChartAction_mul (σ τ : Γ) (i : a.Index) (x : BanachSpectrum ((C).algebra i)) :
    coefficientChartAction K L a (σ * τ) i x =
      coefficientChartAction K L a σ i (coefficientChartAction K L a τ i x) := by
  apply BanachSpectrum.ext
  intro b
  change x (coefficientHom K L (a.algebra i) (σ * τ)⁻¹ b) =
    x (coefficientHom K L (a.algebra i) τ⁻¹ (coefficientHom K L (a.algebra i) σ⁻¹ b))
  rw [mul_inv_rev, coefficientHom_mul, BoundedAlgHom.comp_apply]

theorem coefficientChartAction_pull (σ : Γ) {i j : a.Index} (h : (C).Sub i j)
    (x : BanachSpectrum ((C).algebra i)) :
    coefficientChartAction K L a σ j ((C).pull h x) =
      (C).pull h (coefficientChartAction K L a σ i x) := by
  apply BanachSpectrum.ext
  intro b
  exact congrArg (fun f : BoundedAlgHom K ((C).algebra j) ((C).algebra i) => x (f b))
    (coefficientHom_natural K L σ⁻¹ (a.restriction i j h))

/-- The coefficient action descends along the actual gluing relation. -/
def coefficientPointMap (σ : Γ) : (C).Space → (C).Space :=
  Quotient.lift (fun x => (C).chart x.1 (coefficientChartAction K L a σ x.1 x.2)) (by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, hki, hkj, s, hsi, hsj⟩
    apply (C).chart_eq_iff.mpr
    refine ⟨k, hki, hkj, coefficientChartAction K L a σ k s, ?_, ?_⟩
    · rw [← coefficientChartAction_pull, hsi]
    · rw [← coefficientChartAction_pull, hsj])

@[simp] theorem coefficientPointMap_chart (σ : Γ) (i : a.Index) (x : BanachSpectrum ((C).algebra i)) :
    coefficientPointMap K L a σ ((C).chart i x) = (C).chart i (coefficientChartAction K L a σ i x) :=
  rfl

@[simp] theorem projection_coefficientPointMap (σ : Γ) (x : (C).Space) :
    projection K L a (coefficientPointMap K L a σ x) = projection K L a x := by
  obtain ⟨i, t, rfl⟩ := (C).exists_chart x
  rw [coefficientPointMap_chart, projection_chart, projection_chart]
  congr 1
  apply BanachSpectrum.ext
  intro b
  change t (coefficientHom K L (a.algebra i) σ⁻¹ (iota K L (a.algebra i) b)) =
    t (iota K L (a.algebra i) b)
  rw [coefficientHom_iota]

theorem coefficientPointMap_preimage_chart (σ : Γ) (i : a.Index) :
    coefficientPointMap K L a σ ⁻¹' range ((C).chart i) = range ((C).chart i) := by
  rw [range_chart]
  ext x
  exact Eq.to_iff (congrArg (· ∈ range (a.chart i)) (projection_coefficientPointMap K L a σ x))

variable {G : Type z} [Group G]

/-- A homomorphism into the isometric coefficient automorphisms acts on the
glued scalar extension, with its semilinear pullbacks on every chart. -/
@[instance_reducible]
def coefficientMulAction (σ : G →* Γ) : MulAction G (C).Space where
  smul g x := coefficientPointMap K L a (σ g) x
  one_smul x := by
    obtain ⟨i, t, rfl⟩ := (C).exists_chart x
    change coefficientPointMap K L a (σ 1) ((C).chart i t) = (C).chart i t
    rw [map_one, coefficientPointMap_chart, coefficientChartAction_one]
  mul_smul g h x := by
    obtain ⟨i, t, rfl⟩ := (C).exists_chart x
    change coefficientPointMap K L a (σ (g * h)) ((C).chart i t) =
      coefficientPointMap K L a (σ g) (coefficientPointMap K L a (σ h) ((C).chart i t))
    rw [map_mul, coefficientPointMap_chart, coefficientChartAction_mul,
      coefficientPointMap_chart, coefficientPointMap_chart]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_coefficientChartAction (σ : G →* Γ)
    (hσ : ∀ c : L, Continuous (fun g : G => (σ g).val c)) (i : a.Index) :
    Continuous (fun p : G × BanachSpectrum ((C).algebra i) =>
      coefficientChartAction K L a (σ p.1) i p.2) := by
  unfold coefficientChartAction
  refine BanachSpectrum.continuous_comap_of_continuous_apply
    (fun g : G => (coefficientHom K L (a.algebra i) (σ g)⁻¹).toBoundedRingHom) ?_
  intro c
  apply ((continuous_coefficientOrbit K L (a.algebra i) σ hσ c).comp continuous_inv).congr
  intro g
  change coefficientHom K L (a.algebra i) (σ g⁻¹) c =
    coefficientHom K L (a.algebra i) (σ g)⁻¹ c
  rw [map_inv]

/-- Norm-continuous coefficient orbits give a jointly continuous action on
the extended space. The product quasinet reduces the check to the chart spectra. -/
theorem continuous_coefficientPointMap (σ : G →* Γ)
    (hσ : ∀ c : L, Continuous (fun g : G => (σ g).val c)) :
    Continuous (fun p : G × (C).Space => coefficientPointMap K L a (σ p.1) p.2) := by
  have hG : AtlasTopology.IsQuasinet ({univ} : Set (Set G)) :=
    AtlasTopology.isQuasinet_of_univ_mem (mem_singleton _)
  apply (hG.product (atlas K L a).isNet_chartFamily.1).continuous
  rintro _ ⟨U, hU, V, hV, rfl⟩
  obtain rfl : U = (univ : Set G) := mem_singleton_iff.mp hU
  obtain ⟨i, rfl⟩ := hV
  apply continuousOn_iff_continuous_domRestrict.mpr
  let e := ((atlas K L a).isEmbedding_chart i).toHomeomorph
  let f (p : ↥((univ : Set G) ×ˢ range ((C).chart i))) :
      G × BanachSpectrum ((C).algebra i) := (p.val.1, e.symm ⟨p.val.2, p.property.2⟩)
  have hf : Continuous f :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      (e.symm.continuous.comp ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  apply ((((C).continuous_chart i).comp (continuous_coefficientChartAction K L a σ hσ i)).comp hf).congr
  intro p
  have he : (C).chart i (e.symm ⟨p.val.2, p.property.2⟩) = p.val.2 :=
    congrArg Subtype.val (e.apply_symm_apply ⟨p.val.2, p.property.2⟩)
  change (C).chart i (coefficientChartAction K L a (σ p.val.1) i
    (e.symm ⟨p.val.2, p.property.2⟩)) = coefficientPointMap K L a (σ p.val.1) p.val.2
  exact (coefficientPointMap_chart K L a _ i _).symm.trans
    (congrArg (coefficientPointMap K L a (σ p.val.1)) he)

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension
