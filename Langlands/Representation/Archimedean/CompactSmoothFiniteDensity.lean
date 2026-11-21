import Langlands.Representation.Archimedean.CompactSmoothApproximation
import Langlands.Representation.CompactRepresentativeWeights
import Mathlib.MeasureTheory.Group.Integral

/-! # Density of finite compact orbits in the genuine derivative topology -/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set
open scoped Manifold ContDiff Topology

namespace Langlands.Archimedean.CompactSmoothFiniteDensity

open CompactSmoothAverage
open Langlands.CompactRepresentativeWeights FiniteVectors

universe u𝔤 uG uE uK uι

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  [FiniteDimensional ℝ 𝔤]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace 𝔤 G]
  [LieGroup 𝓘(ℝ, 𝔤) ∞ G]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {K : Type uK} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (π : G →* (E →L[ℂ] E)) (r : K →ₜ* G)
  (μ : Measure K) [IsFiniteMeasure μ]

/-- The original bounded action restricted along the compact homomorphism. -/
abbrev restrictedRepresentation : Representation ℂ K E :=
  (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp π).comp r.toMonoidHom

/-- The actual weighted averages of one smooth orbit, valued in its genuine
derivative topology. -/
def orbitWeightAverage (w : DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π) :
    C(K, ℂ) →ₗ[ℂ] DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π :=
  weightAverageLM π
    (v := fun g => π g (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w : E))
    μ r.toContinuousMap
    (contMDiff_orbit_family π (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w).property)

omit [IsTopologicalGroup K] in
@[simp]
theorem toSmooth_orbitWeightAverage (w : DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π)
    (a : C(K, ℂ)) :
    (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π (orbitWeightAverage π r μ w a) : E) =
      ∫ k, a k • π (r k) (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w : E) ∂μ :=
  rfl

/-- Left translation of a weight acts on its actual integral by the original
compact element. -/
theorem apply_orbitWeightAverage [μ.IsMulLeftInvariant]
    (w : DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π) (a : C(K, ℂ)) (h : K) :
    π (r h) (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π (orbitWeightAverage π r μ w a)) =
      (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π
        (orbitWeightAverage π r μ w (leftRegular h a)) : E) := by
  simp only [toSmooth_orbitWeightAverage]
  let v : E := DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w
  have hv : IsSmoothVector 𝓘(ℝ, 𝔤) π v :=
    (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w).property
  change π (r h) (∫ k, a k • π (r.toContinuousMap k) v ∂μ) =
    ∫ k, a (h⁻¹ * k) • π (r k) v ∂μ
  rw [apply_integral π (v := fun g => π g v) μ a r.toContinuousMap
    (contMDiff_orbit_family π hv) (r h)]
  change (∫ k, a k • π (r h) (π (r k) v) ∂μ) =
    ∫ k, a (h⁻¹ * k) • π (r k) v ∂μ
  rw [← integral_mul_left_eq_self (μ := μ) (fun k => a (h⁻¹ * k) • π (r k) v) h]
  simp only [inv_mul_cancel_left, map_mul, mul_apply_eq_comp]

/-- For a fixed smooth vector, its actual compact integral is an intertwiner
from the left regular scalar weights to the original ambient representation. -/
def orbitAverageIntertwiner [μ.IsMulLeftInvariant]
    (w : DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π) :
    (leftRegular (K := K)).IntertwiningMap (restrictedRepresentation π r) where
  toLinearMap := ((DerivativeSmoothVectors.derivativeCLM 𝓘(ℝ, 𝔤) π []).toLinearMap).comp
    (orbitWeightAverage π r μ w)
  isIntertwining' h := by
    apply LinearMap.ext
    intro a
    exact (apply_orbitWeightAverage π r μ w a h).symm

/-- A weight with finite left-translation orbit gives a vector with finite
compact orbit. -/
theorem isFiniteVector_orbitWeightAverage [μ.IsMulLeftInvariant]
    (w : DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π) {a : C(K, ℂ)}
    (ha : a ∈ finiteWeights) :
    IsFiniteVector (restrictedRepresentation π r)
      (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π (orbitWeightAverage π r μ w a) : E) :=
  (show IsFiniteVector leftRegular a from ha).map (orbitAverageIntertwiner π r μ w)

/-- Genuine smooth vectors with finite original compact orbit are dense in all
genuine smooth vectors for the full word-derivative topology. -/
theorem dense_finiteSmoothVectors [T2Space K] [μ.IsMulLeftInvariant]
    [μ.IsOpenPosMeasure] {ι : Type uι} [Fintype ι]
    (τ : Representation ℂ K (ι → ℂ)) (hτ : ∀ v, Continuous (fun k => τ k v))
    (hinj : Function.Injective τ) :
    Dense {w : DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π |
      IsFiniteVector (restrictedRepresentation π r)
        (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w : E)} := by
  intro w
  let S : Set C(K, ℂ) := (finiteWeights (K := K) : Set C(K, ℂ))
  have hS : Dense S := dense_finiteWeights τ hτ hinj
  have hw : w ∈ closure (orbitWeightAverage π r μ w '' S) := by
    have hr : r.toContinuousMap (1 : K) = 1 := r.map_one
    exact smoothVector_mem_closure_dense_orbitAverage π μ r.toContinuousMap 1 hr w hS
  apply closure_mono _ hw
  rintro _ ⟨a, ha, rfl⟩
  exact isFiniteVector_orbitWeightAverage π r μ w ha

end Langlands.Archimedean.CompactSmoothFiniteDensity

namespace Langlands.Archimedean

open CompactSmoothFiniteDensity

universe u𝔤 uG uE uK uι

/-- Compact-finite vectors are dense in the genuine derivative topology when
the compact group has a faithful continuous representation on a finite
complex coordinate space. -/
def CompactSmoothFiniteDensityStatement : Prop :=
  ∀ (𝔤 : Type u𝔤) [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [FiniteDimensional ℝ 𝔤]
    (G : Type uG) [Group G] [TopologicalSpace G] [ChartedSpace 𝔤 G]
    [LieGroup 𝓘(ℝ, 𝔤) ∞ G]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : Type uK) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (π : G →* (E →L[ℂ] E)) (r : K →ₜ* G) (μ : Measure K)
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure]
    (ι : Type uι) [Fintype ι] (τ : Representation ℂ K (ι → ℂ)),
    (∀ v, Continuous (fun k => τ k v)) → Function.Injective τ →
      Dense {w : DerivativeSmoothVectors 𝓘(ℝ, 𝔤) π |
        FiniteVectors.IsFiniteVector (restrictedRepresentation π r)
          (DerivativeSmoothVectors.toSmooth 𝓘(ℝ, 𝔤) π w : E)}

theorem compactSmoothFiniteDensity : CompactSmoothFiniteDensityStatement.{u𝔤,uG,uE,uK,uι} := by
  intro 𝔤 _ _ _ G _ _ _ _ E _ _ _ K _ _ _ _ _ _ _ π r μ _ _ _ ι _ τ hτ hinj
  exact dense_finiteSmoothVectors π r μ τ hτ hinj

end Langlands.Archimedean
