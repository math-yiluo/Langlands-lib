import Langlands.Geometry.Building.BoundedRootFixerFiltration
import Mathlib.Topology.Order.OrderClosed

/-! # Root-fixer depths for affine-closure-ordered subsets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- The initial topology of real affine functionals on supplied KP apartment
data, without requiring a local-field building presentation. -/
@[instance_reducible] def affineFunctionalTopology : TopologicalSpace D.Apartment :=
  ⨅ f : D.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance

/-- If a nonempty subset lies in the initial affine closure of another subset,
the latter is nonempty too. -/
theorem nonempty_of_nonempty_subset_affineClosure {Ω Ω' : Set D.Apartment}
    (hne : Ω.Nonempty)
    (hsub : Ω ⊆ @closure D.Apartment
      (⨅ f : D.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) Ω') :
    Ω'.Nonempty := by
  let := D.affineFunctionalTopology
  exact (hne.mono hsub).of_closure

/-- An affine functional bounded above on `Ω'` remains bounded above on every
subset of its initial affine closure. -/
theorem bddAbove_affineImage_of_subset_affineClosure {Ω Ω' : Set D.Apartment}
    (f : D.Apartment →ᵃ[ℝ] ℝ) (hb : BddAbove (f '' Ω'))
    (hsub : Ω ⊆ @closure D.Apartment
      (⨅ f : D.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) Ω') :
    BddAbove (f '' Ω) := by
  let := D.affineFunctionalTopology
  have hf : Continuous f := continuous_iff_le_induced.mpr (iInf_le _ f)
  exact hb.closure.mono
    ((Set.image_mono hsub).trans (image_closure_subset_closure_image hf))

/-- Root-fixer depths increase when the subset increases up to initial affine
closure. Only the particular root threshold needs an upper bound. -/
theorem rootFixerDepth_le_of_subset_affineClosure (a : relativeRoots i)
    (x : D.Apartment) {Ω Ω' : Set D.Apartment} (hne : Ω.Nonempty)
    (hb : BddAbove ((fun y => -D.affineFunctional a x 0 y) '' Ω'))
    (hsub : Ω ⊆ @closure D.Apartment
      (⨅ f : D.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) Ω') :
    D.rootFixerDepth a x Ω ≤ D.rootFixerDepth a x Ω' := by
  let := D.affineFunctionalTopology
  have hf : Continuous (-D.affineFunctional a x 0) :=
    continuous_iff_le_induced.mpr (iInf_le _ (-D.affineFunctional a x 0))
  have hub : D.rootFixerDepth a x Ω' ∈
      upperBounds ((fun y => -D.affineFunctional a x 0 y) '' Ω') :=
    fun _ hy => le_csSup hb hy
  rw [← upperBounds_closure] at hub
  apply csSup_le (hne.image _)
  intro z hz
  exact hub (((Set.image_mono hsub).trans
    (image_closure_subset_closure_image hf)) hz)

/-- The closure ordering reverses the inclusion of actual root fixers on
nonempty affine-bounded subsets. -/
theorem rootFixer_le_of_subset_affineClosure (a : relativeRoots i)
    (x : D.Apartment) {Ω Ω' : Set D.Apartment} (hne : Ω.Nonempty)
    (hb : ∀ f : D.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω'))
    (hsub : Ω ⊆ @closure D.Apartment
      (⨅ f : D.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) Ω') :
    D.rootFixer a Ω' ≤ D.rootFixer a Ω := by
  have hne' := D.nonempty_of_nonempty_subset_affineClosure hne hsub
  have hbΩ : ∀ f : D.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω) :=
    fun f => D.bddAbove_affineImage_of_subset_affineClosure f (hb f) hsub
  rw [D.rootFixer_eq_filtration_of_bounded a x hne' hb,
    D.rootFixer_eq_filtration_of_bounded a x hne hbΩ]
  exact D.filtration_antitone x a
    (D.rootFixerDepth_le_of_subset_affineClosure a x hne
      (hb (-D.affineFunctional a x 0)) hsub)

end Langlands.Geometry.Building.KPApartmentData
