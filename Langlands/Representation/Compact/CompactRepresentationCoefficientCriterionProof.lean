import Langlands.Representation.Compact.CompactRepresentationCriterionStatements
import Langlands.Representation.CompactCoefficient.FixedVectorsFiniteDimensional
import Langlands.Representation.Hecke.CommonInvarianceProof
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Compact support of smooth coefficients and projected orbits -/

noncomputable section
universe u v

namespace Langlands.Renard.CompactRepresentation

open MeasureTheory CompactCoefficientClass

section ProjectedOrbit

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hs : IsSmooth ρ)
  (hc : HasCompactSmoothDualCoefficients ρ)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

include μ hs hc hK in
/-- The projected orbit of any vector spans a finite-dimensional space. -/
theorem finiteDimensional_span_projectedOrbit (x : V) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun g : G => Hecke.fixedProjection μ ρ hs K hK (ρ g x))) := by
  classical
  let P := Hecke.fixedProjection μ ρ hs K hK
  let u : G → fixedVectors ρ K.toSubgroup := fun g => P (ρ g x)
  obtain ⟨b, hbu, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range u)
  have hbind : LinearIndepOn ℂ id b := by
    simpa only [Subtype.range_coe] using hbli.linearIndepOn_id
  let B := Module.Basis.extend hbind
  let Λ := fixedExtension μ ρ hs K hK B.sumCoords
  have hΛ : IsSmoothVector ρ.dual Λ := fixedExtension_isSmoothVector μ ρ hs K hK _
  have hcoef (g : G) : matrixCoefficient ρ Λ x g = B.sumCoords (u g) :=
    fixedExtension_apply μ ρ hs K hK _ _
  have hu : IsLocallyConstant u := (Hecke.orbitMap_locallyConstant ρ (hs x)).comp P
  let : TopologicalSpace (fixedVectors ρ K.toSubgroup) := ⊥
  let : DiscreteTopology (fixedVectors ρ K.toSubgroup) := ⟨rfl⟩
  have hfin : (u '' tsupport (matrixCoefficient ρ Λ x)).Finite :=
    ((hc x Λ hΛ).isCompact.image hu.continuous).finite_of_discrete
  have hbfin : b.Finite := by
    refine hfin.subset fun y hy => ?_
    obtain ⟨g, rfl⟩ := hbu hy
    refine ⟨g, subset_tsupport _ ?_, rfl⟩
    rw [Function.mem_support, hcoef]
    have hyB : u g ∈ hbind.extend (Set.subset_univ b) :=
      hbind.subset_extend _ hy
    have hB : B ⟨u g, hyB⟩ = u g := Module.Basis.extend_apply_self hbind _
    rw [← hB, B.sumCoords_self_apply]
    exact one_ne_zero
  rw [← hbspan]
  exact FiniteDimensional.span_of_finite ℂ hbfin

include μ hs hc hK in
/-- Compact smooth-dual coefficients give compact support of each projected orbit. -/
theorem hasCompactSupport_projectedOrbit (x : V) :
    HasCompactSupport (fun g : G => Hecke.fixedProjection μ ρ hs K hK (ρ g x)) := by
  classical
  let P := Hecke.fixedProjection μ ρ hs K hK
  let u : G → fixedVectors ρ K.toSubgroup := fun g => P (ρ g x)
  let E := Submodule.span ℂ (Set.range u)
  let := finiteDimensional_span_projectedOrbit μ ρ hs hc K hK x
  let B := Module.finBasis ℂ E
  let Λ := fun i => fixedExtension μ ρ hs K hK (Subspace.dualLift E (B.coord i))
  let C := fun i => matrixCoefficient ρ (Λ i) x
  have hC (i) : HasCompactSupport (C i) :=
    hc x (Λ i) (fixedExtension_isSmoothVector μ ρ hs K hK _)
  have hcoord (i) (g : G) : C i g =
      B.repr (⟨u g, Submodule.subset_span ⟨g, rfl⟩⟩ : E) i := by
    rw [show C i g = (Subspace.dualLift E (B.coord i)) (u g) from
      fixedExtension_apply μ ρ hs K hK _ _]
    exact Subspace.dualLift_of_mem (W := E) (φ := B.coord i)
      (show u g ∈ E from Submodule.subset_span ⟨g, rfl⟩)
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_iUnion fun i => (hC i).isCompact)
  intro g hg
  by_contra hn
  have hzero : (⟨u g, Submodule.subset_span ⟨g, rfl⟩⟩ : E) = 0 := by
    apply B.repr.injective
    apply Finsupp.ext
    intro i
    rw [map_zero, Finsupp.zero_apply, ← hcoord]
    exact image_eq_zero_of_notMem_tsupport (fun hi => hn (Set.mem_iUnion.mpr ⟨i, hi⟩))
  exact hg (congrArg Subtype.val hzero)

end ProjectedOrbit

/-- Renard IV.1.3, Theorem, for the published Haar-normalized fixed projection. -/
theorem compactRepresentationCoefficientCriterion :
    CompactRepresentationCoefficientCriterionStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ μ _ π
  constructor
  · intro hprojected x ℓ hℓ
    obtain ⟨L, hL⟩ := hℓ
    obtain ⟨K, hKL, hK, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ L
    have hinv : ∀ k ∈ K, ∀ y : π, ℓ (π.representation k y) = ℓ y := by
      intro k hk y
      have heq := congrArg (fun f : Module.Dual ℂ π => f y)
        (hL ⟨k⁻¹, hKL (K.inv_mem hk)⟩)
      change ℓ (π.representation (k⁻¹)⁻¹ y) = ℓ y at heq
      simpa only [inv_inv] using heq
    have hpositive : HasCompactSupport (fun g : G =>
        Hecke.fixedProjection μ π.representation π.isSmooth K hK (π.representation g x)) := by
      have hcomp := (hprojected K hK x).comp_homeomorph (Homeomorph.inv G)
      change HasCompactSupport (fun g : G => Hecke.fixedProjection μ π.representation
        π.isSmooth K hK (π.representation (g⁻¹)⁻¹ x)) at hcomp
      simpa only [inv_inv] using hcomp
    have hscalar := hpositive.comp_left
      (g := fun y : fixedVectors π.representation K.toSubgroup => ℓ y.val) (by simp)
    have heq : (fun y : fixedVectors π.representation K.toSubgroup => ℓ y.val) ∘
        (fun g : G => Hecke.fixedProjection μ π.representation π.isSmooth K hK
          (π.representation g x)) = matrixCoefficient π.representation ℓ x := by
      funext g
      exact apply_heckeAction_normalizedIndicator μ π.representation π.isSmooth K hK hinv _
    rw [heq] at hscalar
    exact hscalar
  · intro hc K hK x
    exact
      (hasCompactSupport_projectedOrbit μ π.representation π.isSmooth hc K hK x).comp_homeomorph
        (Homeomorph.inv G)

end Langlands.Renard.CompactRepresentation
