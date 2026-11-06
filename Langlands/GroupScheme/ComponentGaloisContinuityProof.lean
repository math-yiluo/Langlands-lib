import Langlands.GroupScheme.ComponentGaloisContinuityStatement
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily

/-! # Finite fixing fields and Krull continuity on actual components -/

noncomputable section

universe u

open AlgebraicGeometry
open scoped Topology CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison
open Langlands.AlgebraicGeometry.PointTopology

/-- A finite family of points of a finite-type algebra is fixed over one finite
intermediate field of an algebraic coefficient extension. -/
theorem exists_finite_fixing_algHoms
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    {A : Type u} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    {Index : Type u} [Finite Index] (p : Index → A →ₐ[k] L) :
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      ∀ σ ∈ E.fixingSubgroup, ∀ i, σ.toAlgHom.comp (p i) = p i := by
  classical
  let := Fintype.ofFinite Index
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := k) (A := A)
  let t : Finset L := Finset.univ.biUnion fun i => s.image (p i)
  let E : IntermediateField k L := IntermediateField.adjoin k (t : Set L)
  refine ⟨E, IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral (R := k) x), ?_⟩
  intro σ hσ i
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro a ha
  apply (IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ
  apply IntermediateField.subset_adjoin
  exact Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [IsAlgClosed L] [Algebra.IsAlgebraic k L]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- A finite field constructed from the coordinates of the actual component
representatives has fixing subgroup contained in the actual action kernel. -/
theorem exists_finite_component_fixing_field :
    ∃ E : IntermediateField k L,
      FiniteDimensional k E ∧ E.fixingSubgroup ≤ componentGaloisKernel k L H := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let p := fun c : AlgebraicallyClosedComponents (baseChanged k L H) =>
    GaloisPoint.coordinates k H L
      (baseChangeCoeffEquiv k L H (componentPointRepresentative (baseChanged k L H) c))
  obtain ⟨E, hE, hfix⟩ := exists_finite_fixing_algHoms k L p
  refine ⟨E, hE, ?_⟩
  intro σ hσ
  apply (mem_componentGaloisKernel_iff_representatives k L H σ).mpr
  intro c
  have hpoint : rationalConjugate k L H σ
      (componentPointRepresentative (baseChanged k L H) c) =
        componentPointRepresentative (baseChanged k L H) c := by
    apply (baseChangeCoeffEquiv k L H).injective
    rw [baseChangeCoeffEquiv_rationalConjugate]
    apply (GaloisPoint.coordinates k H L).injective
    ext a
    rw [GaloisPoint.coordinates_conjugate]
    exact DFunLike.congr_fun (hfix σ hσ c) a
  rw [hpoint, pointComponent_representative]

/-- The original component action has open kernel in Mathlib's Krull topology. -/
theorem componentGaloisKernel_isOpen :
    IsOpen (componentGaloisKernel k L H : Set (L ≃ₐ[k] L)) := by
  obtain ⟨E, hE, hle⟩ := exists_finite_component_fixing_field k L H
  let := hE
  exact Subgroup.isOpen_mono hle E.fixingSubgroup_isOpen

/-- The canonical homomorphism onto the finite effective image is continuous. -/
theorem componentGaloisProjection_continuous :
    Continuous (componentGaloisProjection k L H) := by
  apply continuous_of_tendsto_nhds_one (componentGaloisProjection k L H)
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [(componentGaloisKernel_isOpen k L H).mem_nhds
    (componentGaloisKernel k L H).one_mem] with σ hσ
  apply Subtype.ext
  exact hσ

/-- Joint continuity retains the actual connected-component quotient topology. -/
theorem allComponentGaloisAction_continuous :
    Continuous (fun p : (L ≃ₐ[k] L) × AlgebraicallyClosedComponents (baseChanged k L H) =>
      allComponentGaloisAction k L H p.1 p.2) := by
  have heval : Continuous
      (fun p : ComponentGaloisImage k L H × AlgebraicallyClosedComponents (baseChanged k L H) =>
        componentGaloisImageAction k L H p.1 p.2) := continuous_of_discreteTopology
  exact heval.comp ((componentGaloisProjection_continuous k L H).prodMap continuous_id)

/-- The exact published finite-fixing-field and Krull-continuity target. -/
theorem componentGaloisKrullContinuity_proof : ComponentGaloisKrullContinuityStatement.{u} := by
  intro k L _ _ _ _ _ H _ _
  exact ⟨exists_finite_component_fixing_field k L H,
    componentGaloisKernel_isOpen k L H,
    componentGaloisProjection_continuous k L H,
    allComponentGaloisAction_continuous k L H⟩

end Langlands.GroupScheme.IdentityComponent
