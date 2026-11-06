import Langlands.GroupScheme.AlgebraicallyClosedComponents
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Separation.Basic

/-! # The finite coefficient image on actual scheme components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

variable {k : Type u} [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k)))

/-- The inherited quotient topology on actual scheme components. -/
instance allComponentTopologicalSpace : TopologicalSpace (AlgebraicallyClosedComponents H) :=
  inferInstanceAs (TopologicalSpace (_root_.ConnectedComponents H.X.left))

/-- The actual quotient topology on the space of scheme components is T1. -/
instance allComponentT1Space : T1Space (AlgebraicallyClosedComponents H) where
  t1 c := by
    obtain ⟨p, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    apply _root_.ConnectedComponents.isQuotientMap_coe.isCoinducing.isClosed_preimage.mp
    change IsClosed
      ((_root_.ConnectedComponents.mk : H.X.left → _root_.ConnectedComponents H.X.left) ⁻¹'
        {_root_.ConnectedComponents.mk p})
    rw [connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent

variable [IsAlgClosed k] [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- Finiteness makes the existing quotient topology discrete. -/
instance allComponentDiscreteTopology : DiscreteTopology (AlgebraicallyClosedComponents H) :=
  Finite.instDiscreteTopology

/-- A chosen actual rational section representing a component. -/
def componentPointRepresentative (c : AlgebraicallyClosedComponents H) : rationalPoints H :=
  Classical.choose (allComponentOfPoint_surjective H c)

@[simp]
theorem pointComponent_representative (c : AlgebraicallyClosedComponents H) :
    pointComponent H (componentPointRepresentative H c) = c :=
  Classical.choose_spec (allComponentOfPoint_surjective H c)

end Langlands.GroupScheme.IdentityComponent

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [IsAlgClosed L]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- Coefficient automorphisms acting trivially on every actual component. -/
def componentGaloisKernel : Subgroup (L ≃ₐ[k] L) :=
  (allComponentGaloisAction k L H).ker

instance componentGaloisKernel_normal : (componentGaloisKernel k L H).Normal :=
  inferInstanceAs (allComponentGaloisAction k L H).ker.Normal

/-- The kernel is detected by the actual semilinear scheme-component maps. -/
theorem mem_componentGaloisKernel_iff (σ : L ≃ₐ[k] L) :
    σ ∈ componentGaloisKernel k L H ↔
      ∀ c : AlgebraicallyClosedComponents (baseChanged k L H),
        coefficientComponents k L H σ c = c := by
  change allComponentGaloisAction k L H σ = 1 ↔ _
  constructor
  · intro h c
    have hc := congrArg
      (fun a : MulAut (AlgebraicallyClosedComponents (baseChanged k L H)) => a c) h
    change allComponentConjugate k L H σ c = c at hc
    rwa [allComponentConjugate_apply] at hc
  · intro h
    ext c
    change allComponentConjugate k L H σ c = c
    rw [allComponentConjugate_apply]
    exact h c

/-- Kernel membership can be checked on a finite family of chosen actual sections,
indexed by all components. Only equality of components is required. -/
theorem mem_componentGaloisKernel_iff_representatives (σ : L ≃ₐ[k] L) :
    σ ∈ componentGaloisKernel k L H ↔
      ∀ c : AlgebraicallyClosedComponents (baseChanged k L H),
        pointComponent (baseChanged k L H)
          (rationalConjugate k L H σ
            (componentPointRepresentative (baseChanged k L H) c)) = c := by
  rw [mem_componentGaloisKernel_iff]
  constructor
  · intro h c
    rw [← coefficientComponents_pointComponent, pointComponent_representative]
    exact h c
  · intro h c
    rw [← pointComponent_representative (baseChanged k L H) c,
      coefficientComponents_pointComponent]
    simpa only [pointComponent_representative] using h c

/-- The actual image of coefficient automorphisms in component-group automorphisms. -/
def ComponentGaloisImage :=
  (allComponentGaloisAction k L H).range

instance : Group (ComponentGaloisImage k L H) :=
  inferInstanceAs (Group (allComponentGaloisAction k L H).range)

instance : Finite (ComponentGaloisImage k L H) :=
  Finite.of_injective
    (fun a : ComponentGaloisImage k L H =>
      fun c : AlgebraicallyClosedComponents (baseChanged k L H) => a.val c)
    (by
      intro a b h
      apply Subtype.ext
      ext c
      exact congrFun h c)

/-- The finite image is equipped with the discrete topology. -/
instance : TopologicalSpace (ComponentGaloisImage k L H) := ⊥

instance : DiscreteTopology (ComponentGaloisImage k L H) := ⟨rfl⟩

/-- The canonical surjection onto the finite effective coefficient image. -/
def componentGaloisProjection : (L ≃ₐ[k] L) →* ComponentGaloisImage k L H :=
  (allComponentGaloisAction k L H).rangeRestrict

theorem componentGaloisProjection_surjective :
    Function.Surjective (componentGaloisProjection k L H) := by
  rintro ⟨a, σ, hσ⟩
  exact ⟨σ, Subtype.ext hσ⟩

/-- The finite image acts faithfully by automorphisms of all actual components. -/
def componentGaloisImageAction : ComponentGaloisImage k L H →*
    MulAut (AlgebraicallyClosedComponents (baseChanged k L H)) :=
  (allComponentGaloisAction k L H).range.subtype

theorem componentGaloisImageAction_injective :
    Function.Injective (componentGaloisImageAction k L H) :=
  Subtype.val_injective

@[simp]
theorem componentGaloisImageAction_projection (σ : L ≃ₐ[k] L) :
    componentGaloisImageAction k L H (componentGaloisProjection k L H σ) =
      allComponentGaloisAction k L H σ := rfl

/-- Factoring through the image preserves the actual semilinear component maps. -/
theorem componentGaloisImageAction_projection_apply (σ : L ≃ₐ[k] L)
    (c : AlgebraicallyClosedComponents (baseChanged k L H)) :
    componentGaloisImageAction k L H (componentGaloisProjection k L H σ) c =
      coefficientComponents k L H σ c :=
  allComponentConjugate_apply k L H σ c

/-- The ordinary automorphism-group quotient by the action kernel is its finite image. -/
def componentGaloisQuotientEquiv :
    (L ≃ₐ[k] L) ⧸ componentGaloisKernel k L H ≃* ComponentGaloisImage k L H :=
  QuotientGroup.quotientKerEquivRange (allComponentGaloisAction k L H)

@[simp]
theorem componentGaloisQuotientEquiv_mk (σ : L ≃ₐ[k] L) :
    componentGaloisQuotientEquiv k L H (QuotientGroup.mk σ) =
      componentGaloisProjection k L H σ := rfl

instance : Finite ((L ≃ₐ[k] L) ⧸ componentGaloisKernel k L H) :=
  Finite.of_equiv (ComponentGaloisImage k L H)
    (componentGaloisQuotientEquiv k L H).symm.toEquiv

instance componentGaloisKernel_finiteIndex : (componentGaloisKernel k L H).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

/-- The faithful action of the ordinary finite quotient. -/
def componentGaloisQuotientAction :
    ((L ≃ₐ[k] L) ⧸ componentGaloisKernel k L H) →*
      MulAut (AlgebraicallyClosedComponents (baseChanged k L H)) :=
  (componentGaloisImageAction k L H).comp
    (componentGaloisQuotientEquiv k L H).toMonoidHom

theorem componentGaloisQuotientAction_injective :
    Function.Injective (componentGaloisQuotientAction k L H) :=
  (componentGaloisImageAction_injective k L H).comp
    (componentGaloisQuotientEquiv k L H).injective

@[simp]
theorem componentGaloisQuotientAction_mk (σ : L ≃ₐ[k] L) :
    componentGaloisQuotientAction k L H (QuotientGroup.mk σ) =
      allComponentGaloisAction k L H σ := rfl

/-- The full coefficient fixed subgroup is also the fixed subgroup for the finite image. -/
theorem mem_allComponentFixedSubgroup_iff_image
    (c : AlgebraicallyClosedComponents (baseChanged k L H)) :
    c ∈ allComponentFixedSubgroup k L H ↔
      ∀ a : ComponentGaloisImage k L H, componentGaloisImageAction k L H a c = c := by
  constructor
  · intro h a
    obtain ⟨σ, rfl⟩ := componentGaloisProjection_surjective k L H a
    exact h σ
  · intro h σ
    exact h (componentGaloisProjection k L H σ)

end Langlands.GroupScheme.IdentityComponent
