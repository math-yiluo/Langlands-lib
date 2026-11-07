import Langlands.AlgebraicGeometry.LocallyNoetherianComponentSchemes
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.Topology.Compactness.Compact

/-! # Smooth restrictions over the actual connected components of the target -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Langlands.AlgebraicGeometry

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]

/-- The actual inverse image of a target component, with its open subscheme
structure rather than a reduced or affine replacement. -/
def componentPreimageOpen (f : X ⟶ Y) (c : ConnectedComponents Y) : X.Opens :=
  f ⁻¹ᵁ componentOpen Y c

@[simp] theorem mem_componentPreimageOpen (f : X ⟶ Y)
    (c : ConnectedComponents Y) (x : X) :
    x ∈ componentPreimageOpen f c ↔ ConnectedComponents.mk (f x) = c :=
  Iff.rfl

/-- The actual source scheme over a target component. -/
abbrev componentPreimageScheme (f : X ⟶ Y) (c : ConnectedComponents Y) : Scheme.{u} :=
  (componentPreimageOpen f c).toScheme

/-- The inclusion of the actual source restriction. -/
abbrev componentPreimageι (f : X ⟶ Y) (c : ConnectedComponents Y) :
    componentPreimageScheme f c ⟶ X :=
  (componentPreimageOpen f c).ι

/-- Restrict an actual scheme map to a connected component of its target. -/
def targetComponentRestriction (f : X ⟶ Y) (c : ConnectedComponents Y) :
    componentPreimageScheme f c ⟶ componentScheme Y c :=
  f ∣_ componentOpen Y c

@[reassoc (attr := simp)]
theorem targetComponentRestriction_ι (f : X ⟶ Y) (c : ConnectedComponents Y) :
    targetComponentRestriction f c ≫ componentι Y c = componentPreimageι f c ≫ f :=
  morphismRestrict_ι f (componentOpen Y c)

/-- The restriction square is an actual scheme pullback. -/
theorem targetComponentRestriction_isPullback (f : X ⟶ Y)
    (c : ConnectedComponents Y) :
    IsPullback (targetComponentRestriction f c) (componentPreimageι f c)
      (componentι Y c) f :=
  isPullback_morphismRestrict f (componentOpen Y c)

theorem componentPreimageOpen_disjoint (f : X ⟶ Y)
    {c d : ConnectedComponents Y} (h : c ≠ d) :
    Disjoint (componentPreimageOpen f c) (componentPreimageOpen f d) := by
  apply disjoint_iff_inf_le.mpr
  intro x hx
  exact h (hx.1.symm.trans hx.2)

theorem componentPreimageOpen_iSup (f : X ⟶ Y) :
    ⨆ c, componentPreimageOpen f c = ⊤ := by
  apply Opens.ext
  simp only [Opens.coe_iSup, Opens.coe_top, Set.iUnion_eq_univ_iff]
  intro x
  exact ⟨ConnectedComponents.mk (f x), rfl⟩

/-- The actual source open cover paired with `componentOpenCover Y`. -/
def componentPreimageOpenCover (f : X ⟶ Y) : X.OpenCover where
  I₀ := ConnectedComponents Y
  X := componentPreimageScheme f
  f := componentPreimageι f
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    exact ⟨ConnectedComponents.mk (f x), ⟨x, rfl⟩, rfl⟩

/-- Compactness makes the actual component index finite. No nonemptiness
assumption is needed. -/
theorem finite_componentIndex_of_compact [CompactSpace Y] :
    Finite (ConnectedComponents Y) := by
  let : DiscreteTopology (ConnectedComponents Y) :=
    discreteTopology_iff_isOpen_singleton.mpr fun c => by
      rw [← ConnectedComponents.isQuotientMap_coe.isOpen_preimage]
      exact (componentOpen Y c).isOpen
  exact finite_of_compact_of_discrete

instance targetComponentRestriction_smooth (f : X ⟶ Y) [Smooth f]
    (c : ConnectedComponents Y) : Smooth (targetComponentRestriction f c) :=
  MorphismProperty.of_isPullback (targetComponentRestriction_isPullback f c).flip
    (inferInstance : Smooth f)

instance targetComponentRestriction_geometricallyConnected (f : X ⟶ Y)
    [GeometricallyConnected f] (c : ConnectedComponents Y) :
    GeometricallyConnected (targetComponentRestriction f c) :=
  inferInstanceAs (GeometricallyConnected (f ∣_ componentOpen Y c))

/-- Smooth openness and geometric connectedness make every actual source
restriction connected and nonempty. -/
instance componentPreimageScheme_connected (f : X ⟶ Y) [Smooth f]
    [GeometricallyConnected f] (c : ConnectedComponents Y) :
    ConnectedSpace (componentPreimageScheme f c) :=
  GeometricallyConnected.connectedSpace (targetComponentRestriction f c)
    (targetComponentRestriction f c).isOpenMap

/-- Select one standard-smooth chart dimension for each actual target component.
The dimensions may vary between components. -/
def smoothTargetComponentDimensions (f : X ⟶ Y) [Smooth f]
    [GeometricallyConnected f] : ConnectedComponents Y → ℕ :=
  fun c => Classical.choose
    (smoothConnectedRelativeDimension
      (componentPreimageScheme f c) (componentScheme Y c)
      (targetComponentRestriction f c) inferInstance inferInstance)

/-- Each selected dimension is realized by the actual restricted morphism. -/
theorem smoothTargetComponentDimensions_spec (f : X ⟶ Y) [Smooth f]
    [GeometricallyConnected f] (c : ConnectedComponents Y) :
    SmoothOfRelativeDimension (smoothTargetComponentDimensions f c)
      (targetComponentRestriction f c) :=
  Classical.choose_spec
    (smoothConnectedRelativeDimension
      (componentPreimageScheme f c) (componentScheme Y c)
      (targetComponentRestriction f c) inferInstance inferInstance)

end Langlands.AlgebraicGeometry
