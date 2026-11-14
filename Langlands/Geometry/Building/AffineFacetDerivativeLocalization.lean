import Langlands.Geometry.Building.AffineFacetSignSupport
import Langlands.Geometry.Building.AffineFacetRootCount
import Langlands.Geometry.Building.AffineChamberCartanMarks

/-! # Incident facets in the actual derivative arrangement -/

noncomputable section

universe u v

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V : Type u} {A : Type v}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} {x : A}

/-- View the given actual linear forms as affine maps on the vector space. -/
def linearRootArrangement (Φ : Set (Module.Dual ℝ V)) : Set (V →ᵃ[ℝ] ℝ) :=
  LinearMap.toAffineMap '' Φ

/-- On roots through a fixed point, taking the derivative is a bijection onto
the actual derivative image. -/
def vanishingRootDerivativeEquiv (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :
    vanishingRoots Ψ x ≃ derivativeRoots (vanishingRoots Ψ x) :=
  Equiv.ofBijective
    (fun ψ => ⟨ψ.val.linear, linear_mem_derivativeRoots ψ.property⟩)
    ⟨fun ψ η h => Subtype.ext
      (linear_injOn_vanishingRoots Ψ x ψ.property η.property
        (congrArg Subtype.val h)),
      by
        rintro ⟨a, ψ, hψ, rfl⟩
        exact ⟨⟨ψ, hψ⟩, rfl⟩⟩

@[simp] theorem vanishingRootDerivativeEquiv_apply
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) (ψ : vanishingRoots Ψ x) :
    (vanishingRootDerivativeEquiv Ψ x ψ).val = ψ.val.linear := rfl

/-- Translation to a zero of an affine root removes its constant term. -/
theorem affineFunctionalTransport_vsub_eq_linear {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ x = 0) :
    affineFunctionalTransport (AffineEquiv.vaddConst ℝ x).symm ψ =
      ψ.linear.toAffineMap := by
  ext w
  change ψ (w +ᵥ x) = ψ.linear w
  rw [ψ.map_vadd, hψ]
  exact add_zero _

/-- The translated localized arrangement consists of exactly the actual
derivatives, viewed as linear affine maps. -/
theorem transportedRoots_vanishing_eq_linearRootArrangement
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :
    transportedRoots (AffineEquiv.vaddConst ℝ x).symm (vanishingRoots Ψ x) =
      linearRootArrangement (derivativeRoots (vanishingRoots Ψ x)) := by
  ext η
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact ⟨ψ.linear, linear_mem_derivativeRoots hψ,
      (affineFunctionalTransport_vsub_eq_linear hψ.2).symm⟩
  · rintro ⟨a, ⟨ψ, hψ, rfl⟩, rfl⟩
    exact ⟨ψ, hψ, affineFunctionalTransport_vsub_eq_linear hψ.2⟩

/-- Translation identifies all localized facets with facets of the actual
derivative arrangement. -/
def vanishingFacetDerivativeEquiv (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :
    {F : Set A // IsFacet (vanishingRoots Ψ x) F} ≃
      {C : Set V //
        IsFacet (linearRootArrangement (derivativeRoots (vanishingRoots Ψ x))) C} :=
  facetEquivOfTransportedRootsEq (AffineEquiv.vaddConst ℝ x).symm
    (transportedRoots_vanishing_eq_linearRootArrangement Ψ x)

@[simp] theorem vanishingFacetDerivativeEquiv_val
    (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A)
    (F : {F : Set A // IsFacet (vanishingRoots Ψ x) F}) :
    (vanishingFacetDerivativeEquiv Ψ x F).val = (fun y => y -ᵥ x) '' F.val := rfl

/-- Both sides carry their original affine-root face relation. -/
def vanishingFacetDerivativeOrderIso (Ψ : Set (A →ᵃ[ℝ] ℝ)) (x : A) :
    @OrderIso {F : Set A // IsFacet (vanishingRoots Ψ x) F}
      {C : Set V //
        IsFacet (linearRootArrangement (derivativeRoots (vanishingRoots Ψ x))) C}
      ⟨fun F G => IsFaceOf (vanishingRoots Ψ x) F.val G.val⟩
      ⟨fun C D =>
        IsFaceOf (linearRootArrangement (derivativeRoots (vanishingRoots Ψ x)))
          C.val D.val⟩ :=
  { vanishingFacetDerivativeEquiv Ψ x with
    map_rel_iff' := by
      intro F G
      change IsFaceOf
        (linearRootArrangement (derivativeRoots (vanishingRoots Ψ x)))
        ((AffineEquiv.vaddConst ℝ x).symm '' F.val)
        ((AffineEquiv.vaddConst ℝ x).symm '' G.val) ↔ _
      rw [← transportedRoots_vanishing_eq_linearRootArrangement]
      exact isFaceOf_image_iff_transportedRoots _ _ _ _ }

/-- The derivative facet containing the translate of the given incident full
facet. This uses the actual derivative forms. -/
def incidentFacetDerivative (F : IncidentAffineFacet Ψ x) :
    {C : Set V //
      IsFacet (linearRootArrangement (derivativeRoots (vanishingRoots Ψ x))) C} :=
  vanishingFacetDerivativeEquiv Ψ x (incidentFacetLocalization F)

@[simp] theorem incidentFacetDerivative_val (F : IncidentAffineFacet Ψ x) :
    (incidentFacetDerivative F).val =
      (fun y => y -ᵥ x) '' (incidentFacetLocalization F).val := rfl

/-- Every translated point of the original full facet lies in its derivative
facet. -/
theorem vsub_subset_incidentFacetDerivative (F : IncidentAffineFacet Ψ x) :
    (fun y => y -ᵥ x) '' F.val ⊆ (incidentFacetDerivative F).val :=
  Set.image_mono (subset_incidentFacetLocalization F)

/-- The derivative comparison preserves and reflects original incidence
without a finiteness assumption. -/
theorem isFaceOf_incidentFacetDerivative_iff (F G : IncidentAffineFacet Ψ x) :
    IsFaceOf (linearRootArrangement (derivativeRoots (vanishingRoots Ψ x)))
      (incidentFacetDerivative F).val (incidentFacetDerivative G).val ↔
      IsFaceOf Ψ F.val G.val :=
  ((vanishingFacetDerivativeOrderIso Ψ x).map_rel_iff).trans
    (isFaceOf_incidentFacetLocalization_iff F G)

/-- Finite separation along segments realizes every derivative facet by an
original incident full facet. -/
def incidentFacetDerivativeOrderIso
    (hfinite : ∀ y : A, (segmentRoots Ψ x y).Finite) :
    @OrderIso (IncidentAffineFacet Ψ x)
      {C : Set V //
        IsFacet (linearRootArrangement (derivativeRoots (vanishingRoots Ψ x))) C}
      ⟨fun F G => IsFaceOf Ψ F.val G.val⟩
      ⟨fun C D =>
        IsFaceOf (linearRootArrangement (derivativeRoots (vanishingRoots Ψ x)))
          C.val D.val⟩ :=
  RelIso.trans (incidentFacetLocalizationOrderIso hfinite)
    (vanishingFacetDerivativeOrderIso Ψ x)

@[simp] theorem incidentFacetDerivativeOrderIso_apply
    (hfinite : ∀ y : A, (segmentRoots Ψ x y).Finite)
    (F : IncidentAffineFacet Ψ x) :
    incidentFacetDerivativeOrderIso hfinite F = incidentFacetDerivative F := rfl

/-- Actual linear forms nonnegative on every point of the given subset. -/
def nonnegativeLinearRoots (Φ : Set (Module.Dual ℝ V)) (C : Set V) :
    Set (Module.Dual ℝ V) :=
  {a | a ∈ Φ ∧ ∀ w ∈ C, 0 ≤ a w}

/-- The derivative map carries vanishing-root supports to precisely the
nonnegative linear forms on the translated subset. -/
theorem image_linear_nonnegativeRoots_vanishing (F : Set A) :
    (fun ψ : A →ᵃ[ℝ] ℝ => ψ.linear) '' nonnegativeRoots (vanishingRoots Ψ x) F =
      nonnegativeLinearRoots (derivativeRoots (vanishingRoots Ψ x))
        ((fun y => y -ᵥ x) '' F) := by
  have hv (ψ : A →ᵃ[ℝ] ℝ) (hψ : ψ x = 0) (y : A) :
      ψ.linear (y -ᵥ x) = ψ y := by
    rw [ψ.linearMap_vsub, hψ, vsub_eq_sub, sub_zero]
  ext a
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    refine ⟨linear_mem_derivativeRoots hψ.1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hv ψ hψ.1.2]
    exact hψ.2 y hy
  · rintro ⟨⟨ψ, hψ, rfl⟩, h⟩
    refine ⟨ψ, ⟨hψ, fun y hy => ?_⟩, rfl⟩
    rw [← hv ψ hψ.2]
    exact h _ ⟨y, hy, rfl⟩

/-- Passing from an incident full facet to its derivative facet preserves
exactly the supports, with each root replaced by its actual derivative. -/
theorem nonnegativeLinearRoots_incidentFacetDerivative
    (F : IncidentAffineFacet Ψ x) :
    nonnegativeLinearRoots (derivativeRoots (vanishingRoots Ψ x))
      (incidentFacetDerivative F).val =
        (fun ψ : A →ᵃ[ℝ] ℝ => ψ.linear) ''
          nonnegativeRoots (vanishingRoots Ψ x) F.val := by
  rw [incidentFacetDerivative_val, ← image_linear_nonnegativeRoots_vanishing,
    nonnegativeRoots_incidentFacetLocalization]

/-- Reverse inclusion of actual derivative supports detects original incidence. -/
theorem isFaceOf_iff_incident_nonnegativeLinearRoots_subset
    (hneg : ∀ ψ ∈ Ψ, -ψ ∈ Ψ) (F G : IncidentAffineFacet Ψ x) :
    IsFaceOf Ψ F.val G.val ↔
      nonnegativeLinearRoots (derivativeRoots (vanishingRoots Ψ x))
          (incidentFacetDerivative G).val ⊆
        nonnegativeLinearRoots (derivativeRoots (vanishingRoots Ψ x))
          (incidentFacetDerivative F).val := by
  rw [nonnegativeLinearRoots_incidentFacetDerivative,
    nonnegativeLinearRoots_incidentFacetDerivative,
    (linear_injOn_vanishingRoots Ψ x).image_subset_image_iff
      (fun _ h => h.1) (fun _ h => h.1)]
  exact isFaceOf_iff_incident_nonnegativeRoots_subset hneg F G

/-- Corrected affine root systems, including rank zero, supply finite segment
separation and hence the derivative order isomorphism. -/
def IsAffineRootSystemWithRankZero.incidentFacetDerivativeOrderIso
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (x : A) :
    @OrderIso (IncidentAffineFacet Ψ x)
      {C : Set V //
        IsFacet (linearRootArrangement (derivativeRoots (vanishingRoots Ψ x))) C}
      ⟨fun F G => IsFaceOf Ψ F.val G.val⟩
      ⟨fun C D =>
        IsFaceOf (linearRootArrangement (derivativeRoots (vanishingRoots Ψ x)))
          C.val D.val⟩ :=
  AffineRootSystem.incidentFacetDerivativeOrderIso (hΨ.finite_segment_roots x)

end Langlands.Geometry.Building.AffineRootSystem
