import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Restrict
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof

/-! # Total covers from the closed fibre over a local ring -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))

/-- An open containing the closed fibre of a universally closed morphism to a
local spectrum is the whole source. -/
theorem open_eq_top_of_contains_closedFibre [UniversallyClosed p]
    (U : X.Opens)
    (hU : ∀ x : X, p x = IsLocalRing.closedPoint R → x ∈ U) : U = ⊤ := by
  apply top_unique
  intro x _
  by_contra hx
  have hC := p.isClosedMap (U : Set X)ᶜ U.isOpen.isClosed_compl
  have hm : IsLocalRing.closedPoint R ∈ p '' (U : Set X)ᶜ :=
    (IsLocalRing.specializes_closedPoint (p x)).mem_closed hC ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hpy⟩ := hm
  exact hy (hU y hpy)

/-- Opens covering the closed fibre cover the total scheme. -/
theorem iSup_eq_top_of_covers_closedFibre [UniversallyClosed p]
    {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ x : X, p x = IsLocalRing.closedPoint R → ∃ i, x ∈ U i) :
    iSup U = ⊤ := by
  apply open_eq_top_of_contains_closedFibre p
  intro x hx
  exact Opens.mem_iSup.mpr (hU x hx)

/-- A neighbourhood of every actual closed-fibre point gives a total cover. -/
theorem iSup_eq_top_of_closedFibre_neighbourhoods [UniversallyClosed p]
    (U : p.fiber (IsLocalRing.closedPoint R) → X.Opens)
    (hU : ∀ x, p.fiberι (IsLocalRing.closedPoint R) x ∈ U x) : iSup U = ⊤ := by
  apply iSup_eq_top_of_covers_closedFibre p
  intro x hx
  have hx' : x ∈ Set.range (p.fiberι (IsLocalRing.closedPoint R)) := by
    rw [p.range_fiberι]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  exact ⟨y, hU y⟩

/-- The actual scheme open cover indexed by closed-fibre points and their
chosen total neighbourhoods. -/
def closedFibreNeighbourhoodCover [UniversallyClosed p]
    (U : p.fiber (IsLocalRing.closedPoint R) → X.Opens)
    (hU : ∀ x, p.fiberι (IsLocalRing.closedPoint R) x ∈ U x) : X.OpenCover :=
  X.openCoverOfIsOpenCover U (iSup_eq_top_of_closedFibre_neighbourhoods p U hU)

omit [IsLocalRing R] in
/-- Every fibre of a smooth geometrically connected morphism is integral. -/
theorem integral_fibre_of_smooth_geometricallyConnected [Smooth p]
    [GeometricallyConnected p] (s : Spec (CommRingCat.of R)) : IsIntegral (p.fiber s) := by
  have hs : Smooth (p.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ (inferInstance : Smooth p)
  have hc : GeometricallyConnected (p.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ (inferInstance : GeometricallyConnected p)
  have : GeometricallyIntegral (p.fiberToSpecResidueField s) :=
    Langlands.AbelianScheme.smoothGeometricIntegrality _ _ _ hs hc
  exact GeometricallyIntegral.isIntegral_of_subsingleton (p.fiberToSpecResidueField s)

/-- The image in the total scheme of the generic point of its closed fibre. -/
def closedFibreGenericPoint [Smooth p] [GeometricallyConnected p] : X := by
  let : IsIntegral (p.fiber (IsLocalRing.closedPoint R)) :=
    integral_fibre_of_smooth_geometricallyConnected p _
  exact p.fiberι (IsLocalRing.closedPoint R)
    (genericPoint (p.fiber (IsLocalRing.closedPoint R)))

/-- The chosen total point is a generic point of the set-theoretic closed fibre. -/
theorem closedFibreGenericPoint_spec [Smooth p] [GeometricallyConnected p] :
    IsGenericPoint (closedFibreGenericPoint p) (p ⁻¹' {IsLocalRing.closedPoint R}) := by
  let : IsIntegral (p.fiber (IsLocalRing.closedPoint R)) :=
    integral_fibre_of_smooth_geometricallyConnected p _
  have h := (genericPoint_spec (p.fiber (IsLocalRing.closedPoint R))).image
    (p.fiberι (IsLocalRing.closedPoint R)).continuous
  have hclosed : IsClosed (p ⁻¹' {IsLocalRing.closedPoint R}) :=
    (IsLocalRing.isClosed_singleton_closedPoint R).preimage p.continuous
  simp only [Set.image_univ] at h
  change IsGenericPoint (closedFibreGenericPoint p)
    (closure (Set.range (p.fiberι (IsLocalRing.closedPoint R)))) at h
  rw [p.range_fiberι, hclosed.closure_eq] at h
  exact h

/-- Every total open meeting the closed fibre contains its chosen generic point. -/
theorem closedFibreGenericPoint_mem [Smooth p] [GeometricallyConnected p]
    (U : X.Opens) (hU : (p ⁻¹' {IsLocalRing.closedPoint R} ∩ (U : Set X)).Nonempty) :
    closedFibreGenericPoint p ∈ U :=
  ((closedFibreGenericPoint_spec p).mem_open_set_iff U.isOpen).mpr hU

end Langlands.AlgebraicGeometry
