import Langlands.HarmonicAnalysis.Distribution.Subspace
import Langlands.HarmonicAnalysis.Distribution.ClosedSupportedDescentProof

/-! # Supported-distribution descent on closed subsets and relatively closed pieces -/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

universe u

section Closed

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] {Z : Set X}

/-- The closed pushforward as a linear equivalence onto the supported distributions,
using the published bijectivity theorem. Its inverse is the chosen closed descent. -/
def closedPushforwardSupportedEquiv (hZ : IsClosed Z) :
    Distribution Z ≃ₗ[ℂ] supportedOn Z :=
  LinearEquiv.ofBijective (closedPushforwardSupported hZ) (closedSupportedDescent X Z hZ)

/-- The forward linear map is the published `closedPushforwardSupported`. -/
theorem closedPushforwardSupportedEquiv_toLinearMap (hZ : IsClosed Z) :
    (closedPushforwardSupportedEquiv hZ).toLinearMap = closedPushforwardSupported hZ :=
  rfl

@[simp]
theorem closedPushforwardSupportedEquiv_apply (hZ : IsClosed Z) (D : Distribution Z) :
    closedPushforwardSupportedEquiv hZ D = closedPushforwardSupported hZ D :=
  rfl

/-- The ambient coercion of the forward map is the actual closed pushforward. -/
@[simp]
theorem coe_closedPushforwardSupportedEquiv (hZ : IsClosed Z) (D : Distribution Z) :
    (closedPushforwardSupportedEquiv hZ D : Distribution X) = closedPushforward hZ D :=
  rfl

@[simp]
theorem closedPushforwardSupportedEquiv_symm_apply_apply (hZ : IsClosed Z)
    (D : Distribution Z) :
    (closedPushforwardSupportedEquiv hZ).symm (closedPushforwardSupportedEquiv hZ D) = D :=
  (closedPushforwardSupportedEquiv hZ).symm_apply_apply D

@[simp]
theorem closedPushforwardSupportedEquiv_apply_symm_apply (hZ : IsClosed Z)
    (T : supportedOn Z) :
    closedPushforwardSupportedEquiv hZ ((closedPushforwardSupportedEquiv hZ).symm T) = T :=
  (closedPushforwardSupportedEquiv hZ).apply_symm_apply T

/-- The chosen descent pushes forward to the original supported distribution. -/
@[simp]
theorem closedPushforward_closedPushforwardSupportedEquiv_symm (hZ : IsClosed Z)
    (T : supportedOn Z) :
    closedPushforward hZ ((closedPushforwardSupportedEquiv hZ).symm T) =
      (T : Distribution X) :=
  congrArg Subtype.val ((closedPushforwardSupportedEquiv hZ).apply_symm_apply T)

theorem closedPushforwardSupportedEquiv_symm_apply_restrictClosed (hZ : IsClosed Z)
    (T : supportedOn Z) (f : SchwartzBruhat X) :
    (closedPushforwardSupportedEquiv hZ).symm T (SchwartzBruhat.restrictClosed hZ f) =
      (T : Distribution X) f := by
  rw [← closedPushforward_apply, closedPushforward_closedPushforwardSupportedEquiv_symm]

/-- The chosen descent is the unique distribution on `Z` with the given pushforward. -/
theorem eq_closedPushforwardSupportedEquiv_symm_iff (hZ : IsClosed Z)
    (T : supportedOn Z) (D : Distribution Z) :
    D = (closedPushforwardSupportedEquiv hZ).symm T ↔
      closedPushforward hZ D = (T : Distribution X) := by
  rw [LinearEquiv.eq_symm_apply]
  exact Subtype.ext_iff

end Closed

section Open

variable {X : Type u} [TopologicalSpace X] [T2Space X] {U : Set X}

/-- Open restriction preserves pointwise support, with the preimage in `U`. -/
theorem restrictOpen_mem_supportedOn (hU : IsOpen U) {Z : Set X} {D : Distribution X}
    (hD : D ∈ supportedOn Z) :
    restrictOpen hU D ∈ supportedOn ((Subtype.val : U → X) ⁻¹' Z) := by
  intro f hf
  rw [restrictOpen_apply]
  apply hD
  intro z hz
  by_cases hzU : z ∈ U
  · rw [SchwartzBruhat.extendZero_apply_of_mem hU f hzU]
    exact hf ⟨z, hzU⟩ hz
  · exact SchwartzBruhat.extendZero_apply_of_not_mem hU f hzU

/-- Open restriction between supported submodules; `Z` need not be closed. -/
def restrictOpenSupported (hU : IsOpen U) (Z : Set X) :
    supportedOn Z →ₗ[ℂ] supportedOn ((Subtype.val : U → X) ⁻¹' Z) :=
  ((restrictOpen hU).comp (supportedOn Z).subtype).codRestrict _
    (fun D => restrictOpen_mem_supportedOn hU D.property)

@[simp]
theorem coe_restrictOpenSupported (hU : IsOpen U) (Z : Set X) (D : supportedOn Z) :
    (restrictOpenSupported hU Z D : Distribution U) = restrictOpen hU (D : Distribution X) :=
  rfl

theorem restrictOpenSupported_apply (hU : IsOpen U) (Z : Set X) (D : supportedOn Z)
    (f : SchwartzBruhat U) :
    (restrictOpenSupported hU Z D : Distribution U) f =
      (D : Distribution X) (SchwartzBruhat.extendZero hU f) :=
  rfl

end Open

section Descent

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] {U Z : Set X}

/-- Descent of a distribution supported on `Z` to the relatively closed piece
`U ∩ Z` of the open subspace `U`, presented as a subset of `U`. -/
def descendInOpen (hU : IsOpen U) (hZU : IsClosed ((Subtype.val : U → X) ⁻¹' Z)) :
    supportedOn Z →ₗ[ℂ] Distribution ((Subtype.val : U → X) ⁻¹' Z) :=
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  (closedPushforwardSupportedEquiv hZU).symm.toLinearMap ∘ₗ restrictOpenSupported hU Z

theorem descendInOpen_eq_comp (hU : IsOpen U)
    (hZU : IsClosed ((Subtype.val : U → X) ⁻¹' Z)) :
    haveI : LocallyCompactSpace U := hU.locallyCompactSpace
    descendInOpen hU hZU =
      (closedPushforwardSupportedEquiv hZU).symm.toLinearMap ∘ₗ restrictOpenSupported hU Z :=
  rfl

theorem descendInOpen_apply (hU : IsOpen U) (hZU : IsClosed ((Subtype.val : U → X) ⁻¹' Z))
    (D : supportedOn Z) :
    haveI : LocallyCompactSpace U := hU.locallyCompactSpace
    descendInOpen hU hZU D =
      (closedPushforwardSupportedEquiv hZU).symm (restrictOpenSupported hU Z D) :=
  rfl

/-- The descended distribution pushes forward to the open restriction. -/
@[simp]
theorem closedPushforward_descendInOpen (hU : IsOpen U)
    (hZU : IsClosed ((Subtype.val : U → X) ⁻¹' Z)) (D : supportedOn Z) :
    closedPushforward hZU (descendInOpen hU hZU D) = restrictOpen hU (D : Distribution X) :=
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  closedPushforward_closedPushforwardSupportedEquiv_symm hZU (restrictOpenSupported hU Z D)

theorem descendInOpen_apply_restrictClosed (hU : IsOpen U)
    (hZU : IsClosed ((Subtype.val : U → X) ⁻¹' Z)) (D : supportedOn Z)
    (f : SchwartzBruhat U) :
    descendInOpen hU hZU D (SchwartzBruhat.restrictClosed hZU f) =
      (D : Distribution X) (SchwartzBruhat.extendZero hU f) := by
  rw [← closedPushforward_apply, closedPushforward_descendInOpen, restrictOpen_apply]

/-- Uniqueness: the descent is the only distribution on the nested subtype whose
closed pushforward is the open restriction. -/
theorem eq_descendInOpen_iff (hU : IsOpen U) (hZU : IsClosed ((Subtype.val : U → X) ⁻¹' Z))
    (D : supportedOn Z) (E : Distribution ((Subtype.val : U → X) ⁻¹' Z)) :
    E = descendInOpen hU hZU D ↔
      closedPushforward hZU E = restrictOpen hU (D : Distribution X) :=
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  eq_closedPushforwardSupportedEquiv_symm_iff hZU (restrictOpenSupported hU Z D) E

end Descent

end Langlands.HarmonicAnalysis.Distribution
