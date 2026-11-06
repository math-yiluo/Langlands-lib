import Langlands.Representation.Plancherel.UnramifiedNormalizedModels
import Langlands.Representation.Jacquet.CoefficientScalarRestriction
import Langlands.Representation.Smooth.FixedVectors.NormalizedJacquetBridgeProof

/-! # Normalized coefficient Jacquet finiteness and actual compact compression -/

noncomputable section

set_option autoImplicit false

open scoped NNReal

namespace Langlands.Plancherel.UnramifiedNormalized

universe uL uI uG uV

variable {L : Type uL} [Group L] [TopologicalSpace L]
variable {I : Type uI} (ν : I → (L →* ℝ≥0ˣ))
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable [LocallyCompactSpace G] [NonarchimedeanGroup G]
variable {V : Type uV} [AddCommGroup V] [Module (unramifiedRegularFunctions ν) V]
variable (ρ : Representation (unramifiedRegularFunctions ν) G V)

/-- On a compact intersection with a closed Levi, the actual normalized
coefficient Jacquet fixed space is the actual unnormalized one. -/
def normalizedJacquetFixedEquiv (N M : Subgroup G)
    (hN : IsClosed (N : Set G)) (hMN : M ≤ Subgroup.normalizer N)
    (hM : IsClosed (M : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    fixedVectors (jacquetRepresentation ν ρ N M hN hMN)
        (K.toSubgroup.comap M.subtype) ≃ₗ[unramifiedRegularFunctions ν]
      fixedVectors (Jacquet.action ρ N M hMN) (K.toSubgroup.comap M.subtype) := by
  let χ := (jacquetCharacter ν N M hN hMN).toMonoidHom
  have hχ : K.toSubgroup.comap M.subtype ≤ χ.ker := by
    change K.toSubgroup.comap M.subtype ≤
      (constantCharacter ν (HaarModulus.closedInverseHalfCharacter N hN M hMN)).ker
    rw [constantCharacter_ker]
    exact NormalizedJacquetBridge.character_trivial N M hN hMN hM K hK
  let e := LinearEquiv.ofEq _ _
    (fixedVectors_twist_eq_of_le_ker χ
      (Jacquet.Localization.action ρ N 1 M hMN
        (Jacquet.Localization.isInvariant_one N M hMN))
      (K.toSubgroup.comap M.subtype) hχ)
  exact e.trans (Langlands.fixedVectorsEquiv
    (Jacquet.Localization.trivialEquiv ρ N M hMN) (K.toSubgroup.comap M.subtype))

section Compression

variable [Module ℂ V] [IsScalarTower ℂ (unramifiedRegularFunctions ν) V]
variable [IsNoetherianRing (unramifiedRegularFunctions ν)]
variable (hρ : IsSmooth ρ)
variable {N M Nbar : Subgroup G} {g : G}
variable (hN : IsClosed (N : Set G)) (hMN : M ≤ Subgroup.normalizer N)
variable (hM : IsClosed (M : Set G))
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
variable (h : Jacquet.IsIwahoriContraction K N M Nbar g)
variable (hcentral : ∀ m ∈ M, m * g = g * m)

include h hcentral hM in
/-- Finiteness of the normalized coefficient Jacquet fixed space is exactly
the target input needed by the actual complex compression criterion. -/
theorem compressedAction_eventuallyStable_of_normalized_finite
    [Module.Finite (unramifiedRegularFunctions ν) (fixedVectors ρ K.toSubgroup)]
    [Module.Finite (unramifiedRegularFunctions ν)
      (fixedVectors (jacquetRepresentation ν ρ N M hN hMN) (K.toSubgroup.comap M.subtype))] :
    LinearAlgebra.StableEndomorphism.EventuallyStable
      (Jacquet.compressedAction
        (Jacquet.CoefficientRestriction.complexRepresentation ρ)
        ((Jacquet.CoefficientRestriction.isSmooth_complexRepresentation ρ).mpr hρ)
        K hK g) := by
  let : Module.Finite (unramifiedRegularFunctions ν)
      (fixedVectors (Jacquet.action ρ N M hMN) (K.toSubgroup.comap M.subtype)) :=
    Module.Finite.of_surjective
      (normalizedJacquetFixedEquiv ν ρ N M hN hMN hM K hK).toLinearMap
      (normalizedJacquetFixedEquiv ν ρ N M hN hMN hM K hK).surjective
  exact Jacquet.CoefficientRestriction.compressedAction_eventuallyStable_of_native_finite
    ρ hρ K hK h hMN hcentral

end Compression

end Langlands.Plancherel.UnramifiedNormalized
