import Langlands.Correspondence.HenniartExtensionReduction

/-!
# Unramified-twist independence of stable images

Henniart (2000), §4.4, with Henniart (1993), §4.3. Let `z₁⁻¹ σ` and `z₂⁻¹ σ` be
unramified twists of one irreducible Weil class, both unitary with stable images
`y₁` and `y₂`. The second is the twist of the first by the unramified character
with value `w = z₁ z₂⁻¹`, and `‖w‖ = 1` because both classes are unitary. One
candidate sends both classes to their stable images, and its twist compatibility
for the unramified field character with value `w` gives `y₂ = w y₁`. Hence
`z₁ y₁ = z₂ y₂`. Candidate existence and a geometric reciprocity candidate are
the only inputs.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap
open LocalFactor LocalFactor.CommonClosure

universe uK uW uV uE

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartTwistIndependenceFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- Unramified-twist independence at one field, given candidate existence and a
geometric reciprocity candidate of that field. -/
theorem stableImage_unramifiedTwist
    (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e)
    (σ : LocalWeil.Basis.{uK, uW} K) (z₁ z₂ : ℂˣ)
    (σ₁ σ₂ : LocalWeil.UnitaryBasis.{uK, uW} K)
    (y₁ y₂ : PadicSupercuspidal.UnitaryLattice.{uK, uV} K)
    (hσ₁ : σ₁.val = weilUnramifiedTwist K z₁⁻¹ σ)
    (hσ₂ : σ₂.val = weilUnramifiedTwist K z₂⁻¹ σ)
    (h₁ : IsStableImage.{uK, uW, uV, uE} K σ₁ y₁)
    (h₂ : IsStableImage.{uK, uW, uV, uE} K σ₂ y₂) :
    PadicSupercuspidal.unramifiedTwistLatticeEquiv K z₁ (PadicSupercuspidal.includeUnitary K y₁) =
      PadicSupercuspidal.unramifiedTwistLatticeEquiv K z₂
        (PadicSupercuspidal.includeUnitary K y₂) := by
  set w := z₁ * z₂⁻¹ with hw_def
  -- `σ₂` is the twist of `σ₁` by the unramified character with value `w`
  have htw : Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K w) σ₁.val = σ₂.val := by
    rw [hσ₁, hσ₂]
    change ((Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K z₁⁻¹)).trans
      (Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K w))) σ =
        Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K z₂⁻¹) σ
    rw [Weil.twistBasisEquiv_mul, localUnramifiedCharacter_mul, hw_def, mul_right_comm,
      mul_inv_cancel, one_mul]
  -- the unramified field character with value `w` has modulus one
  have hχ : ∀ a, ‖(fieldUnramified K w a : ℂ)‖ = 1 := by
    intro a
    obtain ⟨g, rfl⟩ := reciprocityHom_surjective' K e a
    have htw' : Weil.twistBasisEquiv
        (LocalFactor.RankOne.weilCharacter K e (fieldUnramified K w)) σ₁.val = σ₂.val := by
      rw [weilCharacter_fieldUnramified K he]
      exact htw
    exact Weil.norm_eq_one_of_isUnitaryClass_twist
      (LocalFactor.RankOne.weilCharacter K e (fieldUnramified K w)) σ₁.property
      (htw' ▸ σ₂.property) g
  have hw : ‖(w : ℂ)‖ = 1 := by
    have hu : (fieldUnramified K w K.canonicalTopologicalData.uniformizerUnit : ℂ) = w :=
      congrArg Units.val (K.canonicalTopologicalData.unramifiedCharacter_uniformizer w)
    have h := hχ K.canonicalTopologicalData.uniformizerUnit
    rwa [hu] at h
  -- one candidate sends both classes to their stable images
  obtain ⟨W, A, Φ, hΦ, ⟨x, hx, hΦx⟩, ⟨x', hx', hΦx'⟩⟩ := exists_common_candidate₂ K hCE h₁ h₂
  obtain ⟨π₁, rfl, -⟩ := h₁.exists_generator K
  obtain ⟨x'', hx'', hΦx''⟩ := candidate_twist_generator K hΦ he (fieldUnramified K w)
    (norm_fieldUnramified K hw) x hx hΦx
  have hσ : weilUnitaryTwist K e (fieldUnramified K w) (norm_fieldUnramified K hw) σ₁ = σ₂ :=
    Subtype.ext ((unitaryFieldCharacterTwist_fieldUnramified_val K he hw σ₁).2.trans htw)
  rw [hσ] at hx''
  have hxx : x'' = x' := Subtype.ext (hx''.trans hx'.symm)
  rw [hxx, hΦx'] at hΦx''
  subst hΦx''
  have hinc : ∀ π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K,
      PadicSupercuspidal.includeUnitary K (generator π) = generator π.val := by
    intro π
    simp [PadicSupercuspidal.includeUnitary, Supercuspidal.includeUnitary, includeSubset,
      VirtualRepresentation.map, generator]
  have hval : (supercuspidalUnitaryTwist K (fieldUnramified K w) (norm_fieldUnramified K hw)
      π₁).val = PadicSupercuspidal.unramifiedTwistBasisEquiv K w π₁.val :=
    rfl
  rw [hinc, hinc, PadicSupercuspidal.unramifiedTwistLatticeEquiv_generator,
    PadicSupercuspidal.unramifiedTwistLatticeEquiv_generator, hval, ← Equiv.trans_apply,
    PadicSupercuspidal.unramifiedTwistBasisEquiv_mul, hw_def, mul_comm z₁ z₂⁻¹,
    mul_inv_cancel_left]

/-- Henniart (2000), §4.4: candidate existence and normalized local reciprocity
give the unramified-twist independence of stable images. -/
theorem unramifiedTwistIndependence_of_reciprocity
    (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    (hrec : LocalClassField.CommonClosureReciprocityExistence.{uK}) :
    UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE} := by
  intro p _ K σ z₁ z₂ σ₁ σ₂ y₁ y₂ hσ₁ hσ₂ h₁ h₂
  obtain ⟨eC, heC⟩ := hrec p K K.canonicalTopologicalData
  exact stableImage_unramifiedTwist K hCE (baseGeometricReciprocityProof K eC heC) σ z₁ z₂
    σ₁ σ₂ y₁ y₂ hσ₁ hσ₂ h₁ h₂

end Langlands.Henniart.Extension
