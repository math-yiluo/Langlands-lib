import Langlands.Representation.Smooth.CompactCompletion
import Langlands.Group.PositiveCharacterExtension
import Langlands.Group.HaarModulus
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Compact-open completions and character twists

A character trivial on compact open subgroups does not change their normalized
averages, hence does not change the completion subspace. Positive open-kernel
characters supply this triviality, including the intrinsic Haar normalization
pulled back along a continuous homomorphism into a normalizing subgroup.
-/

noncomputable section

namespace Langlands

open HarishChandraSchwartz
open scoped NNReal

universe uG uV uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

namespace Compact

/-- A twist trivial on the averaging subgroup has the same normalized average. -/
theorem averageMap_twist (χ : G →* ℂˣ) (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (hχρ : IsSmooth (twist χ ρ))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hχ : K.toSubgroup ≤ χ.ker) :
    averageMap (twist χ ρ) hχρ K hK = averageMap ρ hρ K hK := by
  have hrestr : (twist χ ρ).comp K.toSubgroup.subtype =
      ρ.comp K.toSubgroup.subtype := by
    ext k v
    change (χ (k : G) : ℂ) • ρ (k : G) v = ρ (k : G) v
    have hk : χ (k : G) = 1 := hχ k.property
    simp only [hk, Units.val_one, one_smul]
  ext v
  change orbitMean ((twist χ ρ).comp K.toSubgroup.subtype) v =
    orbitMean (ρ.comp K.toSubgroup.subtype) v
  rw [hrestr]

end Compact

namespace CompactCompletion

/-- Compact-trivial twists give equal subspaces of compatible families. -/
theorem completion_twist_eq (χ : G →* ℂˣ) (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (hχρ : IsSmooth (twist χ ρ))
    (hχ : ∀ K : CompactOpenSubgroup G, K.1.toSubgroup ≤ χ.ker) :
    completion (twist χ ρ) hχρ = completion ρ hρ := by
  apply Submodule.ext
  intro v
  change (∀ K L : CompactOpenSubgroup G, L.1 ≤ K.1 →
    Compact.averageMap (twist χ ρ) hχρ K.1 K.2 (v L) = v K) ↔
    (∀ K L : CompactOpenSubgroup G, L.1 ≤ K.1 →
    Compact.averageMap ρ hρ K.1 K.2 (v L) = v K)
  simp_rw [Compact.averageMap_twist χ ρ hρ hχρ _ _ (hχ _)]

/-- The identity on families compares a compact-trivial twist's completion
with the original completion. -/
def twistEquiv (χ : G →* ℂˣ) (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (hχρ : IsSmooth (twist χ ρ))
    (hχ : ∀ K : CompactOpenSubgroup G, K.1.toSubgroup ≤ χ.ker) :
    completion (twist χ ρ) hχρ ≃ₗ[ℂ] completion ρ hρ :=
  LinearEquiv.ofEq _ _ (completion_twist_eq χ ρ hρ hχρ hχ)

@[simp]
theorem twistEquiv_apply (χ : G →* ℂˣ) (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (hχρ : IsSmooth (twist χ ρ))
    (hχ : ∀ K : CompactOpenSubgroup G, K.1.toSubgroup ≤ χ.ker)
    (v : completion (twist χ ρ) hχρ) (K : CompactOpenSubgroup G) :
    (twistEquiv χ ρ hρ hχρ hχ v).1 K = v.1 K :=
  rfl

@[simp]
theorem twistEquiv_symm_apply (χ : G →* ℂˣ) (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (hχρ : IsSmooth (twist χ ρ))
    (hχ : ∀ K : CompactOpenSubgroup G, K.1.toSubgroup ≤ χ.ker)
    (v : completion ρ hρ) (K : CompactOpenSubgroup G) :
    ((twistEquiv χ ρ hρ hχρ hχ).symm v).1 K = v.1 K :=
  rfl

/-- The inverse half of an open-kernel positive character kills every compact
open subgroup. -/
theorem inverseHalfCharacter_compact_le_ker (δ : G →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set G)) (K : CompactOpenSubgroup G) :
    K.1.toSubgroup ≤ (Jacquet.inverseHalfCharacter δ).ker := by
  intro k hk
  change Jacquet.inverseHalfCharacter δ k = 1
  apply (Jacquet.inverseHalfCharacter_eq_one δ k).mpr
  exact PositiveCharacter.eq_one_on_compact δ hδ K.1.toSubgroup K.2 ⟨k, hk⟩

/-- Inverse-half normalization by a positive open-kernel character preserves
the completion, with its literal families unchanged. -/
def inverseHalfTwistEquiv (δ : G →* ℝ≥0ˣ) (hδ : IsOpen (δ.ker : Set G))
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hδρ : IsSmooth (twist (Jacquet.inverseHalfCharacter δ) ρ)) :
    completion (twist (Jacquet.inverseHalfCharacter δ) ρ) hδρ ≃ₗ[ℂ]
      completion ρ hρ :=
  twistEquiv _ ρ hρ hδρ (inverseHalfCharacter_compact_le_ker δ hδ)

@[simp]
theorem inverseHalfTwistEquiv_apply (δ : G →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set G)) (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hδρ : IsSmooth (twist (Jacquet.inverseHalfCharacter δ) ρ))
    (v : completion (twist (Jacquet.inverseHalfCharacter δ) ρ) hδρ)
    (K : CompactOpenSubgroup G) :
    (inverseHalfTwistEquiv δ hδ ρ hρ hδρ v).1 K = v.1 K :=
  rfl

section ClosedHaar

variable {A : Type uA} [Group A] [TopologicalSpace A]
variable [LocallyCompactSpace A] [NonarchimedeanGroup A]

/-- Continuous pullback of the actual closed Haar inverse-half character
is trivial on every compact open subgroup. -/
theorem closedInverseHalfCharacter_compact_le_ker
    (N : Subgroup A) (hN : IsClosed (N : Set A))
    (M : Subgroup A) (hMN : M ≤ Subgroup.normalizer (N : Set A))
    (ι : G →* M) (hι : Continuous ι) (K : CompactOpenSubgroup G) :
    K.1.toSubgroup ≤
      ((HaarModulus.closedInverseHalfCharacter N hN M hMN).comp ι).ker := by
  intro k hk
  change Jacquet.inverseHalfCharacter
    (HaarModulus.closedRestrictCharacter N hN M hMN) (ι k) = 1
  apply (Jacquet.inverseHalfCharacter_eq_one _ _).mpr
  exact PositiveCharacter.eq_one_on_compact
    ((HaarModulus.closedRestrictCharacter N hN M hMN).comp ι)
    ((HaarModulus.isOpen_ker_closedRestrictCharacter N hN M hMN).preimage hι)
    K.1.toSubgroup K.2 ⟨k, hk⟩

/-- The intrinsic closed Haar normalization, transported along a continuous
homomorphism into the normalizing subgroup, preserves completion families. -/
def closedInverseHalfTwistEquiv
    (N : Subgroup A) (hN : IsClosed (N : Set A))
    (M : Subgroup A) (hMN : M ≤ Subgroup.normalizer (N : Set A))
    (ι : G →* M) (hι : Continuous ι)
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hχρ : IsSmooth
      (twist ((HaarModulus.closedInverseHalfCharacter N hN M hMN).comp ι) ρ)) :
    completion
        (twist ((HaarModulus.closedInverseHalfCharacter N hN M hMN).comp ι) ρ) hχρ
      ≃ₗ[ℂ] completion ρ hρ :=
  twistEquiv _ ρ hρ hχρ
    (closedInverseHalfCharacter_compact_le_ker N hN M hMN ι hι)

@[simp]
theorem closedInverseHalfTwistEquiv_apply
    (N : Subgroup A) (hN : IsClosed (N : Set A))
    (M : Subgroup A) (hMN : M ≤ Subgroup.normalizer (N : Set A))
    (ι : G →* M) (hι : Continuous ι)
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hχρ : IsSmooth
      (twist ((HaarModulus.closedInverseHalfCharacter N hN M hMN).comp ι) ρ))
    (v : completion
      (twist ((HaarModulus.closedInverseHalfCharacter N hN M hMN).comp ι) ρ) hχρ)
    (K : CompactOpenSubgroup G) :
    (closedInverseHalfTwistEquiv N hN M hMN ι hι ρ hρ hχρ v).1 K = v.1 K :=
  rfl

end ClosedHaar

end CompactCompletion

end Langlands
