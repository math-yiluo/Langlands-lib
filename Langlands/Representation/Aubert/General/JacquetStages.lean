import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Jacquet.LocalizationTower

/-! # Normalized Jacquet restriction in stages for actual subgroup copies -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV

open SmoothRep
open Jacquet.Localization

section CompactLimit

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An open-kernel positive character is trivial on a subgroup which is a
limit of compact subgroups. -/
theorem positiveCharacter_eq_one_on_compactLimit
    (χ : G →* NNRealˣ) (hχ : IsOpen (χ.ker : Set G))
    (W : Subgroup G) (hWc : IsLimitOfCompactSubgroups W) (w : W) :
    χ w = 1 := by
  obtain ⟨K, hK, hwK⟩ := hWc {w} isCompact_singleton
  let ι : K →* G := W.subtype.comp K.subtype
  have hι : Continuous ι := continuous_subtype_val.comp continuous_subtype_val
  let ψ := χ.comp ι
  have hopen : IsOpen (ψ.ker : Set K) := hχ.preimage hι
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : Finite (K ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
  let x : K := ⟨w, hwK rfl⟩
  have hx : x ^ Nat.card (K ⧸ ψ.ker) ∈ ψ.ker := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  have hp : (ψ x : NNReal) ^ Nat.card (K ⧸ ψ.ker) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, MonoidHom.mem_ker.mp hx, Units.val_one]
  exact Units.ext ((pow_eq_one_iff_of_nonneg (by positivity) Nat.card_pos.ne').mp hp)

end CompactLimit

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- The published localization tower for trivial characters and literal copies
of the second radical and final Levi inside the first Levi. -/
def jacquetTowerDatum (U M W H : Subgroup G) (hWM : W ≤ M) (hHM : H ≤ M)
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hHW : H ≤ Subgroup.normalizer (W : Set G)) : TowerDatum ℂ G where
  U := U
  M := M
  W := W
  H := H
  W_le_M := hWM
  H_le_M := hHM
  M_le_normalizer := hMU
  H_le_normalizer := hHW
  θ := 1
  η := 1
  θ_invariant := isInvariant_one U M hMU
  η_invariant := isInvariant_one W H hHW
  Θ := 1
  Θ_comp_left := rfl
  Θ_comp_right := rfl

section Stages

variable (U M W H : Subgroup G) (hWM : W ≤ M) (hHM : H ≤ M)
  (hMU : M ≤ Subgroup.normalizer (U : Set G))
  (hHW : H ≤ Subgroup.normalizer (W : Set G))
  (hU : IsClosed (U : Set G)) (hM : IsClosed (M : Set G))
  (hW : IsClosed (W.subgroupOf M : Set M))
  (hV : IsClosed ((U ⊔ W : Subgroup G) : Set G))

/-- The actual inner Haar modulus, transported to the ambient final Levi. -/
def innerJacquetModulus : H →* NNRealˣ :=
  letI := hM.locallyCompactSpace
  (HaarModulus.closedRestrictCharacter (W.subgroupOf M) hW
    (H.subgroupOf M) (jacquetTowerDatum U M W H hWM hHM hMU hHW).acting_le_normalizer).comp
      (subgroupOfContinuousEquiv hHM).symm.toMonoidHom

/-- The actual iterated normalized Jacquet functor, with the final subgroup
copy transported back to the ambient final Levi. -/
def iteratedNormalizedJacquetFunctor :
    SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uG, uV} ℂ H :=
  letI := hM.locallyCompactSpace
  normalizedJacquetFunctor U M hU hMU ⋙
    normalizedJacquetFunctor (W.subgroupOf M) (H.subgroupOf M) hW
      (jacquetTowerDatum U M W H hWM hHM hMU hHW).acting_le_normalizer ⋙
    SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hHM).symm

variable (hWc : IsLimitOfCompactSubgroups (W.subgroupOf M))
  (hδ : (HaarModulus.closedRestrictCharacter U hU M hMU).comp
      (Subgroup.inclusion hHM) * innerJacquetModulus U M W H hWM hHM hMU hHW hM hW =
    HaarModulus.closedRestrictCharacter (U ⊔ W) hV H (jacquetTowerDatum U M W H hWM hHM hMU hHW).H_le_normalizer_sup)

/-- The actual normalized Jacquet comparison. The hypothesis `hδ` is exactly
the remaining Haar-modulus factorization, not a functor identity. -/
def normalizedJacquetStagesIso :
    iteratedNormalizedJacquetFunctor.{uG, uV}
      U M W H hWM hHM hMU hHW hU hM hW ≅
    normalizedJacquetFunctor (U ⊔ W) H hV (jacquetTowerDatum U M W H hWM hHM hMU hHW).H_le_normalizer_sup := by
  letI := hM.locallyCompactSpace
  let α := HaarModulus.closedInverseHalfCharacter U hU M hMU
  let β := Jacquet.inverseHalfCharacter
    (innerJacquetModulus U M W H hWM hHM hMU hHW hM hW)
  let γ := HaarModulus.closedInverseHalfCharacter (U ⊔ W) hV H (jacquetTowerDatum U M W H hWM hHM hMU hHW).H_le_normalizer_sup
  have hα : ∀ w : W.subgroupOf M, α (w : M) = 1 := by
    intro w
    apply (Jacquet.inverseHalfCharacter_eq_one _ _).mpr
    exact positiveCharacter_eq_one_on_compactLimit
      (HaarModulus.closedRestrictCharacter U hU M hMU)
      (HaarModulus.isOpen_ker_closedRestrictCharacter U hU M hMU)
      (W.subgroupOf M) hWc w
  have hγ : (jacquetTowerDatum U M W H hWM hHM hMU hHW).restrictedProduct α β = γ := by
    change (jacquetTowerDatum U M W H hWM hHM hMU hHW).restrictedProduct
      (Jacquet.inverseHalfCharacter (HaarModulus.closedRestrictCharacter U hU M hMU))
      (Jacquet.inverseHalfCharacter
        (innerJacquetModulus U M W H hWM hHM hMU hHW hM hW)) =
      Jacquet.inverseHalfCharacter
        (HaarModulus.closedRestrictCharacter (U ⊔ W) hV H (jacquetTowerDatum U M W H hWM hHM hMU hHW).H_le_normalizer_sup)
    exact ((jacquetTowerDatum U M W H hWM hHM hMU hHW).restrictedProduct_inverseHalfCharacter
      (HaarModulus.closedRestrictCharacter U hU M hMU)
      (innerJacquetModulus U M W H hWM hHM hMU hHW hM hW)).trans
        (congrArg Jacquet.inverseHalfCharacter hδ)
  refine NatIso.ofComponents
    (fun A => SmoothRep.mkIso ((jacquetTowerDatum U M W H hWM hHM hMU hHW).twistedEquivOfEq α hα β γ hγ A.representation)) ?_
  intro A B f
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  exact ((jacquetTowerDatum U M W H hWM hHM hMU hHW).twistedEquivOfEq_natural α hα β γ hγ (SmoothRep.hom f)).symm

end Stages

end Langlands.Aubert.General
