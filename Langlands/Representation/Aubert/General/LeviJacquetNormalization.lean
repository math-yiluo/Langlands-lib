import Langlands.Representation.Aubert.General.SubgroupOfModulus
import Langlands.Representation.Derivative.GeneralLinearDerivativeDeterminantTwistProof

/-! # Ambient normalization of the actual Levi-in-Levi Jacquet functor -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV

section Normalizer

variable {G : Type uG} [Group G] {M N L : Subgroup G}

/-- Normalization inside a containing subgroup detects normalization of the
entire ambient radical. -/
theorem normalizes_of_subgroupOf (hNM : N ≤ M) (hLM : L ≤ M)
    (hLN : L.subgroupOf M ≤ Subgroup.normalizer (N.subgroupOf M : Set M)) :
    L ≤ Subgroup.normalizer (N : Set G) := by
  intro l hl
  have hl' : (⟨l, hLM hl⟩ : M) ∈ L.subgroupOf M := hl
  exact (subgroupOfNormalizerMap hNM ⟨⟨l, hLM hl⟩, hLN hl'⟩).property

end Normalizer

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {M Q L N : Subgroup G}

/-- Localize inside `M`, identify the output subgroup with `L`, and twist by
the actual ambient inverse half-modulus of `N`. -/
def leviAmbientNormalizedJacquetFunctor
    (hNM : N ≤ M) (hLM : L ≤ M)
    (hLN : L.subgroupOf M ≤ Subgroup.normalizer (N.subgroupOf M : Set M))
    (hN : IsClosed (N : Set G)) :
    SmoothRep.{0, uG, uV} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ L :=
  Jacquet.Localization.smoothFunctor (N.subgroupOf M) 1 (L.subgroupOf M) hLN
      (Jacquet.Localization.isInvariant_one _ _ hLN) ⋙
    SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hLM).symm ⋙
      SmoothRep.twistFunctor
        (HaarModulus.closedInverseHalfCharacter N hN L
          (normalizes_of_subgroupOf hNM hLM hLN))
        (HaarModulus.isOpen_ker_closedInverseHalfCharacter N hN L
          (normalizes_of_subgroupOf hNM hLM hLN))

/-- The actual inside inverse half-modulus, pulled to `L`, is the ambient
inverse half-modulus. -/
theorem leviInverseHalfCharacter_eq
    (hM : IsClosed (M : Set G)) (hNM : N ≤ M) (hLM : L ≤ M)
    (hLN : L.subgroupOf M ≤ Subgroup.normalizer (N.subgroupOf M : Set M))
    (hN : IsClosed (N : Set G)) (l : L) :
    letI : LocallyCompactSpace M := hM.locallyCompactSpace
    HaarModulus.closedInverseHalfCharacter (N.subgroupOf M)
        (hN.preimage continuous_subtype_val) (L.subgroupOf M) hLN
        ((subgroupOfContinuousEquiv hLM).symm l) =
      HaarModulus.closedInverseHalfCharacter N hN L
        (normalizes_of_subgroupOf hNM hLM hLN) l := by
  let : LocallyCompactSpace M := hM.locallyCompactSpace
  simpa only [ContinuousMulEquiv.apply_symm_apply] using
    closedInverseHalfCharacter_subgroupOf hM hN hNM hLM
      (normalizes_of_subgroupOf hNM hLM hLN)
      ((subgroupOfContinuousEquiv hLM).symm l)

/-- Moving the actual Levi-in-Levi Jacquet normalization through the subgroup
identification exposes the ambient inverse half-modulus. Every component is
the identity on the original localization carrier. -/
def leviNormalizedJacquetAmbientIso
    (hM : IsClosed (M : Set G)) (hNM : N ≤ M) (hLM : L ≤ M)
    (h : IsSemidirectDecomposition
      (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G)) :
    leviNormalizedJacquetFunctor.{uG, uV} hM hLM h hN ≅
      leviAmbientNormalizedJacquetFunctor hNM hLM h.levi_le_normalizer hN := by
  let : LocallyCompactSpace M := hM.locallyCompactSpace
  let e := (subgroupOfContinuousEquiv hLM).symm
  let χ := HaarModulus.closedInverseHalfCharacter (N.subgroupOf M)
    (hN.preimage continuous_subtype_val) (L.subgroupOf M) h.levi_le_normalizer
  let η := HaarModulus.closedInverseHalfCharacter N hN L
    (normalizes_of_subgroupOf hNM hLM h.levi_le_normalizer)
  have hχ : IsOpen (χ.ker : Set (L.subgroupOf M)) :=
    HaarModulus.isOpen_ker_closedInverseHalfCharacter _ _ _ _
  have hη : IsOpen (η.ker : Set L) :=
    HaarModulus.isOpen_ker_closedInverseHalfCharacter _ _ _ _
  have hχη : χ.comp e.toMonoidHom = η := by
    apply MonoidHom.ext
    intro l
    exact leviInverseHalfCharacter_eq hM hNM hLM h.levi_le_normalizer hN l
  let F : SmoothRep.{0, uG, uV} ℂ M ⥤ SmoothRep.{0, uG, uV} ℂ (L.subgroupOf M) :=
    Jacquet.Localization.smoothFunctor (N.subgroupOf M) 1 (L.subgroupOf M)
      h.levi_le_normalizer (Jacquet.Localization.isInvariant_one _ _ h.levi_le_normalizer)
  change (F ⋙ SmoothRep.twistFunctor χ hχ) ⋙ SmoothRep.pullbackFunctor e ≅
    F ⋙ SmoothRep.pullbackFunctor e ⋙ SmoothRep.twistFunctor η hη
  refine Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F ?_
  exact Derivative.DeterminantTwist.pullbackTwistIso e.toMonoidHom e.continuous χ hχ
      (hχ.preimage e.continuous) ≪≫
    Functor.isoWhiskerLeft _ (Derivative.DeterminantTwist.twistCongrIso hχη _ hη)

end Langlands.Aubert.General
