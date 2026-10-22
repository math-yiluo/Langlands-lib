import Langlands.Group.HaarModulus
import Langlands.Representation.Geometric.GeneralIntersectionNormalizers
import Langlands.Representation.Category.Twist
import Langlands.Representation.Induction.Definitions

/-! Actual Haar correction characters in BZ77 section 5.1. -/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.Geometric.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G]
  (M N U Q : Subgroup G) (w : G)
  (hU : IsClosed (U : Set G)) (hQ : IsClosed (Q : Set G))
  (hMU : M ≤ Subgroup.normalizer U) (hNQ : N ≤ Subgroup.normalizer Q)

section Haar

variable [IsTopologicalGroup G]

/-- The actual Haar modulus of `U`, restricted to `M ∩ w⁻¹(N)`. -/
def intersectionRadicalModulus : intersectionIn M N w →* ℝ≥0ˣ :=
  (HaarModulus.closedNormalizerCharacter U hU).comp
    (intersectionToRadicalNormalizer M N U w hMU)

/-- The actual Haar modulus of `U ∩ w⁻¹(Q)`, on the same intersection Levi. -/
def intersectionCorrectionModulus : intersectionIn M N w →* ℝ≥0ˣ :=
  (HaarModulus.closedNormalizerCharacter (intersectionSource U Q w)
    (isClosed_correctionSubgroup U Q w hU hQ)).comp
      (intersectionToCorrectionNormalizer M N U Q w hMU hNQ)

@[simp]
theorem intersectionRadicalModulus_apply (m : intersectionIn M N w) :
    intersectionRadicalModulus M N U w hU hMU m =
      HaarModulus.closedNormalizerCharacter U hU
        (intersectionToRadicalNormalizer M N U w hMU m) := rfl

@[simp]
theorem intersectionCorrectionModulus_apply (m : intersectionIn M N w) :
    intersectionCorrectionModulus M N U Q w hU hQ hMU hNQ m =
      HaarModulus.closedNormalizerCharacter (intersectionSource U Q w)
        (isClosed_correctionSubgroup U Q w hU hQ)
        (intersectionToCorrectionNormalizer M N U Q w hMU hNQ m) := rfl

/-- Positive half of the radical modulus times inverse half of the correction
subgroup modulus; no character is supplied as an arbitrary input. -/
def haarCorrectionCharacter : intersectionIn M N w →* ℂˣ :=
  Jacquet.complexCharacter
      (Jacquet.positiveHalfCharacter (intersectionRadicalModulus M N U w hU hMU)) *
    Jacquet.inverseHalfCharacter (intersectionCorrectionModulus M N U Q w hU hQ hMU hNQ)

/-- The square roots are the positive real square roots, embedded in `ℂ`. -/
@[simp]
theorem haarCorrectionCharacter_apply (m : intersectionIn M N w) :
    (haarCorrectionCharacter M N U Q w hU hQ hMU hNQ m : ℂ) =
      ((NNReal.sqrt (intersectionRadicalModulus M N U w hU hMU m : ℝ≥0) : ℝ) : ℂ) *
        (((NNReal.sqrt
          (intersectionCorrectionModulus M N U Q w hU hQ hMU hNQ m : ℝ≥0) : ℝ) : ℂ))⁻¹ := by
  simp only [haarCorrectionCharacter, MonoidHom.mul_apply, Units.val_mul,
    Jacquet.complexCharacter_apply, Jacquet.positiveHalfCharacter_apply,
    Jacquet.inverseHalfCharacter_apply]

/-- The square records both the magnitude and the direction of correction. -/
theorem haarCorrectionCharacter_sq (m : intersectionIn M N w) :
    haarCorrectionCharacter M N U Q w hU hQ hMU hNQ m ^ 2 =
      Jacquet.complexCharacter (intersectionRadicalModulus M N U w hU hMU) m *
        (Jacquet.complexCharacter
          (intersectionCorrectionModulus M N U Q w hU hQ hMU hNQ) m)⁻¹ := by
  rw [haarCorrectionCharacter, MonoidHom.mul_apply, mul_pow,
    Jacquet.inverseHalfCharacter_sq]
  congr 1
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Jacquet.complexCharacter_apply,
    Jacquet.positiveHalfCharacter_apply]
  norm_cast
  exact NNReal.sq_sqrt _

end Haar

section Smooth

variable [NonarchimedeanGroup G]

theorem isOpen_ker_intersectionRadicalModulus :
    IsOpen ((intersectionRadicalModulus M N U w hU hMU).ker :
      Set (intersectionIn M N w)) :=
  (HaarModulus.isOpen_ker_closedNormalizerCharacter U hU).preimage
    (continuous_intersectionToRadicalNormalizer M N U w hMU)

theorem isOpen_ker_intersectionCorrectionModulus :
    IsOpen ((intersectionCorrectionModulus M N U Q w hU hQ hMU hNQ).ker :
      Set (intersectionIn M N w)) :=
  (HaarModulus.isOpen_ker_closedNormalizerCharacter (intersectionSource U Q w)
    (isClosed_correctionSubgroup U Q w hU hQ)).preimage
      (continuous_intersectionToCorrectionNormalizer M N U Q w hMU hNQ)

/-- The intersection of the two open Haar kernels lies in the correction kernel. -/
theorem isOpen_ker_haarCorrectionCharacter :
    IsOpen ((haarCorrectionCharacter M N U Q w hU hQ hMU hNQ).ker :
      Set (intersectionIn M N w)) := by
  apply Subgroup.isOpen_mono
    (H₁ := (intersectionRadicalModulus M N U w hU hMU).ker ⊓
      (intersectionCorrectionModulus M N U Q w hU hQ hMU hNQ).ker)
  · intro m hm
    have h₁ : intersectionRadicalModulus M N U w hU hMU m = 1 := hm.1
    have h₂ : intersectionCorrectionModulus M N U Q w hU hQ hMU hNQ m = 1 := hm.2
    change haarCorrectionCharacter M N U Q w hU hQ hMU hNQ m = 1
    apply Units.ext
    simp [haarCorrectionCharacter_apply, h₁, h₂]
  · exact (isOpen_ker_intersectionRadicalModulus M N U w hU hMU).inter
      (isOpen_ker_intersectionCorrectionModulus M N U Q w hU hQ hMU hNQ)

/-- The source correction `ε₁` is obtained with `(M,N,U,Q,w)`.
The target correction `ε₂` uses `(N,M,V,P,w⁻¹)`. -/
def haarCorrectionSmoothCharacter :
    Induction.SmoothCharacter ℂ (intersectionIn M N w) where
  toMonoidHom := haarCorrectionCharacter M N U Q w hU hQ hMU hNQ
  isOpen_ker := isOpen_ker_haarCorrectionCharacter M N U Q w hU hQ hMU hNQ

/-- The actual smooth scalar-twist functor used in the orbit-piece composite. -/
def haarCorrectionTwist :
    SmoothRep.{0, uG, uV} ℂ (intersectionIn M N w) ⥤
      SmoothRep.{0, uG, uV} ℂ (intersectionIn M N w) :=
  SmoothRep.twistFunctor (haarCorrectionCharacter M N U Q w hU hQ hMU hNQ)
    (isOpen_ker_haarCorrectionCharacter M N U Q w hU hQ hMU hNQ)

@[simp]
theorem haarCorrectionTwist_action (A : SmoothRep.{0, uG, uV} ℂ (intersectionIn M N w))
    (m : intersectionIn M N w) (v : A) :
    ((haarCorrectionTwist M N U Q w hU hQ hMU hNQ).obj A).representation m v =
      (haarCorrectionCharacter M N U Q w hU hQ hMU hNQ m : ℂ) • A.representation m v := rfl

end Smooth

end Langlands.Geometric.General
