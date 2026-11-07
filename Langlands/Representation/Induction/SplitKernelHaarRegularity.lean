import Langlands.Representation.Induction.SplitKernelEquivariant
import Langlands.Representation.Aubert.General.CorrectedOrbitJacquet
import Langlands.Representation.Twist.AdmissibilityProof

/-! Open kernels for the actual split-kernel Haar ratio and its coefficient image. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Induction

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

universe uG uL uR uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {L : Type uL} [Group L]
variable (r : G →* L) (s : L →* G) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)

/-- The section as a homomorphism into the actual kernel normalizer. -/
def splitKernelNormalizerSection : L →* Subgroup.normalizer (r.ker : Set G) where
  toFun l := ⟨s l, by simp [Subgroup.normalizer_eq_top]⟩
  map_one' := Subtype.ext s.map_one
  map_mul' l k := Subtype.ext (s.map_mul l k)

/-- The same section normalizes the actual kernel intersection in the ambient group. -/
def splitKernelIntersectionNormalizerSection :
    L →* Subgroup.normalizer ((r.ker ⊓ H : Subgroup G) : Set G) where
  toFun l := ⟨s l, Subgroup.inf_normalizer_le_normalizer_inf
    ⟨by simp [Subgroup.normalizer_eq_top],
      Subgroup.le_normalizer (hsH l)⟩⟩
  map_one' := Subtype.ext s.map_one
  map_mul' l k := Subtype.ext (s.map_mul l k)

/-- Remove the nested subtype from the kernel intersection, without changing its value. -/
def splitKernelIntersectionAmbientEquiv :
    (H.comap r.ker.subtype) ≃ₜ* (r.ker ⊓ H : Subgroup G) where
  toFun x := ⟨(x.val : G), x.val.property, x.property⟩
  invFun x := ⟨⟨x, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

section Haar

variable [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [LocallyCompactSpace r.ker]
variable [MeasurableSpace r.ker] [BorelSpace r.ker]
variable [MeasurableSpace (H.comap r.ker.subtype)] [BorelSpace (H.comap r.ker.subtype)]
variable (hN : IsClosed (r.ker : Set G)) (hH : IsClosed (H : Set G))

/-- The original inverse-conjugation Haar ratio is the forward kernel modulus
divided by the forward intersection modulus, both pulled back along the section. -/
theorem splitKernelHaarRatio_eq_normalizerCharacters :
    splitKernelHaarRatio r s H hsH hH =
      ((HaarModulus.closedNormalizerCharacter r.ker hN).comp
        (splitKernelNormalizerSection r s)) /
      ((HaarModulus.closedNormalizerCharacter (r.ker ⊓ H) (hN.inter hH)).comp
        (splitKernelIntersectionNormalizerSection r s H hsH)) := by
  apply MonoidHom.ext
  intro l
  let : LocallyCompactSpace (H.comap r.ker.subtype) :=
    (isClosed_splitKernelIntersection r H hH).locallyCompactSpace
  have hn : mulEquivHaarChar (splitKernelConjugation r s l) =
      (HaarModulus.closedNormalizerCharacter r.ker hN
        (splitKernelNormalizerSection r s l) : ℝ≥0)⁻¹ := by
    rw [Aubert.General.CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter
      r.ker hN (splitKernelNormalizerSection r s l)⁻¹
      (ContinuousMulEquiv.refl r.ker) _ (fun x => by
        simp only [ContinuousMulEquiv.refl_apply, Subgroup.coe_inv, inv_inv]
        exact splitKernelConjugation_apply r s l x)]
    rw [map_inv, Units.val_inv_eq_inv_val]
  have hi : mulEquivHaarChar (splitKernelIntersectionConjugation r s H hsH l) =
      (HaarModulus.closedNormalizerCharacter (r.ker ⊓ H) (hN.inter hH)
        (splitKernelIntersectionNormalizerSection r s H hsH l) : ℝ≥0)⁻¹ := by
    rw [Aubert.General.CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter
      (r.ker ⊓ H) (hN.inter hH) (splitKernelIntersectionNormalizerSection r s H hsH l)⁻¹
      (splitKernelIntersectionAmbientEquiv r H) _ (fun x => by
        simp only [Subgroup.coe_inv, inv_inv]
        exact splitKernelConjugation_apply r s l x.val)]
    rw [map_inv, Units.val_inv_eq_inv_val]
  apply Units.ext
  rw [splitKernelHaarRatio_apply]
  change mulEquivHaarChar (splitKernelIntersectionConjugation r s H hsH l) /
    mulEquivHaarChar (splitKernelConjugation r s l) = _
  rw [hi, hn, inv_div_inv]
  rfl

end Haar

section Regularity

variable [NonarchimedeanGroup G]
variable [LocallyCompactSpace G] [LocallyCompactSpace r.ker]
variable [MeasurableSpace r.ker] [BorelSpace r.ker]
variable [MeasurableSpace (H.comap r.ker.subtype)] [BorelSpace (H.comap r.ker.subtype)]
variable (hN : IsClosed (r.ker : Set G)) (hH : IsClosed (H : Set G))
variable [TopologicalSpace L] [IsTopologicalGroup L] (hs : Continuous s)

include hN hs in
/-- The exact split-kernel Haar ratio has open kernel for a continuous section. -/
theorem isOpen_ker_splitKernelHaarRatio :
    IsOpen ((splitKernelHaarRatio r s H hsH hH).ker : Set L) := by
  let χN := (HaarModulus.closedNormalizerCharacter r.ker hN).comp
    (splitKernelNormalizerSection r s)
  let χI := (HaarModulus.closedNormalizerCharacter (r.ker ⊓ H) (hN.inter hH)).comp
    (splitKernelIntersectionNormalizerSection r s H hsH)
  have hn : IsOpen (χN.ker : Set L) :=
    (HaarModulus.isOpen_ker_closedNormalizerCharacter r.ker hN).preimage
      (hs.subtype_mk _)
  have hi : IsOpen (χI.ker : Set L) :=
    (HaarModulus.isOpen_ker_closedNormalizerCharacter (r.ker ⊓ H) (hN.inter hH)).preimage
      (hs.subtype_mk _)
  apply Subgroup.isOpen_mono (H₁ := χN.ker ⊓ χI.ker) (fun l hl => ?_) (hn.inter hi)
  change splitKernelHaarRatio r s H hsH hH l = 1
  rw [splitKernelHaarRatio_eq_normalizerCharacters r s H hsH hN hH]
  change χN l / χI l = 1
  rw [show χN l = 1 from hl.1, show χI l = 1 from hl.2, div_one]

variable (R : Type uR) [CommRing R] [Algebra ℂ R]

include hN hs in
/-- No topology or injectivity of the coefficient map is needed for the
constant coefficient image of the exact Haar character to have open kernel. -/
theorem isOpen_ker_splitKernelHaarCoefficientCharacter :
    IsOpen ((MonoidHom.comp
      (Units.map (RingHom.toMonoidHom (algebraMap ℂ R)))
      (Jacquet.complexCharacter (splitKernelHaarRatio r s H hsH hH))).ker : Set L) := by
  apply Subgroup.isOpen_mono
    (H₁ := (splitKernelHaarRatio r s H hsH hH).ker) ?_
    (isOpen_ker_splitKernelHaarRatio r s H hsH hN hH hs)
  intro l hl
  change (Units.map (RingHom.toMonoidHom (algebraMap ℂ R)))
    (Jacquet.complexCharacter (splitKernelHaarRatio r s H hsH hH) l) = 1
  change splitKernelHaarRatio r s H hsH hH l = 1 at hl
  simp [Jacquet.complexCharacter, hl]

/-- The coefficient character bundled with the proved open-kernel property. -/
def splitKernelHaarSmoothCharacter : SmoothCharacter R L where
  toMonoidHom := MonoidHom.comp
    (Units.map (RingHom.toMonoidHom (algebraMap ℂ R)))
    (Jacquet.complexCharacter (splitKernelHaarRatio r s H hsH hH))
  isOpen_ker := isOpen_ker_splitKernelHaarCoefficientCharacter r s H hsH hN hH hs R

variable {V : Type uV} [AddCommGroup V] [Module R V] (ρ : Representation R L V)

theorem isSmooth_splitKernelHaarTwist_iff :
    IsSmooth (twist (splitKernelHaarSmoothCharacter r s H hsH hN hH hs R).toMonoidHom ρ) ↔
      IsSmooth ρ :=
  isSmooth_twist_iff _ ρ
    (splitKernelHaarSmoothCharacter r s H hsH hN hH hs R).isOpen_ker

theorem isAdmissible_splitKernelHaarTwist_iff [IsNoetherianRing R] :
    IsAdmissible (twist (splitKernelHaarSmoothCharacter r s H hsH hN hH hs R).toMonoidHom ρ) ↔
      IsAdmissible ρ :=
  isAdmissible_twist_iff _ ρ
    (splitKernelHaarSmoothCharacter r s H hsH hN hH hs R).isOpen_ker

end Regularity

end Langlands.Induction
