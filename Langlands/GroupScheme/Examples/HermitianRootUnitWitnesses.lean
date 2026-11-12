import Langlands.GroupScheme.Examples.HermitianRootReflectionAction
import Langlands.GroupScheme.Examples.HermitianRootGroupScheme

/-! # Canonical unit witnesses for anisotropic diagonal Hermitian forms -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.HermitianRoot

namespace DiagonalForm

variable {A : Type u} [CommRing A] {c : SU3Root.RingInvolution A}
  {ι : Type v} (H : DiagonalForm c ι)

/-- The underlying weights determine all their unit witnesses uniquely. -/
theorem unitWitnesses_eq (w v : ι → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i)
    (hv : ∀ i, (v i : A) = H.weight i) : w = v := by
  funext i
  exact Units.ext ((hw i).trans (hv i).symm)

section Field

variable {L : Type u} [Field L] {d : SU3Root.RingInvolution L}
  [Fintype ι] (H : DiagonalForm d ι)

/-- A coordinate vector detects the corresponding diagonal coefficient. -/
theorem pairing_single_one [DecidableEq ι] (i : ι) :
    H.pairing (Pi.single i 1) (Pi.single i 1) = H.weight i := by
  simp [pairing, Pi.single_apply]

/-- An anisotropic diagonal Hermitian form has no zero diagonal coefficient. -/
theorem weight_ne_zero (hH : H.IsAnisotropic) (i : ι) : H.weight i ≠ 0 := by
  classical
  intro hi
  have hz := hH (Pi.single i 1) ((H.pairing_single_one i).trans hi)
  have he := congrFun hz i
  simp at he

/-- The canonical units obtained from the nonzero anisotropic weights. -/
def anisotropicUnits (hH : H.IsAnisotropic) : ι → Lˣ :=
  fun i => Units.mk0 (H.weight i) (H.weight_ne_zero hH i)

@[simp] theorem anisotropicUnits_val (hH : H.IsAnisotropic) (i : ι) :
    (H.anisotropicUnits hH i : L) = H.weight i := rfl

/-- Anisotropy supplies the unit witnesses required by the group-scheme model. -/
theorem exists_unitWitnesses (hH : H.IsAnisotropic) :
    ∃ w : ι → Lˣ, ∀ i, (w i : L) = H.weight i :=
  ⟨H.anisotropicUnits hH, H.anisotropicUnits_val hH⟩

/-- Every supplied unit witness equals the canonical anisotropic witness. -/
theorem unitWitnesses_eq_anisotropicUnits (hH : H.IsAnisotropic)
    (w : ι → Lˣ) (hw : ∀ i, (w i : L) = H.weight i) :
    w = H.anisotropicUnits hH :=
  H.unitWitnesses_eq w (H.anisotropicUnits hH) hw (H.anisotropicUnits_val hH)

end Field
end DiagonalForm

namespace SchemeModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (SU3Root.fieldInvolution k L) Middle)

/-- The actual group scheme is independent of its supplied unit witnesses. -/
theorem groupScheme_eq_of_unitWitnesses
    (w v : Middle → Lˣ)
    (hw : ∀ i, (w i : L) = H.weight i)
    (hv : ∀ i, (v i : L) = H.weight i) :
    groupScheme k L H w hw = groupScheme k L H v hv := by
  have h := H.unitWitnesses_eq w v hw hv
  subst v
  rfl

/-- The anisotropic Hermitian group model with its canonical weight units. -/
def anisotropicGroupScheme (hH : H.IsAnisotropic) :
    GroupScheme (Spec (CommRingCat.of k)) :=
  groupScheme k L H (H.anisotropicUnits hH) (H.anisotropicUnits_val hH)

/-- Canonical weight units produce the same actual model as any supplied witnesses. -/
theorem groupScheme_eq_anisotropicGroupScheme (hH : H.IsAnisotropic)
    (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i) :
    groupScheme k L H w hw = anisotropicGroupScheme k L H hH :=
  groupScheme_eq_of_unitWitnesses k L H w (H.anisotropicUnits hH) hw
    (H.anisotropicUnits_val hH)

/-- Identification with an anisotropic model does not require choosing weight units. -/
theorem exists_model_iso_iff (G : GroupScheme (Spec (CommRingCat.of k)))
    (hH : H.IsAnisotropic) :
    (∃ (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i),
      Nonempty (G ≅ groupScheme k L H w hw)) ↔
        Nonempty (G ≅ anisotropicGroupScheme k L H hH) := by
  constructor
  · rintro ⟨w, hw, he⟩
    simpa only [groupScheme_eq_anisotropicGroupScheme k L H hH w hw] using he
  · intro he
    exact ⟨H.anisotropicUnits hH, H.anisotropicUnits_val hH, he⟩

end SchemeModel
end Langlands.GroupScheme.HermitianRoot
