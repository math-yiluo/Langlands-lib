import Langlands.Representation.Induction.BlockCharacterAbsorption
import Langlands.AllField.Representation.Induction.BlockFactors
import Langlands.AllField.Representation.Induction.Equivalences
/-! # Absorbing the normalizing character into the block factors -/

noncomputable section
open scoped BigOperators

namespace Langlands.AllField.Induction.SmoothCharacter
open Langlands.Induction.SmoothCharacter
open Langlands.AllField.Induction.SmoothCharacter
open Langlands.Induction
open Langlands.AllField.Induction

universe uR uI uG uV



end Langlands.AllField.Induction.SmoothCharacter

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF uV
variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The positive half Levi modulus restricted to the actual `i`th block. -/
def blockHalfModulus (i : Fin B.length) : GeneralLinear (B.size i) F →* ℂˣ :=
  (T.leviHalfModulus B).comp (MonoidHom.mulSingle (fun j => GeneralLinear (B.size j) F) i)

/-- The inverse half character on the actual `i`th block. -/
def blockInverseHalfModulus (i : Fin B.length) : GeneralLinear (B.size i) F →* ℂˣ :=
  (T.blockHalfModulus B i)⁻¹

/-- Coordinate restriction carries its open-kernel certificate. -/
def blockHalfCharacter (i : Fin B.length) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (GeneralLinear (B.size i) F) :=
  letI := T.topology
  (T.leviHalfCharacter B).coordinate i

/-- Inverting the coordinate restriction retains its open-kernel certificate. -/
def blockInverseHalfCharacter (i : Fin B.length) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (GeneralLinear (B.size i) F) :=
  letI := T.topology
  (T.blockHalfCharacter B i).inverse

@[simp] theorem blockHalfCharacter_toMonoidHom (i : Fin B.length) :
    letI := T.topology
    (T.blockHalfCharacter B i).toMonoidHom = T.blockHalfModulus B i := rfl

@[simp] theorem blockInverseHalfCharacter_toMonoidHom (i : Fin B.length) :
    letI := T.topology
    (T.blockInverseHalfCharacter B i).toMonoidHom = T.blockInverseHalfModulus B i := rfl

theorem isOpen_ker_blockHalfModulus (i : Fin B.length) :
    letI := T.topology
    IsOpen ((T.blockHalfModulus B i).ker : Set (GeneralLinear (B.size i) F)) :=
  letI := T.topology
  (T.blockHalfCharacter B i).isOpen_ker

@[simp] theorem blockHalfModulus_apply (i : Fin B.length)
    (g : GeneralLinear (B.size i) F) :
    T.blockHalfModulus B i g = T.leviHalfModulus B (Pi.mulSingle i g) := rfl

@[simp] theorem blockInverseHalfModulus_apply (i : Fin B.length)
    (g : GeneralLinear (B.size i) F) :
    T.blockInverseHalfModulus B i g = (T.blockHalfModulus B i g)⁻¹ := rfl

/-- The coordinate half modulus is one on the actual standard upper unipotent subgroup. -/
@[simp] theorem blockHalfModulus_upperUnipotent (i : Fin B.length)
    (u : GeneralLinear.upperUnipotent (B.size i) F) :
    T.blockHalfModulus B i u.val = 1 := by
  rw [T.blockHalfModulus_apply, T.leviHalfModulus_eq_one]
  apply T.normOneLevi_le_ker_leviModulus B
  rw [T.mem_normOneLevi]
  intro j
  by_cases h : j = i
  · subst j
    simp only [Pi.mulSingle_eq_same]
    have hdet : GeneralLinear.determinant u.val = 1 := by
      apply Units.ext
      change Matrix.det u.val.val = 1
      rw [Matrix.det_of_isUpperTriangular u.property.1]
      simp only [GeneralLinear.UpperUnipotent.entry_diag, Finset.prod_const_one]
    change T.normalizedAbsUnits (GeneralLinear.determinant u.val) = 1
    rw [hdet, map_one]
  · simp [Pi.mulSingle_eq_of_ne h]

variable {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- Positive half twists of the supplied block representations, on their original carriers. -/
def blockHalfTwist (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :=
  fun i => twist (T.blockHalfModulus B i) (σ i)

/-- Inverse half twists of the supplied block representations. -/
def blockInverseHalfTwist
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :=
  fun i => twist (T.blockInverseHalfModulus B i) (σ i)

theorem blockTensor_halfTwist
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    B.blockTensor (T.blockHalfTwist B σ) = twist (T.leviHalfModulus B) (B.blockTensor σ) := by
  let := T.topology
  exact (T.leviHalfCharacter B).external_coordinate_twist σ

theorem blockTensor_inverseHalfTwist
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    B.blockTensor (T.blockInverseHalfTwist B σ) =
      twist (T.leviHalfModulus B)⁻¹ (B.blockTensor σ) := by
  let := T.topology
  exact (T.leviHalfCharacter B).inverse.external_coordinate_twist σ

/-- The actual parabolic covariance actions coincide after positive absorption. -/
theorem halfAbsorptionInducing_eq
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F)) =
      (B.blockTensor (T.blockHalfTwist B σ)).comp (B.leviProjection F) := by
  rw [T.blockTensor_halfTwist]
  rfl

/-- Inverse half twists cancel the normalization in the actual covariance action. -/
theorem inverseHalfAbsorptionInducing_eq
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    twist (T.parabolicHalfModulus B)
        ((B.blockTensor (T.blockInverseHalfTwist B σ)).comp (B.leviProjection F)) =
      (B.blockTensor σ).comp (B.leviProjection F) := by
  rw [T.blockTensor_inverseHalfTwist]
  change (twist (T.leviHalfModulus B) (twist (T.leviHalfModulus B)⁻¹
    (B.blockTensor σ))).comp (B.leviProjection F) = _
  rw [twist_twist_inv]

/-- Identity on tensor values, regarded as an equivalence of the parabolic actions. -/
def halfAbsorptionInducingEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    (twist (T.parabolicHalfModulus B)
      ((B.blockTensor σ).comp (B.leviProjection F))).Equiv
      ((B.blockTensor (T.blockHalfTwist B σ)).comp (B.leviProjection F)) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    change (twist (T.parabolicHalfModulus B)
      ((B.blockTensor σ).comp (B.leviProjection F))) g = _
    rw [T.halfAbsorptionInducing_eq]
    rfl

/-- Identity on tensor values after inverse normalization. -/
def inverseHalfAbsorptionInducingEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    (twist (T.parabolicHalfModulus B)
      ((B.blockTensor (T.blockInverseHalfTwist B σ)).comp (B.leviProjection F))).Equiv
      ((B.blockTensor σ).comp (B.leviProjection F)) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' g := by
    change (twist (T.parabolicHalfModulus B)
      ((B.blockTensor (T.blockInverseHalfTwist B σ)).comp (B.leviProjection F))) g = _
    rw [T.inverseHalfAbsorptionInducing_eq]
    rfl

/-- Absorb positive normalization into the actual block factors. -/
def normalizedProductHalfAbsorptionEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B σ).Equiv
      (Induction.smoothInduced (B.parabolic F)
        ((B.blockTensor (T.blockHalfTwist B σ)).comp (B.leviProjection F))) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Induction.smoothInducedEquiv _ (T.halfAbsorptionInducingEquiv B σ)

/-- Normalize inverse-half-twisted factors to recover the original unnormalized induction. -/
def normalizedProductInverseHalfAbsorptionEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B (T.blockInverseHalfTwist B σ)).Equiv
      (Induction.smoothInduced (B.parabolic F)
        ((B.blockTensor σ).comp (B.leviProjection F))) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Induction.smoothInducedEquiv _ (T.inverseHalfAbsorptionInducingEquiv B σ)

/-- Both directions of positive absorption preserve every value of the induced function. -/
@[simp] theorem normalizedProductHalfAbsorptionEquiv_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F))))
    (g : GeneralLinear n F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ (T.normalizedProductHalfAbsorptionEquiv B σ f) g =
      Induction.eval _ _ f g := rfl

@[simp] theorem normalizedProductHalfAbsorptionEquiv_symm_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F)
        ((B.blockTensor (T.blockHalfTwist B σ)).comp (B.leviProjection F)))
    (g : GeneralLinear n F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ ((T.normalizedProductHalfAbsorptionEquiv B σ).symm f) g =
      Induction.eval _ _ f g := rfl

/-- Both directions of inverse absorption also preserve every function value. -/
@[simp] theorem normalizedProductInverseHalfAbsorptionEquiv_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor (T.blockInverseHalfTwist B σ)).comp (B.leviProjection F))))
    (g : GeneralLinear n F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ (T.normalizedProductInverseHalfAbsorptionEquiv B σ f) g =
      Induction.eval _ _ f g := rfl

@[simp] theorem normalizedProductInverseHalfAbsorptionEquiv_symm_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F)
        ((B.blockTensor σ).comp (B.leviProjection F)))
    (g : GeneralLinear n F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ ((T.normalizedProductInverseHalfAbsorptionEquiv B σ).symm f) g =
      Induction.eval _ _ f g := rfl

end Langlands.LocalFieldData
