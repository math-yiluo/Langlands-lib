import Langlands.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.AllField.Representation.Induction.BlockCharacterAbsorption
import Langlands.AllField.Representation.Jacquet.ParabolicSupplement
import Langlands.AllField.Representation.Parabolic.FlattenedRefinementModulusCalculation
import Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement
/-! # Common determinant twists of actual normalized block induction -/

noncomputable section
open scoped BigOperators

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

open Langlands.GeneralLinear hiding SupercuspidalClass

universe uF uV

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B : BlockShape n)
  (χ : letI := T.topology; Induction.SmoothCharacter ℂ Fˣ)
  {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))

private theorem blockTensor_determinant_twist :
    letI := T.topology
    B.blockTensor (fun i => twist (χ.toMonoidHom.comp determinant) (σ i)) =
      twist ((χ.toMonoidHom.comp determinant).comp (B.leviEmbedding F))
        (B.blockTensor σ) := by
  let := T.topology
  let χL : Induction.SmoothCharacter ℂ (B.Levi F) :=
    ⟨(χ.toMonoidHom.comp determinant).comp (B.leviEmbedding F),
      χ.isOpen_ker.preimage ((T.generalLinearDeterminant n).continuous.comp
        (T.blockLeviEmbedding B).continuous)⟩
  have hcoord (i : Fin B.length) :
      (χL.coordinate i).toMonoidHom = χ.toMonoidHom.comp
        (determinant : GeneralLinear (B.size i) F →* Fˣ) := by
    apply MonoidHom.ext
    intro g
    change χ.toMonoidHom (determinant (B.leviEmbedding F (Pi.mulSingle i g))) =
      χ.toMonoidHom (determinant g)
    rw [Langlands.Parabolic.FlattenedModulusCalculation.determinant_leviEmbedding]
    congr 1
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.mulSingle_eq_of_ne hji]
    · simp
  simpa only [hcoord] using χL.external_coordinate_twist σ

/-- The two parabolic covariance actions agree after a common determinant twist. -/
theorem normalizedProductDeterminantTwistInducing_eq :
    letI := T.topology
    twist ((χ.toMonoidHom.comp determinant).comp (B.parabolic F).subtype)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F))) =
      twist (T.parabolicHalfModulus B)
        ((B.blockTensor (fun i => twist (χ.toMonoidHom.comp determinant) (σ i))).comp
          (B.leviProjection F)) := by
  let := T.topology
  rw [blockTensor_determinant_twist T B χ σ]
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change (χ.toMonoidHom (determinant g.val) : ℂ) •
      ((T.parabolicHalfModulus B g : ℂ) • B.blockTensor σ (B.leviProjection F g) v) =
    (T.parabolicHalfModulus B g : ℂ) •
      ((χ.toMonoidHom (determinant
        (B.leviEmbedding F (B.leviProjection F g))) : ℂ) •
          B.blockTensor σ (B.leviProjection F g) v)
  rw [determinant_blockParabolic, Langlands.Parabolic.FlattenedModulusCalculation.determinant_leviEmbedding]
  exact smul_comm _ _ _

/-- Identity on tensor values, with the two actual covariance actions. -/
def normalizedProductDeterminantTwistInducingEquiv :
    letI := T.topology
    (twist ((χ.toMonoidHom.comp determinant).comp (B.parabolic F).subtype)
      (twist (T.parabolicHalfModulus B)
        ((B.blockTensor σ).comp (B.leviProjection F)))).Equiv
      (twist (T.parabolicHalfModulus B)
        ((B.blockTensor (fun i => twist (χ.toMonoidHom.comp determinant) (σ i))).comp
          (B.leviProjection F))) := by
  letI := T.topology
  exact
    { toLinearEquiv := LinearEquiv.refl ℂ _
      isIntertwining' := fun g => by
        change (twist ((χ.toMonoidHom.comp determinant).comp (B.parabolic F).subtype)
          (twist (T.parabolicHalfModulus B)
            ((B.blockTensor σ).comp (B.leviProjection F)))) g = _
        rw [T.normalizedProductDeterminantTwistInducing_eq B χ σ]
        rfl }

/-- Multiply an actual induced function by `χ(det g)`. No smoothness of the
block representations, admissibility, or irreducibility is required. -/
def normalizedProductDeterminantTwistEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (twist (χ.toMonoidHom.comp determinant) (T.normalizedProductInduced B σ)).Equiv
      (T.normalizedProductInduced B
        (fun i => twist (χ.toMonoidHom.comp determinant) (σ i))) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  let χn : Induction.SmoothCharacter ℂ (GeneralLinear n F) :=
    ⟨χ.toMonoidHom.comp determinant,
      χ.isOpen_ker.preimage (T.generalLinearDeterminant n).continuous⟩
  (Induction.smoothInductionTwistEquiv (B.parabolic F) χn
    (twist (T.parabolicHalfModulus B)
      ((B.blockTensor σ).comp (B.leviProjection F)))).trans
    (Induction.smoothInducedEquiv (B.parabolic F)
      (T.normalizedProductDeterminantTwistInducingEquiv B χ σ))

@[simp]
theorem normalizedProductDeterminantTwistEquiv_eval
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F))))
    (g : GeneralLinear n F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ (T.normalizedProductDeterminantTwistEquiv B χ σ f) g =
      (χ.toMonoidHom (determinant g) : ℂ) • Induction.eval _ _ f g := rfl

@[simp]
theorem normalizedProductDeterminantTwistEquiv_symm_eval
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor (fun i => twist (χ.toMonoidHom.comp determinant) (σ i))).comp
            (B.leviProjection F))))
    (g : GeneralLinear n F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval _ _ ((T.normalizedProductDeterminantTwistEquiv B χ σ).symm f) g =
      ((χ.toMonoidHom (determinant g))⁻¹ : ℂˣ) • Induction.eval _ _ f g := rfl

end Langlands.LocalFieldData
