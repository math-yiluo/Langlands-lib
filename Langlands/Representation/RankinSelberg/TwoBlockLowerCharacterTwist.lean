import Langlands.Representation.Induction.NormalizedProductCharacterTwist
import Langlands.Representation.Induction.OppositeParabolic
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa

/-! # Common determinant twists of actual normalized lower block induction -/

noncomputable section
open scoped BigOperators

namespace Langlands.RankinSelberg.TwoBlockSecondDeformation

open GeneralLinear

universe uF uW

section LowerTwist

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
  (χ : letI := T.topology; Induction.SmoothCharacter ℂ F.Carrierˣ)
  {W : Fin B.length → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (W i))

private theorem blockTensor_twist :
    letI := T.topology
    B.blockTensor (fun i => twist (χ.toMonoidHom.comp determinant) (σ i)) =
      twist ((χ.toMonoidHom.comp determinant).comp (B.leviEmbedding F.Carrier))
        (B.blockTensor σ) := by
  let := T.topology
  let χL : Induction.SmoothCharacter ℂ (B.Levi F.Carrier) :=
    ⟨(χ.toMonoidHom.comp determinant).comp (B.leviEmbedding F.Carrier),
      χ.isOpen_ker.preimage ((T.generalLinearDeterminant n).continuous.comp
        (T.blockLeviEmbedding B).continuous)⟩
  have hcoord (i : Fin B.length) :
      (χL.coordinate i).toMonoidHom = χ.toMonoidHom.comp
        (determinant : GeneralLinear (B.size i) F.Carrier →* F.Carrierˣ) := by
    apply MonoidHom.ext
    intro g
    change χ.toMonoidHom (determinant (B.leviEmbedding F.Carrier (Pi.mulSingle i g))) =
      χ.toMonoidHom (determinant g)
    rw [Langlands.Parabolic.FlattenedModulusCalculation.determinant_leviEmbedding]
    congr 1
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.mulSingle_eq_of_ne hji]
    · simp
  simpa only [hcoord] using χL.external_coordinate_twist σ

/-- Equality of the complete lower parabolic covariance actions, on the
original dependent tensor carrier and with the inverse half-modulus. -/
theorem lowerTwistInducing_eq :
    letI := T.topology
    twist ((χ.toMonoidHom.comp determinant).comp (B.oppositeParabolic F.Carrier).subtype)
        (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.oppositeLeviProjection F.Carrier))) =
      twist (T.oppositeParabolicHalfModulus B)
        ((B.blockTensor (fun i => twist (χ.toMonoidHom.comp determinant) (σ i))).comp
          (B.oppositeLeviProjection F.Carrier)) := by
  let := T.topology
  rw [blockTensor_twist T B χ σ]
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  change (χ.toMonoidHom (determinant g.val) : ℂ) •
      ((T.oppositeParabolicHalfModulus B g : ℂ) •
        B.blockTensor σ (B.oppositeLeviProjection F.Carrier g) v) =
    (T.oppositeParabolicHalfModulus B g : ℂ) •
      ((χ.toMonoidHom (determinant
        (B.leviEmbedding F.Carrier (B.oppositeLeviProjection F.Carrier g))) : ℂ) •
          B.blockTensor σ (B.oppositeLeviProjection F.Carrier g) v)
  rw [TwoBlockConvergence.determinant_oppositeParabolic,
    Langlands.Parabolic.FlattenedModulusCalculation.determinant_leviEmbedding]
  exact smul_comm _ _ _

/-- An actual equivalence of normalized lower-induced representations:
multiply a section at `x` by `χ(det x)`. -/
def lowerTwistEquiv :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (twist (χ.toMonoidHom.comp determinant)
      (T.normalizedOppositeParabolicInduced B (B.blockTensor σ))).Equiv
      (T.normalizedOppositeParabolicInduced B
        (B.blockTensor (fun i => twist (χ.toMonoidHom.comp determinant) (σ i)))) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  let χn : Induction.SmoothCharacter ℂ (GeneralLinear n F.Carrier) :=
    ⟨χ.toMonoidHom.comp determinant,
      χ.isOpen_ker.preimage (T.generalLinearDeterminant n).continuous⟩
  let e :
      (twist ((χ.toMonoidHom.comp determinant).comp (B.oppositeParabolic F.Carrier).subtype)
        (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.oppositeLeviProjection F.Carrier)))).Equiv
        (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => twist (χ.toMonoidHom.comp determinant) (σ i))).comp
            (B.oppositeLeviProjection F.Carrier))) :=
    { toLinearEquiv := LinearEquiv.refl ℂ _
      isIntertwining' := fun g => by
        change (twist
          ((χ.toMonoidHom.comp determinant).comp (B.oppositeParabolic F.Carrier).subtype)
          (twist (T.oppositeParabolicHalfModulus B)
            ((B.blockTensor σ).comp (B.oppositeLeviProjection F.Carrier)))) g = _
        rw [lowerTwistInducing_eq T B χ σ]
        rfl }
  exact (Induction.smoothInductionTwistEquiv (B.oppositeParabolic F.Carrier) χn
    (twist (T.oppositeParabolicHalfModulus B)
      ((B.blockTensor σ).comp (B.oppositeLeviProjection F.Carrier)))).trans
        (Induction.smoothInducedEquiv _ e)

end LowerTwist

end Langlands.RankinSelberg.TwoBlockSecondDeformation
