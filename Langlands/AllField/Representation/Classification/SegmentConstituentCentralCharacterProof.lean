import Langlands.Representation.Classification.SegmentConstituentCentralCharacterProof
import Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement
import Langlands.AllField.Representation.Induction.BlockFactors
/-!
# The scalar action on segment inductions and their constituents

Ambient scalar matrices lie in every standard block Levi as constant block
scalars, the explicit block modulus is trivial on them, and normalized
parabolic induction acts on them through the inducing Levi representation.
The scalar characters of block factors multiply in their tensor product. For
the segment factors `ν^i A` the determinant powers add up to the exponent
`m (m - 1) / 2`, for both orders of the factors. Constituents inherit the
scalar character through their actual injective or surjective intertwiners.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.AllField

universe uF uV

namespace GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape hiding HasBlockIwahoriFactorization IsWeaklyContracting
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear



end GeneralLinear.BlockShape

namespace Classification
open Langlands.Classification
open Langlands.AllField.Classification

end Classification

end Langlands.AllField

namespace Langlands.LocalFieldData
universe uF uV
open Langlands.LocalFieldData

variable {F : Type uF} [Field F] (T : LocalFieldData F)

section Modulus


end Modulus

section Induced

variable {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- A scalar character of the inducing Levi representation on the constant block
scalars is the scalar character of its normalized parabolic induction. -/
theorem hasScalarCharacter_normalizedParabolicInduced {V : Type uV} [AddCommGroup V]
    [Module ℂ V] {σ : Representation ℂ (B.Levi F) V} {ω : Fˣ →* ℂˣ}
    (h : Classification.HasScalarCharacter σ (B.scalarLevi F) ω) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Classification.HasScalarCharacter (T.normalizedParabolicInduced B σ)
      GeneralLinear.scalar ω := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro a f
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hx : x * GeneralLinear.scalar a =
      ((B.scalarParabolic F a : B.parabolic F) : GeneralLinear n F) *
        x := by
    rw [B.coe_scalarParabolic]
    exact (Matrix.GeneralLinearGroup.scalar_commute a x).symm
  change Induction.eval (B.parabolic F)
      (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F))) f
      (x * GeneralLinear.scalar a) =
    (ω a : ℂ) • Induction.eval (B.parabolic F)
      (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F))) f x
  rw [hx, T.normalizedParabolicInduced_covariant B σ f, B.leviProjection_scalarParabolic,
    show T.leviModulus B (B.scalarLevi F a) = 1 from T.leviModulus_scalar B a,
    Units.val_one, NNReal.sqrt_one, NNReal.coe_one,
    Complex.ofReal_one, one_smul]
  exact h a _

/-- If each block factor `σ i` has scalar character `c i`, then
`i(σ_1, …, σ_r)` has scalar character `∏ i, c i`. -/
theorem hasScalarCharacter_normalizedProductInduced {V : Fin B.length → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)}
    {c : Fin B.length → (Fˣ →* ℂˣ)}
    (h : ∀ i, Classification.HasScalarCharacter (σ i) GeneralLinear.scalar (c i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Classification.HasScalarCharacter (T.normalizedProductInduced B σ)
      GeneralLinear.scalar (∏ i, c i) :=
  T.hasScalarCharacter_normalizedParabolicInduced B
    (GeneralLinear.BlockShape.hasScalarCharacter_blockTensor h)

end Induced

section Segment


end Segment

end Langlands.LocalFieldData

namespace Langlands.AllField
universe uF uV

namespace Classification
open Langlands.Classification
open Langlands.AllField.Classification


end Classification

end Langlands.AllField
