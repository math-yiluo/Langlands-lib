import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Tensor.Finite

/-! Tensor compatibility for normalized induction in an actual product Levi. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

namespace RefinedInductionTensor

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Smooth representations of the actual inner Levi factors. -/
abbrev Factors :=
  letI := T.topology
  ∀ i, SmoothRep.{0, uF, uV} ℂ ((S i).Levi F.Carrier)

variable (A : Factors.{uF, uV} F T B S)

/-- The external tensor action transported to the actual refined subgroup. -/
def inducingRepresentation :=
  letI := T.topology
  (FiniteTensor.external (fun i => (A i).representation)).comp
    (refinedLeviEquiv F.Carrier B S).symm.toMonoidHom

/-- The actual function carrier for one block's normalized induction. -/
abbrev BlockFunctions (i : Fin B.length) :=
  letI := T.topology
  Induction.SmoothFunctions ((S i).parabolic F.Carrier)
    (twist (T.parabolicHalfModulus (S i))
      ((A i).representation.comp ((S i).leviProjection F.Carrier)))

/-- The family of actual normalized induced block actions. -/
def blockRepresentations (i : Fin B.length) :
    Representation ℂ (GeneralLinear (B.size i) F.Carrier)
      (BlockFunctions F T B S A i) :=
  letI := T.topology
  T.normalizedParabolicInduced (S i) (A i).representation

/-- The actual external tensor of the normalized induced block actions. -/
def externalRepresentation :=
  FiniteTensor.external (blockRepresentations F T B S A)

/-- The actual tensor-valued function carrier for refined normalized induction. -/
abbrev RefinedFunctions :=
  letI := T.topology
  Induction.SmoothFunctions (refinedParabolic F.Carrier B S)
    (twist (T.refinedParabolicHalfModulus B S)
      ((inducingRepresentation F T B S A).comp
        (refinedLeviProjection F.Carrier B S)))

/-- Actual normalized induction of the transported external tensor action. -/
def refinedRepresentation :
    Representation ℂ (B.Levi F.Carrier) (RefinedFunctions F T B S A) :=
  T.normalizedRefinedInduced B S (inducingRepresentation F T B S A)

/-- The canonical inverse sends a pure tensor of induced functions to its
pointwise tensor-valued product function. -/
def CanonicalInverse
    (E : (refinedRepresentation F T B S A).Equiv
      (externalRepresentation F T B S A)) : Prop :=
  letI := T.topology
  ∀ (f : ∀ i, BlockFunctions F T B S A i) (g : B.Levi F.Carrier),
    Induction.eval _ _ (E.symm (PiTensorProduct.tprod ℂ f)) g =
      PiTensorProduct.tprod ℂ (fun i => Induction.eval _ _ (f i) (g i))

/-- Existence of an actual equivalence with its canonical inverse prescribed. -/
def Comparison : Prop :=
  Nonempty { E : (refinedRepresentation F T B S A).Equiv
      (externalRepresentation F T B S A) // CanonicalInverse F T B S A E }

end RefinedInductionTensor

/-- Normalized induction in every actual product Levi commutes with the finite
external tensor product, with the pointwise pure-tensor inverse prescribed.
The field and coefficient universes are independent. This is a statement. -/
def RefinedInductionTensorTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
    (A : RefinedInductionTensor.Factors.{uF, uV} F T B S),
    RefinedInductionTensor.Comparison F T B S A

end Langlands.Parabolic
