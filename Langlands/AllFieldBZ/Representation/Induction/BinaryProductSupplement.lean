import Langlands.AllFieldBZ.Representation.Induction.BinaryProduct

/-!
# All-field port of the unit of `Langlands.Representation.Induction.BinaryProduct`

The one-dimensional unit of the binary normalized product and the left and right
unit equivalences, over an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). These declarations of the original module
`Langlands.Representation.Induction.BinaryProduct` are not part of its port
`Langlands.AllFieldBZ.Representation.Induction.BinaryProduct`. See the paired Markdown.
-/

noncomputable section

open CategoryTheory

namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData

open Langlands.GeneralLinear Langlands.BinaryTensor

universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData) {a b : ℕ}

/-- The genuine one-dimensional unit: `ULift ℂ` with the trivial action of
`GL_0(F)`. -/
def binaryProductUnit :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) :=
  letI := T.topology
  SmoothRep.of (Representation.trivial ℂ (GeneralLinear 0 F.Carrier) (ULift.{uV} ℂ))
    isSmooth_trivial

theorem binaryProductUnit_representation :
    letI := T.topology
    (T.binaryProductUnit.{uF, uV}).representation =
      Representation.trivial ℂ (GeneralLinear 0 F.Carrier) (ULift.{uV} ℂ) := rfl

theorem finrank_binaryProductUnit :
    letI := T.topology
    Module.finrank ℂ (T.binaryProductUnit.{uF, uV}) = 1 :=
  (ULift.moduleEquiv (R := ℂ) (M := ℂ)).finrank_eq.trans (Module.finrank_self ℂ)

/-- The left unit equivalence `1 × B ≃ B`, with the rank cast `GL_{0+b} = GL_b`
and the lift of `B` to the output universe. -/
def binaryProductLeftUnitEquiv
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor 0 b).obj (T.binaryProductUnit, B)).representation.Equiv
      (lift.{uF, uV, uF} (B.representation.comp
        (GeneralLinear.reindex (R := F.Carrier) (finCongr (Nat.zero_add b))).toMonoidHom)) :=
  letI := T.topology
  (T.binaryLeftZeroTensorEquiv rfl (T.binaryProductUnit, B)).trans
    ((compEquiv (secondFactorUnitEquiv B.representation) _).trans (liftEquiv _))

/-- The right unit equivalence `A × 1 ≃ A`, with the rank cast `GL_{a+0} = GL_a`
and the lift of `A` to the output universe. -/
def binaryProductRightUnitEquiv
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor a 0).obj (A, T.binaryProductUnit)).representation.Equiv
      (lift.{uF, uV, uF} (A.representation.comp
        (GeneralLinear.reindex (R := F.Carrier) (finCongr (Nat.add_zero a))).toMonoidHom)) :=
  letI := T.topology
  (T.binaryRightZeroTensorEquiv rfl (A, T.binaryProductUnit)).trans
    ((compEquiv (firstFactorUnitEquiv A.representation) _).trans (liftEquiv _))

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
