import Langlands.Representation.Classification.ProductLeviCuspidalJacquetAssembly
import Langlands.Representation.Parabolic.RefinedJacquetTensor
import Langlands.Representation.Parabolic.RefinedInductionTensorProof

/-! # Normalized induction after Jacquet on a product Levi -/

noncomputable section

namespace Langlands.Parabolic.RefinedInductionJacquetTensor

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The blockwise normalized Jacquet objects on the inner Levis. -/
def jacquetFactors
    (π : letI := T.topology
      ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    RefinedInductionTensor.Factors.{uF,uV} F T B S := fun i =>
  (T.normalizedJacquetFunctor.{uF,uV} (S i)).obj (π i)

set_option maxHeartbeats 800000 in
/-- Compare the actual normalized refined induction–Jacquet composite with the
external tensor of the normalized block composites. -/
def equiv {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ (π : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
      ρ.Equiv (B.blockTensor fun i => (π i).representation) →
        (T.normalizedRefinedInduced B S (T.normalizedRefinedJacquet B S ρ)).Equiv
          (RefinedInductionTensor.externalRepresentation F T B S (jacquetFactors T B S π)) := by
  letI := T.topology
  letI := T.leviTopologicalGroup B
  intro π e
  let A := jacquetFactors T B S π
  let eJ : (T.normalizedRefinedJacquet B S ρ).Equiv
      (RefinedInductionTensor.inducingRepresentation F T B S A) :=
    (RefinedJacquetTensor.normalizedRefinedJacquetCongr T B S e).trans
      (RefinedJacquetTensor.jacquetEquiv T B S fun i => (π i).obj)
  exact (ProductLeviCuspidalJacquetAssembly.normalizedRefinedInducedCongr T B S eJ).trans
    (refinedInductionTensor.{uF,uV} p F T n B S A).some.val

end Langlands.Parabolic.RefinedInductionJacquetTensor

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

/-- If a product-Levi representation is equivalent to an external tensor, its
normalized refined induction–Jacquet composite is equivalent to the external
tensor of the normalized induction–Jacquet composites in the individual blocks. -/
def RefinedInductionJacquetTensorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : BlockShape n) (S : BlockRefinement B),
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (B.Levi F.Carrier) V)
      (π : ∀ i, SmoothRep.{0,uF,uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
      Nonempty (ρ.Equiv (B.blockTensor fun i => (π i).representation)) →
        Nonempty ((T.normalizedRefinedInduced B S (T.normalizedRefinedJacquet B S ρ)).Equiv
          (RefinedInductionTensor.externalRepresentation F T B S
            (RefinedInductionJacquetTensor.jacquetFactors T B S π)))

theorem refinedInductionJacquetTensor : RefinedInductionJacquetTensorStatement.{uF,uV} := by
  intro p hp F T n B S
  let := T.topology
  let := T.leviTopologicalGroup B
  intro V _ _ ρ π he
  exact he.map (RefinedInductionJacquetTensor.equiv T B S ρ π)

end Langlands.Parabolic
