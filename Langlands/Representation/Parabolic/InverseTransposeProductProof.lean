import Langlands.Representation.Parabolic.InverseTransposeProductStatement
import Langlands.Representation.Twist.PullbackProof
import Langlands.Representation.Induction.OppositeProductReversalProof
import Langlands.Representation.Induction.InverseTranspose
import Langlands.Representation.Smooth.Transfer.PullbackProof

namespace Langlands.Parabolic

universe uF uV uL

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

private theorem inverseTransposeOppositeReversal :
    letI := T.topology
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape n),
      letI := T.generalLinearTopologicalGroup n
      ∀ (V : Fin B.length → Type uV) [hadd : ∀ i, AddCommGroup (V i)]
        [hmod : ∀ i, Module ℂ (V i)]
        (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)),
        (∀ i, IsSmooth (σ i)) →
        letI : ∀ i : Fin B.reverse.length, AddCommGroup (V i.rev) := fun i => hadd i.rev
        letI : ∀ i : Fin B.reverse.length, Module ℂ (V i.rev) := fun i => hmod i.rev
        Nonempty (Representation.Equiv
          (T.normalizedOppositeParabolicInduced B (B.blockTensor
            (fun i => (σ i).comp
              (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)))
          (T.normalizedProductInduced B.reverse (V := fun i => V i.rev)
            (fun i => (σ i.rev).comp
              (GeneralLinear.inverseTranspose (B.size i.rev) F.Carrier).toMonoidHom))) := by
  let := T.topology
  intro n B
  let := T.generalLinearTopologicalGroup n
  intro V hadd hmod σ hσ
  have hτ (i : Fin B.length) : IsSmooth ((σ i).comp
      (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom) :=
    isSmooth_comp _ (GeneralLinear.continuous_inverseTranspose _ _) (hσ i)
  obtain ⟨E, _, _⟩ := glOppositeProductReversal p F T n B V
    (fun i => (σ i).comp
      (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom) hτ
  exact ⟨E⟩

/-- Compose inverse-transpose precomposition with the actual opposite-product reversal. -/
theorem normalizedProductInverseTranspose :
    NormalizedProductInverseTransposeClause.{uF, uV} F T := by
  let := T.topology
  intro n _hn B
  let := T.generalLinearTopologicalGroup n
  intro V hadd hmod σ hσ
  obtain ⟨E⟩ := inverseTransposeOppositeReversal T n B V σ hσ
  exact ⟨(T.inverseTransposeProductToOppositeEquiv B σ).trans E⟩

/-- Inverse transpose negates the real determinant-power exponent. -/
theorem determinantPowerCharacter_inverseTranspose (n : ℕ) (u : ℝ) :
    (T.determinantPowerCharacter n u).comp
        (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom =
      T.determinantPowerCharacter n (-u) := by
  apply MonoidHom.ext
  intro g
  change realPowerCharacter (T.determinantNorm n) u
      (GeneralLinear.inverseTranspose n F.Carrier g) =
    realPowerCharacter (T.determinantNorm n) (-u) g
  rw [realPowerCharacter_neg, MonoidHom.inv_apply]
  change (positiveUnitsToComplex.comp (Units.map (NNReal.rpowMonoidHom u)))
      (T.determinantNorm n (GeneralLinear.inverseTranspose n F.Carrier g)) = _
  rw [T.determinantNorm_inverseTranspose, map_inv]
  rfl

/-- The determinant twist clause needs neither positive rank nor smoothness. -/
theorem inverseTransposeDeterminantTwist :
    InverseTransposeDeterminantTwistClause.{uF, uV} F T := by
  intro n V _ _ σ u
  rw [twist_comp, determinantPowerCharacter_inverseTranspose]

/-- Reversal and negation preserve strict decrease for every finite sequence. -/
theorem reverseNegateStrictAnti : ReverseNegateStrictAntiClause := by
  intro r u hu i j hij
  exact neg_lt_neg (hu (Fin.rev_lt_rev.mpr hij))

/-- Inverse transpose reverses normalized products and negates determinant exponents. -/
theorem inverseTransposeProduct : InverseTransposeProductStatement.{uF, uV} := by
  refine ⟨?_, reverseNegateStrictAnti⟩
  intro p hp F T
  exact ⟨normalizedProductInverseTranspose T, inverseTransposeDeterminantTwist T⟩

/-- The same proof with an independent lift universe for the block carriers. -/
theorem inverseTransposeProductLift : InverseTransposeProductLiftStatement.{uF, uV, uL} :=
  inverseTransposeProduct.{uF, max uV uL}

end Langlands.Parabolic
