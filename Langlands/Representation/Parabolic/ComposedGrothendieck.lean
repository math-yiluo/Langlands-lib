import Langlands.Representation.Aubert.AlternatingOperator
import Langlands.Representation.Aubert.RefinedAlternatingOperator
import Langlands.Representation.Parabolic.RefinementInductionTransitivityProof
import Langlands.Representation.Parabolic.RefinementJacquetTransitivityProof

/-! Exact finite-length K0 transitivity for the actual composed parabolic. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric SmoothRep CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- The actual direct composed induction functor preserves finite length. -/
theorem normalizedComposedInduction_preservesFiniteLength :
    letI := T.topology
    PreservesFiniteLength (T.normalizedComposedInductionFunctor.{uF, uV} B S) := by
  let := T.topology
  intro A hA
  have hI := (normalizedRefinedFiniteLengthExactness.{uF, uV} F T).1 n B S A hA
  have hII := (normalizedParabolicFiniteLength.{uF, max uF uV} F T).1 n B
    ((T.normalizedRefinedInductionFunctor.{uF, uV} B S).obj A) hI
  let e := SmoothRep.equivOfIso
    ((normalizedRefinementInductionTransitivity.{uF, uV} F T B S).choose.app A)
  exact FiniteLengthAssembly.finiteLength_of_injective
    e.symm.toIntertwiningMap e.symm.injective hII

/-- The actual direct composed Jacquet functor preserves finite length. -/
theorem normalizedComposedJacquet_preservesFiniteLength :
    letI := T.topology
    PreservesFiniteLength (T.normalizedComposedJacquetFunctor.{uF, uV} B S) := by
  let := T.topology
  intro A hA
  have hJ := (normalizedParabolicFiniteLength.{uF, uV} F T).2 n B A hA
  have hJJ := (normalizedRefinedFiniteLengthExactness.{uF, uV} F T).2.1 n B S
    ((T.normalizedJacquetFunctor.{uF, uV} B).obj A) hJ
  let e := SmoothRep.equivOfIso
    ((normalizedRefinementJacquetTransitivity.{uF, uV} F T B S).choose.app A)
  exact FiniteLengthAssembly.finiteLength_of_injective
    e.symm.toIntertwiningMap e.symm.injective hJJ

/-- Direct composed induction on exact finite-length K0, defined by induction
in stages and identified below with the actual direct functor on generators. -/
def normalizedComposedInductionK0 :
    letI := T.topology
    SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
        (refinedLevi F.Carrier B S) →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier :=
  letI := T.topology
  (normalizedInductionK0.{uF, uV} F T B).comp
    (normalizedRefinedInductionK0.{uF, uV} F T B S)

/-- Direct composed Jacquet restriction on exact finite-length K0, defined by
restriction in stages and identified below with the actual direct functor. -/
def normalizedComposedJacquetK0 :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
      SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
        (refinedLevi F.Carrier B S) :=
  letI := T.topology
  (normalizedRefinedJacquetK0.{uF, uV} F T B S).comp
    (normalizedJacquetK0.{uF, uV} F T B)

/-- Induction in stages as an equality of maps on all virtual classes. -/
theorem normalizedInductionK0_comp_refinedInductionK0 :
    letI := T.topology
    (normalizedInductionK0.{uF, uV} F T B).comp
        (normalizedRefinedInductionK0.{uF, uV} F T B S) =
      normalizedComposedInductionK0.{uF, uV} F T B S := rfl

/-- Jacquet restriction in stages as an equality on all virtual classes. -/
theorem normalizedRefinedJacquetK0_comp_jacquetK0 :
    letI := T.topology
    (normalizedRefinedJacquetK0.{uF, uV} F T B S).comp
        (normalizedJacquetK0.{uF, uV} F T B) =
      normalizedComposedJacquetK0.{uF, uV} F T B S := rfl

/-- The composed induction map is the class of the actual direct induced object,
for any finite-length proof of that output. -/
theorem normalizedComposedInductionK0_finiteLengthClass :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (refinedLevi F.Carrier B S))
      (hA : A.HasFiniteLength)
      (hOut : ((T.normalizedComposedInductionFunctor.{uF, max uF uV} B S).obj A).HasFiniteLength),
      normalizedComposedInductionK0.{uF, uV} F T B S
          (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
        GeneralLinear.finiteLengthClass n F.Carrier
          ((T.normalizedComposedInductionFunctor.{uF, max uF uV} B S).obj A) hOut := by
  let := T.topology
  intro A hA hOut
  have hI := (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T).1 n B S A hA
  have hII := normalizedInductionK0_hasFiniteLength.{uF, uV} F T B _ hI
  change normalizedInductionK0.{uF, uV} F T B
    (normalizedRefinedInductionK0.{uF, uV} F T B S
      (FiniteLengthGrothendieckGroup.ofRepresentation A hA)) = _
  rw [normalizedRefinedInductionK0_finiteLengthClass F T B S A hA hI,
    normalizedInductionK0_finiteLengthClass F T B _ hI hII]
  exact FiniteLengthGrothendieckGroup.ofObject_eq_of_iso
    ((normalizedRefinementInductionTransitivity.{uF, max uF uV} F T B S).choose.app A)

/-- The composed Jacquet map is the class of the actual full-radical quotient,
for any finite-length proof of that output. -/
theorem normalizedComposedJacquetK0_finiteLengthClass :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hA : A.HasFiniteLength)
      (hOut : ((T.normalizedComposedJacquetFunctor.{uF, max uF uV} B S).obj A).HasFiniteLength),
      normalizedComposedJacquetK0.{uF, uV} F T B S
          (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
        FiniteLengthGrothendieckGroup.ofRepresentation
          ((T.normalizedComposedJacquetFunctor.{uF, max uF uV} B S).obj A) hOut := by
  let := T.topology
  intro A hA hOut
  have hJ := normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B A hA
  have hJJ := (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T).2.1 n B S _ hJ
  change normalizedRefinedJacquetK0.{uF, uV} F T B S
    (normalizedJacquetK0.{uF, uV} F T B
      (GeneralLinear.finiteLengthClass n F.Carrier A hA)) = _
  rw [normalizedJacquetK0_finiteLengthClass F T B A hA hJ,
    normalizedRefinedJacquetK0_finiteLengthClass F T B S _ hJ hJJ]
  exact FiniteLengthGrothendieckGroup.ofObject_eq_of_iso
    ((normalizedRefinementJacquetTransitivity.{uF, max uF uV} F T B S).choose.app A)

/-- The actual direct generator formula characterizes the composed induction
map among all integer-linear maps. -/
theorem normalizedComposedInductionK0_eq_iff :
    letI := T.topology
    ∀ i : SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
        (refinedLevi F.Carrier B S) →ₗ[ℤ]
        GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier,
      i = normalizedComposedInductionK0.{uF, uV} F T B S ↔
        ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (refinedLevi F.Carrier B S))
          (hA : A.HasFiniteLength),
          ∃ hOut : ((T.normalizedComposedInductionFunctor.{uF, max uF uV} B S).obj A).HasFiniteLength,
            i (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
              GeneralLinear.finiteLengthClass n F.Carrier
                ((T.normalizedComposedInductionFunctor.{uF, max uF uV} B S).obj A) hOut := by
  let := T.topology
  intro i
  constructor
  · rintro rfl A hA
    exact ⟨normalizedComposedInduction_preservesFiniteLength F T B S A hA,
      normalizedComposedInductionK0_finiteLengthClass F T B S A hA _⟩
  · intro hi
    apply FiniteLengthGrothendieckGroup.hom_ext_object ℂ (refinedLevi F.Carrier B S)
    intro A
    obtain ⟨hOut, h⟩ := hi A.val A.property
    exact h.trans
      (normalizedComposedInductionK0_finiteLengthClass F T B S A.val A.property hOut).symm

/-- The actual direct generator formula characterizes the composed Jacquet map
among all integer-linear maps. -/
theorem normalizedComposedJacquetK0_eq_iff :
    letI := T.topology
    ∀ r : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
        SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
          (refinedLevi F.Carrier B S),
      r = normalizedComposedJacquetK0.{uF, uV} F T B S ↔
        ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
          (hA : A.HasFiniteLength),
          ∃ hOut : ((T.normalizedComposedJacquetFunctor.{uF, max uF uV} B S).obj A).HasFiniteLength,
            r (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
              FiniteLengthGrothendieckGroup.ofRepresentation
                ((T.normalizedComposedJacquetFunctor.{uF, max uF uV} B S).obj A) hOut := by
  let := T.topology
  intro r
  constructor
  · rintro rfl A hA
    exact ⟨normalizedComposedJacquet_preservesFiniteLength F T B S A hA,
      normalizedComposedJacquetK0_finiteLengthClass F T B S A hA _⟩
  · intro hr
    apply FiniteLengthGrothendieckGroup.hom_ext_object ℂ (GeneralLinear n F.Carrier)
    intro A
    obtain ⟨hOut, h⟩ := hr A.val A.property
    exact h.trans
      (normalizedComposedJacquetK0_finiteLengthClass F T B S A.val A.property hOut).symm

end Langlands.Parabolic
