import Langlands.Representation.Parabolic.FiniteLengthGrothendieckProof
import Langlands.Representation.CuspidalSupport.FiniteBlockShapes

/-!
# The unadjusted alternating induction–Jacquet operator

The actual normalized parabolic induction and Jacquet functors induce named
integer-linear maps of the exact finite-length smooth Grothendieck groups, by the
published generic construction together with the published finite-length
preservation and exactness theorems. The unadjusted alternating operator of
Aubert's Definition 1.5 is the signed sum, over every ordered positive block
shape `B` of rank `n`, of induction after Jacquet restriction, with sign
`(-1) ^ (n - B.length)`. No support-dependent sign adjustment is made.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Parabolic

universe uF uV

open SmoothRep

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The map of exact finite-length Grothendieck groups induced by actual
normalized parabolic induction from the block-shape Levi to `GL_n`, with
saturated carriers `Type (max uF uV)`. It is the published generic functor map,
supplied with the published finite-length preservation and exactness theorems. -/
def normalizedInductionK0 {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier :=
  letI := T.topology
  B.finiteLengthMapToGeneralLinear F.Carrier
    (T.normalizedParabolicInductionFunctor.{uF, max uF uV} B)
    ((normalizedParabolicFiniteLength.{uF, max uF uV} F T).1 n B)
    (FiniteLengthGrothendieckAssembly.normalizedInductionFunctor_preservesShortExact F T B)

/-- The map of exact finite-length Grothendieck groups induced by the actual
normalized Jacquet functor from `GL_n` to the block-shape Levi, with saturated
carriers `Type (max uF uV)`. It is the published generic functor map, supplied
with the published finite-length preservation and exactness theorems. -/
def normalizedJacquetK0 {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
      B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier :=
  letI := T.topology
  B.finiteLengthMapFromGeneralLinear F.Carrier
    (T.normalizedJacquetFunctor.{uF, max uF uV} B)
    ((normalizedParabolicFiniteLength.{uF, max uF uV} F T).2 n B)
    (FiniteLengthGrothendieckAssembly.normalizedJacquetFunctor_preservesShortExact F T B)

section Induction

variable {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Actual normalized induction of a finite-length smooth Levi representation has
finite length, by the published finite-length theorem. -/
theorem normalizedInductionK0_hasFiniteLength :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)),
      A.HasFiniteLength →
        ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A).HasFiniteLength :=
  (normalizedParabolicFiniteLength.{uF, max uF uV} F T).1 n B

/-- The named induction map sends the class of an actual finite-length smooth
Levi representation to the class of its actual normalized induction, for every
choice of the output finite-length proof. -/
theorem normalizedInductionK0_finiteLengthClass :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)) (hA : A.HasFiniteLength)
      (hOut : ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A).HasFiniteLength),
      normalizedInductionK0.{uF, uV} F T B (B.finiteLengthClass F.Carrier A hA) =
        GeneralLinear.finiteLengthClass n F.Carrier
          ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A) hOut := by
  let := T.topology
  intro A hA _
  exact B.finiteLengthMapToGeneralLinear_finiteLengthClass F.Carrier _ _ _ A hA

/-- The named induction map has the generator property of the published
induction clause. -/
theorem normalizedInductionK0_spec :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)) (hA : A.HasFiniteLength),
      ∃ hOut : ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A).HasFiniteLength,
        normalizedInductionK0.{uF, uV} F T B (B.finiteLengthClass F.Carrier A hA) =
          GeneralLinear.finiteLengthClass n F.Carrier
            ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A) hOut := by
  let := T.topology
  intro A hA
  exact ⟨normalizedInductionK0_hasFiniteLength F T B A hA,
    normalizedInductionK0_finiteLengthClass F T B A hA _⟩

/-- The named induction map is the unique integer-linear map with the generator
property: it is the unique map of the published induction clause. -/
theorem normalizedInductionK0_eq_iff :
    letI := T.topology
    ∀ i : B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
        GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier,
      i = normalizedInductionK0.{uF, uV} F T B ↔
        ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)) (hA : A.HasFiniteLength),
          ∃ hOut : ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A).HasFiniteLength,
            i (B.finiteLengthClass F.Carrier A hA) =
              GeneralLinear.finiteLengthClass n F.Carrier
                ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj A) hOut := by
  let := T.topology
  intro i
  constructor
  · rintro rfl
    exact normalizedInductionK0_spec F T B
  · intro hi
    exact ((normalizedParabolicGrothendieck.{uF, uV} F T).1 n B).unique hi
      (normalizedInductionK0_spec F T B)

end Induction

section Jacquet

variable {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The actual normalized Jacquet module of a finite-length smooth `GL_n`
representation has finite length, by the published finite-length theorem. -/
theorem normalizedJacquetK0_hasFiniteLength :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      A.HasFiniteLength →
        ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A).HasFiniteLength :=
  (normalizedParabolicFiniteLength.{uF, max uF uV} F T).2 n B

/-- The named Jacquet map sends the class of an actual finite-length smooth
`GL_n` representation to the class of its actual normalized Jacquet module, for
every choice of the output finite-length proof. -/
theorem normalizedJacquetK0_finiteLengthClass :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (hA : A.HasFiniteLength)
      (hOut : ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A).HasFiniteLength),
      normalizedJacquetK0.{uF, uV} F T B (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
        B.finiteLengthClass F.Carrier
          ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A) hOut := by
  let := T.topology
  intro A hA _
  exact B.finiteLengthMapFromGeneralLinear_finiteLengthClass F.Carrier _ _ _ A hA

/-- The named Jacquet map has the generator property of the published Jacquet
clause. -/
theorem normalizedJacquetK0_spec :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (hA : A.HasFiniteLength),
      ∃ hOut : ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A).HasFiniteLength,
        normalizedJacquetK0.{uF, uV} F T B (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
          B.finiteLengthClass F.Carrier
            ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A) hOut := by
  let := T.topology
  intro A hA
  exact ⟨normalizedJacquetK0_hasFiniteLength F T B A hA,
    normalizedJacquetK0_finiteLengthClass F T B A hA _⟩

/-- The named Jacquet map is the unique integer-linear map with the generator
property: it is the unique map of the published Jacquet clause. -/
theorem normalizedJacquetK0_eq_iff :
    letI := T.topology
    ∀ r : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
        B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier,
      r = normalizedJacquetK0.{uF, uV} F T B ↔
        ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
          (hA : A.HasFiniteLength),
          ∃ hOut : ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A).HasFiniteLength,
            r (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
              B.finiteLengthClass F.Carrier
                ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A) hOut := by
  let := T.topology
  intro r
  constructor
  · rintro rfl
    exact normalizedJacquetK0_spec F T B
  · intro hr
    exact ((normalizedParabolicGrothendieck.{uF, uV} F T).2 n B).unique hr
      (normalizedJacquetK0_spec F T B)

end Jacquet

end Langlands.Parabolic

namespace Langlands.Aubert

universe uF uV

open Parabolic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The unadjusted alternating induction–Jacquet operator of Aubert's
Definition 1.5 on the exact finite-length smooth Grothendieck group of `GL_n`:
the sum, over every ordered positive block shape `B` of rank `n` enumerated by
`Fintype.ofFinite`, of `(-1) ^ (n - B.length)` times normalized induction after
the normalized Jacquet map, in the integer module of linear endomorphisms. -/
def alternatingOperator (n : ℕ) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier :=
  letI := T.topology
  letI : Fintype (GeneralLinear.BlockShape n) := Fintype.ofFinite _
  ∑ B : GeneralLinear.BlockShape n,
    ((-1 : ℤ) ^ (n - B.length)) •
      (normalizedInductionK0.{uF, uV} F T B).comp (normalizedJacquetK0.{uF, uV} F T B)

/-- The defining sum, for any finite enumeration of the block shapes of rank `n`. -/
theorem alternatingOperator_eq_sum (n : ℕ) [Fintype (GeneralLinear.BlockShape n)] :
    letI := T.topology
    alternatingOperator.{uF, uV} F T n =
      ∑ B : GeneralLinear.BlockShape n,
        ((-1 : ℤ) ^ (n - B.length)) •
          (normalizedInductionK0.{uF, uV} F T B).comp (normalizedJacquetK0.{uF, uV} F T B) := by
  let := T.topology
  unfold alternatingOperator
  congr
  exact Subsingleton.elim _ _

/-- The value of the alternating operator on an arbitrary virtual class. -/
theorem alternatingOperator_apply (n : ℕ) [Fintype (GeneralLinear.BlockShape n)] :
    letI := T.topology
    ∀ x : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier,
      alternatingOperator.{uF, uV} F T n x =
        ∑ B : GeneralLinear.BlockShape n,
          ((-1 : ℤ) ^ (n - B.length)) •
            normalizedInductionK0.{uF, uV} F T B (normalizedJacquetK0.{uF, uV} F T B x) := by
  let := T.topology
  intro x
  rw [alternatingOperator_eq_sum, LinearMap.sum_apply]
  rfl

/-- Normalized induction after the normalized Jacquet module of an actual
finite-length smooth `GL_n` representation has finite length, by the published
finite-length theorem applied twice. -/
theorem normalizedInductionJacquet_hasFiniteLength {n : ℕ} :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      A.HasFiniteLength → ∀ B : GeneralLinear.BlockShape n,
        ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj
          ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A)).HasFiniteLength := by
  let := T.topology
  intro A hA B
  exact normalizedInductionK0_hasFiniteLength.{uF, uV} F T B _
    (normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B A hA)

/-- The generator formula, for every choice of the output finite-length proofs:
on the class of an actual finite-length smooth `GL_n` representation, the
alternating operator is the signed sum of the classes of its actual normalized
inductions after normalized Jacquet modules. -/
theorem alternatingOperator_finiteLengthClass_of_hasFiniteLength (n : ℕ)
    [Fintype (GeneralLinear.BlockShape n)] :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (hA : A.HasFiniteLength)
      (hOut : ∀ B : GeneralLinear.BlockShape n,
        ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj
          ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A)).HasFiniteLength),
      alternatingOperator.{uF, uV} F T n (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
        ∑ B : GeneralLinear.BlockShape n,
          ((-1 : ℤ) ^ (n - B.length)) •
            GeneralLinear.finiteLengthClass n F.Carrier
              ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj
                ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A)) (hOut B) := by
  let := T.topology
  intro A hA hOut
  rw [alternatingOperator_apply]
  refine Finset.sum_congr rfl fun B _ => ?_
  have hJ := normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B A hA
  rw [normalizedJacquetK0_finiteLengthClass F T B A hA hJ,
    normalizedInductionK0_finiteLengthClass F T B _ hJ (hOut B)]

/-- The generator formula with the output finite-length proofs supplied by the
published finite-length theorem. -/
theorem alternatingOperator_finiteLengthClass (n : ℕ) [Fintype (GeneralLinear.BlockShape n)] :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (hA : A.HasFiniteLength),
      alternatingOperator.{uF, uV} F T n (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
        ∑ B : GeneralLinear.BlockShape n,
          ((-1 : ℤ) ^ (n - B.length)) •
            GeneralLinear.finiteLengthClass n F.Carrier
              ((T.normalizedParabolicInductionFunctor.{uF, max uF uV} B).obj
                ((T.normalizedJacquetFunctor.{uF, max uF uV} B).obj A))
              (normalizedInductionJacquet_hasFiniteLength.{uF, uV} F T A hA B) := by
  let := T.topology
  intro A hA
  exact alternatingOperator_finiteLengthClass_of_hasFiniteLength F T n A hA _

end Langlands.Aubert
