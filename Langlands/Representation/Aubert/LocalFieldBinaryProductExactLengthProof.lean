import Langlands.Representation.Aubert.LocalFieldBinaryProductExactLengthStatement
import Langlands.Representation.Aubert.BinaryProductExactnessProof
import Langlands.Representation.Smooth.FiniteLengthInduction
import Langlands.AllField.Representation.Parabolic.InductionExactnessProof
import Langlands.AllFieldBZ.Representation.Classification.IrreducibleProductFiniteLengthProof

/-!
# Finite length and separate exactness of the local-field binary GL product

Proof of `Langlands.Aubert.LocalFieldBinaryProductExactLengthStatement`. For positive
ranks the binary product is the external tensor product followed by normalized parabolic
induction on the upper block Levi; tensor exactness over `ℂ` and exactness of normalized
induction give separate exactness, and two reductions to irreducible factors together with
`Langlands.AllFieldBZ.Classification.irreducibleProductFiniteLength` give finite length.
At a zero rank the product is a tensor model with a finite-dimensional factor.
See the paired Markdown.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert

open SmoothRep GeneralLinear
open AllFieldBZ.LocalFieldPackage.TopologicalData

universe uF uV

variable {K : AllFieldBZ.LocalFieldPackage.{uF}} (T : K.TopologicalData)

private theorem positiveProduct_exact {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    PreservesFiniteLengthShortExactLeft (binaryPositiveProductFunctor.{uF, uV} T ha hb) ∧
      PreservesFiniteLengthShortExactRight (binaryPositiveProductFunctor.{uF, uV} T ha hb) := by
  let := T.topology
  let B := BlockShape.binary a b ha hb
  let Φ := binaryPairFamilyFunctor.{uF, uV} T ha hb ⋙ FiniteTensor.externalFunctor
  have hTensor : PreservesFiniteLengthShortExactLeft Φ ∧
      PreservesFiniteLengthShortExactRight Φ :=
    BinaryProductExactness.tensorModel_exact Φ
      (fun X => BinaryProductExactness.pairSplit
        (fun i => ((binaryPairFamilyFunctor T ha hb).obj X i : Type uV)))
      (by
        intro X Y f v
        exact BinaryProductExactness.pairSplit_map _ _
          (fun i => (hom ((binaryPairFamilyFunctor T ha hb).map f i)).toLinearMap) v)
  have hInd ⦃X Y Z : SmoothRep.{0, uF, uV} ℂ (B.Levi K.Carrier)⦄
      (f : X ⟶ Y) (g : Y ⟶ Z) (h : IsShortExact (hom f) (hom g)) :
      IsShortExact
        (hom ((normalizedParabolicInductionFunctor T B).map f))
        (hom ((normalizedParabolicInductionFunctor T B).map g)) := by
    obtain ⟨hi, he, hq⟩ :=
      AllField.Parabolic.normalizedInductionExactness K.Carrier T B X Y Z
        X.representation Y.representation Z.representation (hom f) (hom g)
        X.isSmooth Y.isSmooth Z.isSmooth h.1 h.2.1 h.2.2
    exact ⟨hi, hq, he⟩
  exact ⟨fun D A B C f g h => hInd (Φ.map _) (Φ.map _) (hTensor.1 D A B C f g h),
    fun D A B C f g h => hInd (Φ.map _) (Φ.map _) (hTensor.2 D A B C f g h)⟩

private theorem positiveProduct_length {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    PreservesFiniteLength₂ (binaryPositiveProductFunctor.{uF, uV} T ha hb) := by
  let := T.topology
  let Φ := binaryPositiveProductFunctor.{uF, uV} T ha hb
  have hExact := positiveProduct_exact.{uF, uV} T ha hb
  intro A B hA hB
  let left := Prod.sectL _ B ⋙ Φ
  have hLeft : PreservesFiniteLengthShortExact left := by
    intro X Y Z f g hX hY hZ h
    exact hExact.1 ⟨B, hB⟩ ⟨X, hX⟩ ⟨Y, hY⟩ ⟨Z, hZ⟩ (hom f) (hom g) h
  refine preservesFiniteLength_of_irreducibles left hLeft (fun C hC => ?_) A hA
  let right := Prod.sectR C _ ⋙ Φ
  have hRight : PreservesFiniteLengthShortExact right := by
    intro X Y Z f g hX hY hZ h
    exact hExact.2 ⟨C, hasFiniteLength_of_isIrreducible hC⟩ ⟨X, hX⟩ ⟨Y, hY⟩
      ⟨Z, hZ⟩ (hom f) (hom g) h
  refine preservesFiniteLength_of_irreducibles right hRight (fun D hD => ?_) B hB
  exact AllFieldBZ.Classification.irreducibleProductFiniteLength.{uF, uV} K T (a + b)
    (by omega) (BlockShape.binary a b ha hb)
    ((binaryPairFamilyFunctor T ha hb).obj (C, D)) (by
      intro i
      fin_cases i
      · exact hC
      · exact hD)

private theorem binaryProduct_exact (a b : ℕ) :
    letI := T.topology
    PreservesFiniteLengthShortExactLeft (binaryNormalizedProductFunctor.{uF, uV} T a b) ∧
      PreservesFiniteLengthShortExactRight (binaryNormalizedProductFunctor.{uF, uV} T a b) := by
  let := T.topology
  by_cases ha : a = 0
  · exact BinaryProductExactness.tensorModel_exact _
      (fun X => (binaryLeftZeroTensorEquiv T ha X).toLinearEquiv)
      (fun f v => binaryLeftZeroTensorEquiv_naturality T ha f v)
  · by_cases hb : b = 0
    · exact BinaryProductExactness.tensorModel_exact _
        (fun X => (binaryRightZeroTensorEquiv T hb X).toLinearEquiv)
        (fun f v => binaryRightZeroTensorEquiv_naturality T hb f v)
    · rw [binaryNormalizedProductFunctor_of_pos T
        (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)]
      exact positiveProduct_exact T _ _

open Derivative.ProductDerivativesFiniteLength in
private theorem binaryProduct_length (a b : ℕ) :
    letI := T.topology
    PreservesFiniteLength₂ (binaryNormalizedProductFunctor.{uF, uV} T a b) := by
  let := T.topology
  intro A B hA hB
  by_cases ha : a = 0
  · let : Subsingleton (GeneralLinear a K.Carrier) :=
      GeneralLinear.subsingleton_of_rank_eq_zero ha
    let : Finite (GeneralLinear a K.Carrier) := Finite.of_subsingleton
    let : FiniteDimensional ℂ A := finiteDimensional_of_isFiniteLength A.representation hA
    refine isFiniteLength_of_equiv (binaryLeftZeroTensorEquiv T ha (A, B)).symm ?_
    exact isFiniteLength_comp _ _ (GeneralLinear.reindex _).surjective
      (isFiniteLength_secondFactor _ hB)
  · by_cases hb : b = 0
    · let : Subsingleton (GeneralLinear b K.Carrier) :=
        GeneralLinear.subsingleton_of_rank_eq_zero hb
      let : Finite (GeneralLinear b K.Carrier) := Finite.of_subsingleton
      let : FiniteDimensional ℂ B := finiteDimensional_of_isFiniteLength B.representation hB
      refine isFiniteLength_of_equiv (binaryRightZeroTensorEquiv T hb (A, B)).symm ?_
      exact isFiniteLength_comp _ _ (GeneralLinear.reindex _).surjective
        (isFiniteLength_firstFactor _ hA)
    · rw [binaryNormalizedProductFunctor_of_pos T
        (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)]
      exact positiveProduct_length T (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) A B hA hB

/-- The all-field normalized product descends in both variables to exact
Grothendieck classes at every pair of ranks. -/
theorem localFieldBinaryProductExactLength :
    LocalFieldBinaryProductExactLengthStatement.{uF, uV} := by
  intro F _ T
  dsimp only
  intro a b
  exact ⟨binaryProduct_length.{uF, max uF uV} (K := AllFieldBZ.LocalFieldPackage.ofField F) T a b,
    binaryProduct_exact.{uF, max uF uV} (K := AllFieldBZ.LocalFieldPackage.ofField F) T a b⟩

end Langlands.Aubert
