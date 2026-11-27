import Langlands.Representation.Aubert.LocalFieldGradedGrothendieck
import Langlands.Representation.Aubert.General.LocalFieldGLRationalOperatorStatement
import Langlands.Representation.Aubert.BinaryProductExactnessProof
import Langlands.AllField.Representation.Classification.NormalizedProductFiniteLengthProof
import Langlands.AllField.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.Smooth.Admissibility.FiniteLengthReduction

/-! Tensor classes in the actual binary product Levi over a local field. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct MonoidAlgebra

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GeneralLinear SmoothRep
open SmoothRep.FiniteLengthGrothendieckGroup
open AllFieldBZ (LocalFieldPackage)
open AllFieldBZ.LocalFieldPackage.TopologicalData

universe u v

variable {F : Type u} [Field F] (T : LocalFieldData F)
  {a b : ℕ} (ha : 0 < a) (hb : 0 < b)

/-- External tensor product with target the actual binary product Levi. -/
def localFieldBinaryLeviTensorFunctor :
    letI := T.topology
    (SmoothRep.{0, u, max (u + 1) v} ℂ (GeneralLinear a F) ×
      SmoothRep.{0, u, max (u + 1) v} ℂ (GeneralLinear b F)) ⥤
        SmoothRep.{0, u, max (u + 1) v} ℂ ((BlockShape.binary a b ha hb).Levi F) :=
  letI := T.topology
  letI : TopologicalSpace (LocalFieldPackage.ofField F).Carrier := T.topology
  binaryPairFamilyFunctor (F := LocalFieldPackage.ofField F) T ha hb ⋙ FiniteTensor.externalFunctor

private theorem binaryLeviTensor_finiteLength :
    letI := T.topology
    PreservesFiniteLength₂ (localFieldBinaryLeviTensorFunctor.{u, v} T ha hb) := by
  let := T.topology
  let : TopologicalSpace (LocalFieldPackage.ofField F).Carrier := T.topology
  intro A C hA hC
  let X := (binaryPairFamilyFunctor (F := LocalFieldPackage.ofField F) T ha hb).obj (A, C)
  have hX (i : Fin 2) : (X i).HasFiniteLength := by
    fin_cases i
    · exact hA
    · exact hC
  have haX (i : Fin 2) : (X i).IsAdmissible :=
    SmoothRep.isAdmissible_of_finiteLength_of_irreducible
      (fun D hD => (AllField.CuspidalSupport.cuspidalEmbedding F T _ D hD).1) (X i) (hX i)
  have hmatch := AllField.FiniteTensor.padicExternalTensorFactors F T (a + b)
    (by omega) (BlockShape.binary a b ha hb) X X haX haX
    (fun i => Classification.ProductLengthProof.selfMatching_of_finiteLength (hX i))
  obtain ⟨m, s, _, hs, _, _⟩ := hmatch
  exact LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength
    (A := Rep.of ((BlockShape.binary a b ha hb).blockTensor (fun i => (X i).representation))) ⟨s, hs⟩

private theorem binaryLeviTensor_shortExact :
    letI := T.topology
    let Φ := localFieldBinaryLeviTensorFunctor.{u, v} T ha hb
    PreservesFiniteLengthShortExactLeft Φ ∧ PreservesFiniteLengthShortExactRight Φ := by
  let := T.topology
  let : TopologicalSpace (LocalFieldPackage.ofField F).Carrier := T.topology
  intro Φ
  let P := binaryPairFamilyFunctor.{u, max (u + 1) v} (F := LocalFieldPackage.ofField F) T ha hb
  exact BinaryProductExactness.tensorModel_exact Φ
    (fun X => BinaryProductExactness.pairSplit (fun i => (P.obj X i : Type (max (u + 1) v))))
    (fun f x => BinaryProductExactness.pairSplit_map _ _
      (fun i => (hom (P.map f i)).toLinearMap) x)

/-- The tensor map on exact Grothendieck groups with target the product Levi. -/
def localFieldBinaryLeviTensorMap :
    letI := T.topology
    (GeneralLinear.FiniteLengthGrothendieckGroup.{max (u + 1) v, u} a F ⊗[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{max (u + 1) v, u} b F) →ₗ[ℤ]
        (BlockShape.binary a b ha hb).FiniteLengthGrothendieckGroup.{max (u + 1) v, u} F :=
  letI := T.topology
  tensorMap (localFieldBinaryLeviTensorFunctor T ha hb) (binaryLeviTensor_finiteLength T ha hb)
    (binaryLeviTensor_shortExact T ha hb).1 (binaryLeviTensor_shortExact T ha hb).2

/-- Pure tensors of actual classes give the class of the external tensor. -/
theorem localFieldBinaryLeviTensorMap_objects :
    letI := T.topology
    ∀ (A : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (GeneralLinear a F))
      (C : FiniteLengthObject.{0, u, max (u + 1) v} ℂ (GeneralLinear b F)),
      localFieldBinaryLeviTensorMap.{u, v} T ha hb (ofObject A ⊗ₜ[ℤ] ofObject C) =
        ofRepresentation ((localFieldBinaryLeviTensorFunctor T ha hb).obj (A.val, C.val))
          (binaryLeviTensor_finiteLength T ha hb A.val C.val A.property C.property) := by
  let := T.topology
  intro A C
  exact tensorMap_objects _ _ _ _ A C

/-- Applying normalized induction to the tensor map gives the graded binary
induction product in positive degrees. -/
theorem localFieldBinaryLeviTensorMap_induced
    (hm : LocalFieldMatrixParabolicExactLength.{u, v} T (a + b))
    (hx : LocalFieldBinaryProductExactLengthStatement.{u, max (u + 1) v}) :
    letI := T.topology
    let B := BlockShape.binary a b ha hb
    let i := map (T.normalizedParabolicInductionFunctor B) (hm B).1 (hm B).2.1
    i.comp (localFieldBinaryLeviTensorMap T ha hb) =
      TensorProduct.lift (LocalFieldGraded.binaryProduct (K := LocalFieldPackage.ofField F) T hx a b) := by
  let := T.topology
  let : TopologicalSpace (LocalFieldPackage.ofField F).Carrier := T.topology
  intro B i
  apply TensorProduct.ext
  apply bilinear_ext
  intro A C
  change i (localFieldBinaryLeviTensorMap T ha hb (ofObject A ⊗ₜ[ℤ] ofObject C)) =
    LocalFieldGraded.binaryProduct (K := LocalFieldPackage.ofField F) T hx a b (ofObject A) (ofObject C)
  rw [localFieldBinaryLeviTensorMap_objects, LocalFieldGraded.binaryProduct_objects]
  simp only [i, map_ofRepresentation]
  apply ofRepresentation_eq_of_equiv
  let P := binaryPositiveProductFunctor.{u, max (u + 1) v} (F := LocalFieldPackage.ofField F) T ha hb
  let V := (localFieldBinaryLeviTensorFunctor.{u, v} T ha hb).obj (A.val, C.val)
  let J := (T.normalizedParabolicInductionFunctor B).obj V
  have e : J.representation.Equiv (P.obj (A.val, C.val)).representation := Representation.Equiv.refl _
  exact e.trans (SmoothRep.equivOfIso
    ((binaryNormalizedProductPositiveIso (F := LocalFieldPackage.ofField F) T ha hb).app (A.val, C.val)).symm)

end Langlands.Aubert.General.RationalPointFamily.GL
