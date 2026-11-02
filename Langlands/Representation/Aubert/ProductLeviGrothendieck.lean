import Langlands.Representation.Aubert.GradedGrothendieck
import Langlands.Representation.Aubert.AlternatingOperator

/-!
# Tensor comparison with the actual binary product Levi

For two positive block ranks the external tensor product lands in the actual
block-shape Levi category. Its K0 tensor comparison is distinct from the
subsequent induction map to the larger general linear group.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
variable {a b : ℕ} (ha : 0 < a) (hb : 0 < b)

/-- The actual external tensor functor to the positive binary product Levi. -/
def binaryProductLeviTensorFunctor :
    letI := T.topology
    (SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier) ×
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)) ⥤
        SmoothRep.{0, uF, max uF uV} ℂ
          ((GeneralLinear.BlockShape.binary a b ha hb).Levi F.Carrier) :=
  letI := T.topology
  T.binaryPairFamilyFunctor ha hb ⋙ FiniteTensor.externalFunctor

/-- The actual positive binary induction factors through the product Levi. -/
theorem binaryPositiveProduct_factorization :
    letI := T.topology
    T.binaryPositiveProductFunctor.{uF, max uF uV} ha hb =
      binaryProductLeviTensorFunctor F T ha hb ⋙
        T.normalizedParabolicInductionFunctor
          (GeneralLinear.BlockShape.binary a b ha hb) := rfl

/-- Explicit finite-length and separate short-exactness obligations for the
actual product-Levi external tensor functor. -/
def ProductLeviTensorPrerequisitesStatement : Prop :=
  letI := T.topology
  let Φ := binaryProductLeviTensorFunctor.{uF, uV} F T ha hb
  SmoothRep.PreservesFiniteLength₂ Φ ∧
    SmoothRep.PreservesFiniteLengthShortExactLeft Φ ∧
      SmoothRep.PreservesFiniteLengthShortExactRight Φ

/-- The actual tensor comparison has product-Levi exact K0 as its target. -/
def productLeviTensorMap
    (hp : ProductLeviTensorPrerequisitesStatement.{uF, uV} F T ha hb) :
    letI := T.topology
    (GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} a F.Carrier ⊗[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} b F.Carrier) →ₗ[ℤ]
        (GeneralLinear.BlockShape.binary a b ha hb).FiniteLengthGrothendieckGroup.{uV, uF}
          F.Carrier :=
  letI := T.topology
  SmoothRep.FiniteLengthGrothendieckGroup.tensorMap
    (binaryProductLeviTensorFunctor F T ha hb) hp.1 hp.2.1 hp.2.2

/-- Bijectivity of the product-Levi tensor comparison is an additional target,
not an identification of the source with K0 of the larger GL group. -/
def ProductLeviTensorBijectiveStatement
    (hp : ProductLeviTensorPrerequisitesStatement.{uF, uV} F T ha hb) : Prop :=
  letI := T.topology
  Function.Bijective (productLeviTensorMap F T ha hb hp)

/-- The product-Levi K0 tensor equivalence, constructed only from a proof of
the exact bijectivity target for the already constructed map. -/
def productLeviTensorEquiv
    (hp : ProductLeviTensorPrerequisitesStatement.{uF, uV} F T ha hb)
    (he : ProductLeviTensorBijectiveStatement F T ha hb hp) :
    letI := T.topology
    (GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} a F.Carrier ⊗[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} b F.Carrier) ≃ₗ[ℤ]
        (GeneralLinear.BlockShape.binary a b ha hb).FiniteLengthGrothendieckGroup.{uV, uF}
          F.Carrier :=
  letI := T.topology
  LinearEquiv.ofBijective (productLeviTensorMap F T ha hb hp) he

/-- Induction is the subsequent map from product-Levi K0 to the larger GL K0. -/
def productLeviInductionTensorMap
    (hp : ProductLeviTensorPrerequisitesStatement.{uF, uV} F T ha hb) :
    letI := T.topology
    (GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} a F.Carrier ⊗[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} b F.Carrier) →ₗ[ℤ]
        GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} (a + b) F.Carrier :=
  letI := T.topology
  (Parabolic.normalizedInductionK0 F T (GeneralLinear.BlockShape.binary a b ha hb)).comp
    (productLeviTensorMap F T ha hb hp)

/-- The object formula identifies external tensor classes in the product Levi. -/
theorem productLeviTensorMap_classes
    (hp : ProductLeviTensorPrerequisitesStatement.{uF, uV} F T ha hb) :
    letI := T.topology
    ∀ (A : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ
        (GeneralLinear a F.Carrier))
      (B : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ
        (GeneralLinear b F.Carrier)),
      productLeviTensorMap F T ha hb hp
          (SmoothRep.FiniteLengthGrothendieckGroup.ofObject A ⊗ₜ[ℤ]
            SmoothRep.FiniteLengthGrothendieckGroup.ofObject B) =
        SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
          ((binaryProductLeviTensorFunctor F T ha hb).obj (A.val, B.val))
          (hp.1 _ _ A.property B.property) := by
  let := T.topology
  intro A B
  exact SmoothRep.FiniteLengthGrothendieckGroup.tensorMap_objects _ _ _ _ A B

/-- The tensor comparison followed by actual induction agrees with homogeneous
binary induction multiplication. This is equality of maps on exact K0. -/
theorem productLeviInductionTensorMap_eq
    (hp : ProductLeviTensorPrerequisitesStatement.{uF, uV} F T ha hb)
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) :
    letI := T.topology
    productLeviInductionTensorMap F T ha hb hp =
      TensorProduct.lift (binaryProductK0 F T hx a b) := by
  let := T.topology
  apply TensorProduct.ext
  apply SmoothRep.FiniteLengthGrothendieckGroup.bilinear_ext
  intro A B
  change Parabolic.normalizedInductionK0 F T _
      (productLeviTensorMap F T ha hb hp
        (SmoothRep.FiniteLengthGrothendieckGroup.ofObject A ⊗ₜ[ℤ]
          SmoothRep.FiniteLengthGrothendieckGroup.ofObject B)) =
    binaryProductK0 F T hx a b
      (SmoothRep.FiniteLengthGrothendieckGroup.ofObject A)
      (SmoothRep.FiniteLengthGrothendieckGroup.ofObject B)
  rw [productLeviTensorMap_classes, binaryProductK0_classes]
  let L := (binaryProductLeviTensorFunctor F T ha hb).obj (A.val, B.val)
  have hL : L.HasFiniteLength := hp.1 _ _ A.property B.property
  have hI := Parabolic.normalizedInductionK0_hasFiniteLength F T
    (GeneralLinear.BlockShape.binary a b ha hb) L hL
  refine (Parabolic.normalizedInductionK0_finiteLengthClass F T
    (GeneralLinear.BlockShape.binary a b ha hb) L hL hI).trans ?_
  apply SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv
  exact SmoothRep.equivOfIso
    ((T.binaryNormalizedProductPositiveIso ha hb).app (A.val, B.val)).symm

end Langlands.Aubert
