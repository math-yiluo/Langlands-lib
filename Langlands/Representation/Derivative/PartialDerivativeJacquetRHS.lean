import Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonStatement
import Langlands.Representation.Derivative.TopLocalizationData

/-!
# Actual right-hand quotient in the positive Jacquet comparison

The composite quotient map into the existing normalized two-block Jacquet functor
followed by the existing partial derivative is surjective and natural. Its action
retains the actual inverse-half first-factor modulus. This helper does not construct
the natural comparison with the ordinary derivative.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.Derivative.JacquetRHS

open GeneralLinear HarmonicAnalysis

universe uF uV

/-- Every actual upper unipotent has determinant one, including in rank zero. -/
theorem determinant_upperUnipotent {R : Type uF} [CommRing R] {m : ℕ}
    (u : GeneralLinear.upperUnipotent m R) :
    GeneralLinear.determinant u.val = 1 := by
  apply Units.ext
  change Matrix.det u.val.val = 1
  rw [Matrix.det_of_isUpperTriangular u.property.1]
  simp

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The actual two-block modulus is one on a final-block upper unipotent. -/
theorem leviModulus_upperUnipotent (T : F.TopologicalData) (k m : ℕ)
    (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ u : GeneralLinear.upperUnipotent m F.Carrier,
      T.leviModulus (Shahidi.twoBlocks k m hk hm)
        ((Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm (1, u.val)) = 1 := by
  let := T.topology
  intro u
  rw [T.leviModulus_twoBlocks]
  change T.determinantNorm k 1 ^ m / T.determinantNorm m u.val ^ k = 1
  rw [map_one, TopLocalization.determinantNorm_upper]
  simp

/-- Therefore its canonical inverse-half normalization is also one. -/
theorem inverseHalf_leviModulus_upperUnipotent (T : F.TopologicalData) (k m : ℕ)
    (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ u : GeneralLinear.upperUnipotent m F.Carrier,
      Jacquet.inverseHalfCharacter (T.leviModulus (Shahidi.twoBlocks k m hk hm))
        ((Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm (1, u.val)) = 1 := by
  let := T.topology
  intro u
  exact (Jacquet.inverseHalfCharacter_eq_one _ _).mpr
    (leviModulus_upperUnipotent T k m hk hm u)

/-- The actual first quotient map, with codomain the transported Jacquet object. -/
def jacquetMk (T : F.TopologicalData) (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier),
      A →ₗ[ℂ] (positiveTwoBlockNormalizedJacquet T k m hk hm).obj A := by
  letI := T.topology
  intro A
  exact (Shahidi.twoBlocks k m hk hm).jacquetMk A.representation

theorem jacquetMk_surjective (T : F.TopologicalData) (k m : ℕ)
    (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier),
      Function.Surjective (jacquetMk T k m hk hm A) := by
  let := T.topology
  intro A
  exact (Shahidi.twoBlocks k m hk hm).jacquetMk_surjective A.representation

/-- The transported actual Jacquet action uses the inverse continuous Levi map. -/
theorem jacquet_action_mk (T : F.TopologicalData) (k m : ℕ)
    (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (a : GeneralLinear k F.Carrier × GeneralLinear m F.Carrier) (v : A),
      ((positiveTwoBlockNormalizedJacquet T k m hk hm).obj A).representation a
          (jacquetMk T k m hk hm A v) =
        (Jacquet.inverseHalfCharacter (T.leviModulus (Shahidi.twoBlocks k m hk hm))
          ((Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm a) : ℂ) •
            jacquetMk T k m hk hm A (A.representation (GeneralLinear.blockSum a) v) := by
  let := T.topology
  intro A a v
  change T.normalizedJacquet (Shahidi.twoBlocks k m hk hm) A.representation
      ((Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm a)
      ((Shahidi.twoBlocks k m hk hm).jacquetMk A.representation v) = _
  rw [T.normalizedJacquet_mk, Jacquet.inverseHalfCharacter_apply,
    Shahidi.twoBlocks_leviEmbedding]
  rfl

/-- Transport to the product keeps the actual mapped underlying quotient map. -/
theorem jacquet_map_mk (T : F.TopologicalData) (k m : ℕ)
    (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier)}
      (f : A ⟶ B) (v : A),
      SmoothRep.hom ((positiveTwoBlockNormalizedJacquet T k m hk hm).map f)
          (jacquetMk T k m hk hm A v) =
        jacquetMk T k m hk hm B (SmoothRep.hom f v) := by
  intros
  rfl

/-- The actual double quotient map into the right-hand composite functor. -/
def rhsMk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier),
      A →ₗ[ℂ] ((positiveTwoBlockNormalizedJacquet T k m hk hm) ⋙
        partialDerivative T ψ k m).obj A := by
  letI := T.topology
  intro A
  exact (partialDerivativeMk T ψ k m
    ((positiveTwoBlockNormalizedJacquet T k m hk hm).obj A)).comp
      (jacquetMk T k m hk hm A)

theorem rhsMk_surjective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier),
      Function.Surjective (rhsMk T ψ k m hk hm A) := by
  let := T.topology
  intro A
  exact (partialDerivativeMk_surjective T ψ k m _).comp
    (jacquetMk_surjective T k m hk hm A)

/-- Naturality holds for the actual composite functor's image of every intertwiner. -/
theorem rhsMk_natural (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier)}
      (f : A ⟶ B) (v : A),
      SmoothRep.hom (((positiveTwoBlockNormalizedJacquet T k m hk hm) ⋙
        partialDerivative T ψ k m).map f) (rhsMk T ψ k m hk hm A v) =
        rhsMk T ψ k m hk hm B (SmoothRep.hom f v) := by
  let := T.topology
  intro A B f v
  change SmoothRep.hom ((partialDerivative T ψ k m).map
      ((positiveTwoBlockNormalizedJacquet T k m hk hm).map f))
      (partialDerivativeMk T ψ k m _ (jacquetMk T k m hk hm A v)) =
    partialDerivativeMk T ψ k m _ (jacquetMk T k m hk hm B (SmoothRep.hom f v))
  rw [partialDerivative_map_mk, jacquet_map_mk]

/-- The actual first-factor action retains exactly the inverse-half Jacquet scalar. -/
theorem rhs_action_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (g : GeneralLinear k F.Carrier) (v : A),
      (((positiveTwoBlockNormalizedJacquet T k m hk hm) ⋙
        partialDerivative T ψ k m).obj A).representation g (rhsMk T ψ k m hk hm A v) =
        (Jacquet.inverseHalfCharacter (T.leviModulus (Shahidi.twoBlocks k m hk hm))
          ((Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm (g, 1)) : ℂ) •
            rhsMk T ψ k m hk hm A
              (A.representation (GeneralLinear.blockSum (g, 1)) v) := by
  let := T.topology
  intro A g v
  change ((partialDerivative T ψ k m).obj
      ((positiveTwoBlockNormalizedJacquet T k m hk hm).obj A)).representation g
      (partialDerivativeMk T ψ k m _ (jacquetMk T k m hk hm A v)) = _
  rw [partialDerivative_action_mk, jacquet_action_mk, map_smul]
  rfl

/-- Every actual parabolic-radical relation is killed by the double quotient. -/
theorem rhsMk_radical (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (u : (Shahidi.twoBlocks k m hk hm).unipotentRadical F.Carrier) (v : A),
      rhsMk T ψ k m hk hm A (A.representation u.val.val v) =
        rhsMk T ψ k m hk hm A v := by
  let := T.topology
  intro A u v
  exact congrArg (partialDerivativeMk T ψ k m
    ((positiveTwoBlockNormalizedJacquet T k m hk hm).obj A))
    (Jacquet.mk_apply_subgroup
      (A.representation.comp ((Shahidi.twoBlocks k m hk hm).parabolic F.Carrier).subtype)
      ((Shahidi.twoBlocks k m hk hm).unipotentRadical F.Carrier) u v)

/-- The same relation for the radical's actual image in the ambient GL group. -/
theorem rhsMk_unipotentSubgroup (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (u : (Shahidi.twoBlocks k m hk hm).unipotentSubgroup F.Carrier) (v : A),
      rhsMk T ψ k m hk hm A (A.representation u.val v) =
        rhsMk T ψ k m hk hm A v := by
  let := T.topology
  intro A u v
  obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.mp u.property
  rw [← hwu]
  exact rhsMk_radical T ψ k m hk hm A ⟨w, hw⟩ v

/-- Final-block upper unipotents satisfy the original entrywise-character relation. -/
theorem rhsMk_upperUnipotent (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (u : GeneralLinear.upperUnipotent m F.Carrier) (v : A),
      rhsMk T ψ k m hk hm A (A.representation (GeneralLinear.blockSum (1, u.val)) v) =
        (Whittaker.entrywiseCharacter ψ.complex m u : ℂ) •
          rhsMk T ψ k m hk hm A v := by
  let := T.topology
  intro A u v
  have h :
      ((positiveTwoBlockNormalizedJacquet T k m hk hm).obj A).representation (1, u.val)
          (jacquetMk T k m hk hm A v) =
        jacquetMk T k m hk hm A
          (A.representation (GeneralLinear.blockSum (1, u.val)) v) := by
    rw [jacquet_action_mk, inverseHalf_leviModulus_upperUnipotent]
    simp
  change partialDerivativeMk T ψ k m _
    (jacquetMk T k m hk hm A
      (A.representation (GeneralLinear.blockSum (1, u.val)) v)) = _
  rw [← h, partialDerivativeMk_unipotent]
  rfl

end Langlands.Derivative.JacquetRHS
