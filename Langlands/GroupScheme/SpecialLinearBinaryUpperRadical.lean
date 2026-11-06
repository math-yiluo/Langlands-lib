import Langlands.GroupScheme.SpecialLinearBinaryUpperRootKernel
import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.Rational.CharacterLine
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Unipotent.BaseChange
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SubgroupBaseChange

/-! # The actual geometric unipotent radical of the binary triangular group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.BinaryUpper

variable {k : Type u} [Field k]

/-- Every unipotent group mapping to the triangular group lands in its additive root. -/
theorem range_le_upperRootMap_of_isUnipotent
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (j : H ⟶ groupScheme (CommRingCat.of k)) (hH : IsUnipotent H) :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range (upperRootMap (CommRingCat.of k)) := by
  intro T g hg
  obtain ⟨x, rfl⟩ := (SubgroupFunctor.mem_range).mp hg
  rw [mem_range_upperRootMap_iff_diagonalPoints]
  have h := hH.characterEval_eq_one
    (characterRestrict j (diagonalCharacter (CommRingCat.of k))) T x
  rwa [characterEval_characterRestrict, characterEval_diagonalCharacter] at h

/-- The same greatestness holds after arbitrary extension of the ground field. -/
theorem range_le_baseChange_upperRootMap_of_isUnipotent
    {K : Type u} [Field K] (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {H : GroupScheme (Spec (CommRingCat.of K))}
    (j : H ⟶ (GroupScheme.baseChange b).obj (groupScheme (CommRingCat.of k)))
    (hH : IsUnipotent H) :
    SubgroupFunctor.range j ≤
      SubgroupFunctor.range ((GroupScheme.baseChange b).map
        (upperRootMap (CommRingCat.of k))) := by
  intro T g hg
  obtain ⟨x, rfl⟩ := (SubgroupFunctor.mem_range).mp hg
  rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange,
    mem_range_upperRootMap_iff_diagonalPoints]
  have h := hH.characterEval_eq_one
    (characterRestrict j (rationalCharacters.baseChange b
      (diagonalCharacter (CommRingCat.of k)))) T x
  rwa [characterEval_characterRestrict, rationalCharacters.characterEval_baseChange,
    characterEval_diagonalCharacter] at h

private theorem additive_isVectorGroup :
    RelativeRoot.IsVectorGroupOfDimension
      (VectorGroup.groupScheme (CommRingCat.of k) 1) 1 :=
  ⟨VectorGroup.coordinates (CommRingCat.of k) 1,
    VectorGroup.isNaturalVectorCoordinates⟩

/-- The actual upper root is the full ground-field unipotent radical. -/
theorem isUnipotentRadical_upperRootMap :
    IsUnipotentRadical (upperRootMap (CommRingCat.of k)) where
  isClosedSubgroup := isClosedSubgroup_upperRootMap _
  smooth := additive_isVectorGroup.smooth
  connectedSpace := additive_isVectorGroup.connectedSpace
  isUnipotent := VectorGroup.isUnipotent k 1
  isNormal := isNormal_range_upperRootMap _
  greatest _H j _ _ _ hu _ := range_le_upperRootMap_of_isUnipotent j hu

/-- The algebraic-closure pullback is also the full unipotent radical. -/
theorem isUnipotentRadical_baseChange_upperRootMap :
    IsUnipotentRadical ((GroupScheme.baseChange (toAlgebraicClosure k)).map
      (upperRootMap (CommRingCat.of k))) := by
  have : Smooth (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom :=
    additive_isVectorGroup.smooth
  have : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom :=
    additive_isVectorGroup.isAffineHom
  have : ConnectedSpace (VectorGroup.groupScheme (CommRingCat.of k) 1).X.left :=
    additive_isVectorGroup.connectedSpace
  refine ⟨(isClosedSubgroup_upperRootMap _).baseChange _, ?_, ?_, ?_, ?_, ?_⟩
  · change Smooth (pullback.snd
      (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom (toAlgebraicClosure k))
    infer_instance
  · exact GroupScheme.connectedSpace_baseChange_of_smooth_affine
      (VectorGroup.groupScheme (CommRingCat.of k) 1) (toAlgebraicClosure k)
  · exact (VectorGroup.isUnipotent k 1).baseChange
  · rw [SubgroupFunctor.range_baseChangeHom]
    exact (isNormal_range_upperRootMap _).baseChange _
  · intro H j _ _ _ hu _
    exact range_le_baseChange_upperRootMap_of_isUnipotent _ j hu

/-- The actual upper root is a geometric unipotent radical, in the Levi interface. -/
theorem isGeometricUnipotentRadical_upperRootMap :
    LeviSubgroup.IsGeometricUnipotentRadical (upperRootMap (CommRingCat.of k)) :=
  ⟨isUnipotentRadical_upperRootMap, isUnipotentRadical_baseChange_upperRootMap⟩

/-- The actual additive inclusion, with its proved geometric-radical property. -/
def geometricRadicalRepresentative :
    {r : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ groupScheme (CommRingCat.of k) //
      LeviSubgroup.IsGeometricUnipotentRadical r} :=
  ⟨upperRootMap (CommRingCat.of k), isGeometricUnipotentRadical_upperRootMap⟩

end Langlands.GroupScheme.SpecialLinear.BinaryUpper
