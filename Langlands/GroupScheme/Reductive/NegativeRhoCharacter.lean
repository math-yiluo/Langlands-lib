import Langlands.GroupScheme.Reductive.IntegralWeylVectorProperties
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.HomogeneousCharacterCoordinates

/-! # Extending negative rho along a supplied dynamic Levi retraction -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section Extension

variable {S : Scheme.{u}} {G H : GroupScheme S} {T : CommGroupScheme S}
  {ν : (Gm S).toGrp ⟶ G} [IsSeparated G.X.hom]
  {i : H ⟶ G} {j : T.toGrp ⟶ G}
  (hH : (parabolic ν).IsRepresentedBy i)
  (hT : (centralizer ν).IsRepresentedBy j)

/-- Extend a character of a supplied commutative dynamic centralizer to its parabolic. -/
def extendCentralizerCharacter : characterLattice T →+ rationalCharacters H :=
  (characterRestrict (limitGroupHom hH hT)).comp
    (rationalCharacters.equivCharacterLattice T).symm.toAddMonoidHom

/-- Restricting an extended character recovers the original character. -/
@[simp] theorem restrict_extendCentralizerCharacter (χ : characterLattice T) :
    characterRestrict (centralizerToParabolic hH hT)
      (extendCentralizerCharacter hH hT χ) =
        (rationalCharacters.equivCharacterLattice T).symm χ := by
  change Additive.ofMul (centralizerToParabolic hH hT ≫
    (limitGroupHom hH hT ≫ CommGroupScheme.groupHom χ)) = _
  rw [← Category.assoc, centralizerToParabolic_comp_limitGroupHom, Category.id_comp]
  rfl

theorem extendCentralizerCharacter_injective :
    Function.Injective (extendCentralizerCharacter hH hT) := by
  intro χ ψ h
  have hh := congrArg (characterRestrict (centralizerToParabolic hH hT)) h
  simpa using hh

/-- The extended character evaluates on the image under the actual limit morphism. -/
theorem characterEval_extendCentralizerCharacter (χ : characterLattice T)
    (U : Over S) (x : U ⟶ H.X) :
    characterEval (extendCentralizerCharacter hH hT χ) U x =
      characterEval ((rationalCharacters.equivCharacterLattice T).symm χ) U
        (x ≫ (limitGroupHom hH hT).hom.hom) :=
  characterEval_characterRestrict _ _ _ _

end Extension

section NegativeRho

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}
  {i : H ⟶ G} {j : T.toGrp ⟶ G}
  (hH : (parabolic ν).IsRepresentedBy i)
  (hT : (centralizer ν).IsRepresentedBy j)
  {J : Type v} (Q : RootDatum J (characterLattice T) (cocharacterLattice T))
  (b : Q.Base) (hspan : Q.corootSpan ℤ = ⊤)

/-- The actual rational character extending negative rho on the supplied dynamic centralizer. -/
def negativeRhoCharacter : rationalCharacters H :=
  extendCentralizerCharacter hH hT (-IntegralWeylVector.rho Q b hspan)

/-- Its restriction to the supplied centralizer is exactly negative rho. -/
@[simp] theorem restrict_negativeRhoCharacter :
    rationalCharacters.equivCharacterLattice T
      (characterRestrict (centralizerToParabolic hH hT)
        (negativeRhoCharacter hH hT Q b hspan)) =
      -IntegralWeylVector.rho Q b hspan := by
  simp [negativeRhoCharacter]

/-- On actual coroots the restricted character is the negative dual height. -/
theorem pairing_negativeRhoCharacter (hQ : IsRootDatumOf j Q) (a : J) :
    latticePairing T
      (rationalCharacters.equivCharacterLattice T
        (characterRestrict (centralizerToParabolic hH hT)
          (negativeRhoCharacter hH hT Q b hspan))) (Q.coroot a) = -b.flip.height a := by
  rw [restrict_negativeRhoCharacter, ← hQ.1]
  simp only [LinearMap.map_neg₂, IntegralWeylVector.pairing_rho_coroot_eq_height]

/-- The actual restricted character is regular on all coroots. -/
theorem pairing_negativeRhoCharacter_ne_zero (hQ : IsRootDatumOf j Q) (a : J) :
    latticePairing T
      (rationalCharacters.equivCharacterLattice T
        (characterRestrict (centralizerToParabolic hH hT)
          (negativeRhoCharacter hH hT Q b hspan))) (Q.coroot a) ≠ 0 := by
  rw [pairing_negativeRhoCharacter hH hT Q b hspan hQ a]
  exact neg_ne_zero.mpr (b.flip.height_ne_zero a)

variable [IsAffine H.X.left]

/-- The affine coordinate of the actual extended negative-rho character. -/
def negativeRhoCoordinate : AffineCoordinates.algebra H :=
  AffineCoordinates.characterCoordinate H (negativeRhoCharacter hH hT Q b hspan)

/-- The coordinate has the character's prescribed value on every relative test scheme. -/
theorem pointAlgebraHom_negativeRhoCoordinate
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ H.X) :
    AffineCoordinates.pointAlgebraHom H U x (negativeRhoCoordinate hH hT Q b hspan) =
      (characterEval ((rationalCharacters.equivCharacterLattice T).symm
        (-IntegralWeylVector.rho Q b hspan)) U
        (x ≫ (limitGroupHom hH hT).hom.hom)).val := by
  rw [negativeRhoCoordinate, AffineCoordinates.pointAlgebraHom_characterCoordinate]
  rfl

/-- Evaluation at the centralizer inclusion recovers negative rho on all test schemes. -/
theorem pointAlgebraHom_negativeRhoCoordinate_centralizer
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ T.toGrp.X) :
    AffineCoordinates.pointAlgebraHom H U
      (x ≫ (centralizerToParabolic hH hT).hom.hom)
        (negativeRhoCoordinate hH hT Q b hspan) =
      (characterEval ((rationalCharacters.equivCharacterLattice T).symm
        (-IntegralWeylVector.rho Q b hspan)) U x).val := by
  rw [negativeRhoCoordinate, AffineCoordinates.pointAlgebraHom_characterCoordinate,
    ← characterEval_characterRestrict]
  rw [negativeRhoCharacter, restrict_extendCentralizerCharacter]

/-- Every value of the coordinate is a unit, including over nonaffine or nonreduced tests. -/
theorem isUnit_negativeRhoCoordinate
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ H.X) :
    IsUnit (AffineCoordinates.pointAlgebraHom H U x
      (negativeRhoCoordinate hH hT Q b hspan)) := by
  rw [pointAlgebraHom_negativeRhoCoordinate]
  exact Units.isUnit _

end NegativeRho

end Langlands.GroupScheme.Dynamic
