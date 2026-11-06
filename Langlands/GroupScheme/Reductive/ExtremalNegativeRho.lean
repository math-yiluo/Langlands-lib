import Langlands.GroupScheme.Reductive.ExtremalMatrixCoefficient
import Langlands.GroupScheme.Reductive.NegativeRhoCharacterUniqueness
import Langlands.GroupScheme.Reductive.NegativeRhoUnitCell

/-! # Identifying the two extremal characters with extended negative rho -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

section Restriction

variable {S : Scheme.{u}} {G H : GroupScheme S} {T : CommGroupScheme S}
  {j : T.toGrp ⟶ G}

/-- Restriction along the conjugate factor is the normalizing automorphism's
action on the restricted character. -/
theorem equivCharacterLattice_restrict_conjugateTorusFactor
    (jH : T.toGrp ⟶ H) (n : normalizerPoints j) (χ : rationalCharacters H) :
    rationalCharacters.equivCharacterLattice T
        (characterRestrict (conjugateTorusFactor jH n) χ) =
      characterAut (normalizingAut j n)
        (rationalCharacters.equivCharacterLattice T (characterRestrict jH χ)) := by
  rw [conjugateTorusFactor, characterRestrict_comp, AddMonoidHom.comp_apply]
  rfl

/-- Conjugating a torus factor preserves injectivity of character restriction. -/
theorem characterRestrict_conjugateTorusFactor_injective
    (jH : T.toGrp ⟶ H) (hinj : Function.Injective (characterRestrict jH))
    (n : normalizerPoints j) :
    Function.Injective (characterRestrict (conjugateTorusFactor jH n)) := by
  intro χ ψ h
  apply hinj
  apply (rationalCharacters.equivCharacterLattice T).injective
  apply (characterAut (normalizingAut j n)).injective
  have h' := congrArg (rationalCharacters.equivCharacterLattice T) h
  simpa only [equivCharacterLattice_restrict_conjugateTorusFactor] using h'

end Restriction

namespace MatrixRepresentation

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  {G H Q : GroupScheme (Spec (CommRingCat.of k))}
  (ρ : MatrixRepresentation G n)
  (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (e : n → ℤ) (hν : ν ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
  (i : H ⟶ G) (hH : (Dynamic.parabolic ν).IsRepresentedBy i)
  (j : n) (hj : ∀ a, a ≠ j → e j < e a)

/-- The two extremal characters restrict to the identical diagonal-entry
character on any common subgroup of the two supplied parabolics. -/
theorem restrict_minimum_eq_restrict_oppositeMaximum
    (iQ : Q ⟶ G)
    (hQ : (Dynamic.parabolic (Dynamic.oppositeCocharacter ν)).IsRepresentedBy iQ)
    {Z : GroupScheme (Spec (CommRingCat.of k))}
    (jZ : Z ⟶ G) (jH : Z ⟶ H) (jQ : Z ⟶ Q)
    (hZH : jH ≫ i = jZ) (hZQ : jQ ≫ iQ = jZ) :
    characterRestrict jH (minimumWeightCharacter ρ ν e hν i hH j hj) =
      characterRestrict jQ (oppositeMaximumWeightCharacter ρ ν e hν iQ hQ j hj) := by
  apply rationalCharacters.ext_characterEval
  intro U z
  apply Units.ext
  rw [characterEval_characterRestrict, characterEval_characterRestrict,
    minimumWeightCharacter_eval, oppositeMaximumWeightCharacter_eval]
  simp only [Category.assoc, ← Grp.comp_hom_hom, hZH, hZQ]

variable [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (jT : T.toGrp ⟶ G)
  (hZ : (Dynamic.centralizer ν).IsRepresentedBy jT)
  (hc : IsClosedSubgroup i) (w : normalizerPoints jT)
  (hQ : (Dynamic.parabolic (Dynamic.oppositeCocharacter ν)).IsRepresentedBy
    (i ≫ (G.innerIso w.val).hom))

include hc in
/-- If the normalizing automorphism negates the restricted minimum
character, the opposite maximum character is its negative on the same group. -/
theorem oppositeMaximumWeightCharacter_eq_neg_minimum
    (hanti : characterAut (normalizingAut jT w)
      (rationalCharacters.equivCharacterLattice T
        (characterRestrict (Dynamic.centralizerToParabolic hH hZ)
          (minimumWeightCharacter ρ ν e hν i hH j hj))) =
      -rationalCharacters.equivCharacterLattice T
        (characterRestrict (Dynamic.centralizerToParabolic hH hZ)
          (minimumWeightCharacter ρ ν e hν i hH j hj))) :
    oppositeMaximumWeightCharacter ρ ν e hν
        (i ≫ (G.innerIso w.val).hom) hQ j hj =
      -minimumWeightCharacter ρ ν e hν i hH j hj := by
  apply characterRestrict_conjugateTorusFactor_injective
    (Dynamic.centralizerToParabolic hH hZ)
    (Dynamic.parabolicCharacterEquiv hH hc hZ).injective w
  have heq := restrict_minimum_eq_restrict_oppositeMaximum ρ ν e hν i hH j hj
    (i ≫ (G.innerIso w.val).hom) hQ jT
    (Dynamic.centralizerToParabolic hH hZ)
    (conjugateTorusFactor (Dynamic.centralizerToParabolic hH hZ) w)
    (Dynamic.centralizerToParabolic_comp hH hZ)
    (conjugateTorusFactor_comp _ (Dynamic.centralizerToParabolic_comp hH hZ) w)
  have hopp :
      characterRestrict (conjugateTorusFactor (Dynamic.centralizerToParabolic hH hZ) w)
          (minimumWeightCharacter ρ ν e hν i hH j hj) =
        -characterRestrict (Dynamic.centralizerToParabolic hH hZ)
          (minimumWeightCharacter ρ ν e hν i hH j hj) := by
    apply (rationalCharacters.equivCharacterLattice T).injective
    rw [equivCharacterLattice_restrict_conjugateTorusFactor, map_neg]
    exact hanti
  rw [map_neg, hopp, neg_neg]
  exact heq.symm

end MatrixRepresentation

namespace Dynamic

open MatrixRepresentation AffineCoordinates

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (ρ : MatrixRepresentation G n)
  (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (e : n → ℤ) (hν : ν ≫ ρ = GeneralLinear.diagonalCocharacter n (CommRingCat.of k) e)
  (i : H ⟶ G) (hH : (parabolic ν).IsRepresentedBy i)
  (jT : T.toGrp ⟶ G) (hZ : (centralizer ν).IsRepresentedBy jT)
  (hc : IsClosedSubgroup i)
  (j : n) (hj : ∀ a, a ≠ j → e j < e a)
  {J : Type v} (P : RootDatum J (characterLattice T) (cocharacterLattice T))
  (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
  (hweight : rationalCharacters.equivCharacterLattice T
      (characterRestrict (centralizerToParabolic hH hZ)
        (minimumWeightCharacter ρ ν e hν i hH j hj)) =
    -IntegralWeylVector.rho P b hspan)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

include hweight hc in
omit [IsAffineHom H.X.hom] in
/-- The constructed extremal character is the actual extended negative rho
when its torus restriction has that weight. -/
theorem minimumWeightCharacter_eq_negativeRho :
    minimumWeightCharacter ρ ν e hν i hH j hj =
      negativeRhoCharacter hH hZ P b hspan :=
  (eq_negativeRhoCharacter_iff hH hc hZ P b hspan _).mpr hweight

include hweight hc in
/-- The diagonal coefficient has left covariance for the actual extended
negative-rho coordinate. -/
theorem diagonalMatrixCoefficient_mem_leftCovariant_negativeRho :
    diagonalMatrixCoefficient ρ j ∈ leftCovariantSubspace i
      (negativeRhoCoordinate hH hZ P b hspan) := by
  have h := diagonalMatrixCoefficient_mem_leftCovariantSubspace ρ ν e hν i hH j hj
  rw [minimumWeightCharacter_eq_negativeRho ρ ν e hν i hH jT hZ hc j hj
    P b hspan hweight] at h
  exact h

include hweight hc in
/-- The normalized diagonal coefficient as an element of the actual
negative-rho covariant function space. -/
def negativeRhoDiagonalCoefficient :
    leftCovariantSubspace i (negativeRhoCoordinate hH hZ P b hspan) :=
  ⟨diagonalMatrixCoefficient ρ j,
    diagonalMatrixCoefficient_mem_leftCovariant_negativeRho ρ ν e hν i hH jT hZ hc j hj
      P b hspan hweight⟩

variable (w : normalizerPoints jT)
  (hQ : (parabolic (oppositeCocharacter ν)).IsRepresentedBy (i ≫ (G.innerIso w.val).hom))
  (hanti : characterAut (normalizingAut jT w) (-IntegralWeylVector.rho P b hspan) =
    IntegralWeylVector.rho P b hspan)

include hweight hanti hc in
omit [IsAffineHom H.X.hom] in
/-- The opposite maximum character is the negative of the same extended
negative-rho character on `H`. -/
theorem oppositeMaximumWeightCharacter_eq_neg_negativeRho :
    oppositeMaximumWeightCharacter ρ ν e hν (i ≫ (G.innerIso w.val).hom) hQ j hj =
      -negativeRhoCharacter hH hZ P b hspan := by
  rw [oppositeMaximumWeightCharacter_eq_neg_minimum ρ ν e hν i hH j hj jT hZ hc w hQ]
  · rw [minimumWeightCharacter_eq_negativeRho ρ ν e hν i hH jT hZ hc j hj
      P b hspan hweight]
  · rw [hweight, neg_neg]
    exact hanti

include hweight hanti hc hQ in
/-- The diagonal coefficient has inverse-right covariance for exactly the
same negative-rho coordinate used in its left covariance. -/
theorem pointAlgebraHom_mul_inv_diagonalMatrixCoefficient_negativeRho
    (U : Over (Spec (CommRingCat.of k))) (h : U ⟶ H.X) (g : U ⟶ G.X) :
    pointAlgebraHom G U (g * (h ≫ (i ≫ (G.innerIso w.val).hom).hom.hom)⁻¹)
        (diagonalMatrixCoefficient ρ j) =
      pointAlgebraHom H U h (negativeRhoCoordinate hH hZ P b hspan) *
        pointAlgebraHom G U g (diagonalMatrixCoefficient ρ j) := by
  have heq := pointAlgebraHom_mul_inv_diagonalMatrixCoefficient ρ ν e hν j hj
    (i ≫ (G.innerIso w.val).hom) hQ U h g
  rw [oppositeMaximumWeightCharacter_eq_neg_negativeRho ρ ν e hν i hH jT hZ hc j hj
    P b hspan hweight w hQ hanti, neg_neg] at heq
  exact heq

end Dynamic

end Langlands.GroupScheme
