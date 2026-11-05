import Langlands.GroupScheme.Dynamic.CommonCentralizerDeterminantBalance

/-! # Three-factor determinant balance for equal dynamic centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators Classical

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Weights

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
  (zeta eta : cocharacterLattice T)
  (hEq : Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
    Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i))

include hT hEq

/-- Equal actual centralizers have the same zero pairings on every nonzero
adjoint weight space. -/
theorem latticePairing_eq_zero_iff_of_centralizer_eq
    (α : characterLattice T) (hα : weightSpace i α ≠ ⊥) :
    latticePairing T α zeta = 0 ↔ latticePairing T α eta = 0 := by
  have hw := congrArg
    (fun F => weightSpace i α ⊓ RelativeRoot.tangentSubmodule F) hEq
  rw [weightSpace_inf_tangentSubmodule_centralizer hT i zeta,
    weightSpace_inf_tangentSubmodule_centralizer hT i eta] at hw
  constructor
  · intro hz
    by_contra he
    rw [ite_eq_left hz, ite_eq_right he] at hw
    exact hα hw
  · intro he
    by_contra hz
    rw [ite_eq_right hz, ite_eq_left he] at hw
    exact hα hw.symm

/-- The positive/zero weighted axis vanishes when the two actual dynamic
centralizers agree. No representation of the axis subgroup is required. -/
theorem regionWeightCharacter_positive_zero_eq_zero_of_centralizer_eq :
    regionWeightCharacter i
      (fun α => 0 < latticePairing T α zeta ∧ latticePairing T α eta = 0) = 0 := by
  unfold regionWeightCharacter
  have hterm (α : characterLattice T) :
      (if 0 < latticePairing T α zeta ∧ latticePairing T α eta = 0
        then Module.finrank k (weightSpace i α) else 0) •
          (rationalCharacters.equivCharacterLattice T).symm α = 0 := by
    by_cases hα : weightSpace i α = ⊥
    · have hd : Module.finrank k (weightSpace i α) = 0 := by
        rw [hα, finrank_bot]
      simp only [hd, ite_self, zero_smul]
    · have hz := latticePairing_eq_zero_iff_of_centralizer_eq hT i zeta eta hEq α hα
      have hp : ¬(0 < latticePairing T α zeta ∧ latticePairing T α eta = 0) := by
        rintro ⟨hpos, he⟩
        exact (ne_of_gt hpos) (hz.mpr he)
      simp only [ite_eq_right hp, zero_smul]
  simp only [hterm, finsum_zero]

variable {i} [Mono i.hom.hom.left] (hroot : HasRelativeRootSystem i)

include hroot

/-- The two full positive-weight characters add to twice their common
positive region when the dynamic centralizers agree. -/
theorem HasRelativeRootSystem.positiveWeightCharacter_balance_of_centralizer_eq :
    positiveWeightCharacter i zeta + positiveWeightCharacter i eta =
      2 • regionWeightCharacter i
        (fun α => 0 < latticePairing T α zeta ∧ 0 < latticePairing T α eta) := by
  rw [hroot.positiveWeightCharacter_balance hT zeta eta,
    regionWeightCharacter_positive_zero_eq_zero_of_centralizer_eq hT i zeta eta hEq]
  have hswap :
      regionWeightCharacter i
          (fun α => latticePairing T α zeta = 0 ∧ 0 < latticePairing T α eta) =
        regionWeightCharacter i
          (fun α => 0 < latticePairing T α eta ∧ latticePairing T α zeta = 0) := by
    congr 1
    funext α
    exact propext (and_comm ..)
  rw [hswap,
    regionWeightCharacter_positive_zero_eq_zero_of_centralizer_eq hT i eta zeta hEq.symm,
    zero_add, zero_add]

end Weights

namespace Dynamic

section Determinants

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z U V C : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffine Z.X.left]
  [IsAffineHom U.X.hom] [IsAffineHom V.X.hom] [IsAffineHom C.X.hom]
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
  (zeta eta : cocharacterLattice T)
  (hEq : centralizer (CommGroupScheme.groupHom zeta ≫ i) =
    centralizer (CommGroupScheme.groupHom eta ≫ i))
  (iZ : Z ⟶ G)
  {iU : U ⟶ G} {iV : V ⟶ G} {iC : C ⟶ G}
  (hZ : SubgroupFunctor.range iZ ≤ centralizer (CommGroupScheme.groupHom zeta ≫ i))
  (hZ' : SubgroupFunctor.range iZ ≤ centralizer (CommGroupScheme.groupHom eta ≫ i))
  (hU : (unipotent (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy iU)
  (hV : (unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iV)
  (hC : (unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
    unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iC)
  (j : T.toGrp ⟶ Z) (hj : j ≫ iZ = i)
  {dU dV dC : ℕ}
  (cU : Lie.FiniteCoordinates U dU) (cV : Lie.FiniteCoordinates V dV)
  (cC : Lie.FiniteCoordinates C dC)

include hroot hT hEq hj

/-- The additive determinant character measuring the discrepancy between
the product of two radical determinants and the square of their intersection
determinant. Its evaluation is the corresponding multiplicative ratio. -/
def centralizingDeterminantSquareDefect : rationalCharacters Z :=
  (centralizingUnipotentAction
      (CommGroupScheme.groupHom zeta ≫ i) iZ hZ hU).determinantCharacter cU +
    (centralizingUnipotentAction
      (CommGroupScheme.groupHom eta ≫ i) iZ hZ' hV).determinantCharacter cV -
    2 • (centralizingUnipotentIntersectionAction
      (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
      iZ hZ hZ' hC).determinantCharacter cC

/-- Equal dynamic centralizers remove both axis terms from the torus
restriction of the actual three conjugation determinants. -/
theorem characterRestrict_centralizingDeterminant_square_of_centralizer_eq :
    characterRestrict j
        ((centralizingUnipotentAction
          (CommGroupScheme.groupHom zeta ≫ i) iZ hZ hU).determinantCharacter cU +
         (centralizingUnipotentAction
          (CommGroupScheme.groupHom eta ≫ i) iZ hZ' hV).determinantCharacter cV) =
      characterRestrict j
        (2 • (centralizingUnipotentIntersectionAction
          (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
          iZ hZ hZ' hC).determinantCharacter cC) := by
  simp only [map_add, map_nsmul,
    centralizingUnipotentAction_characterRestrict_determinant hT i zeta iZ j hj hZ hU cU,
    centralizingUnipotentAction_characterRestrict_determinant hT i eta iZ j hj hZ' hV cV,
    centralizingUnipotentIntersectionAction_characterRestrict_determinant
      hT i zeta eta iZ j hj hZ hZ' hC cC]
  exact hroot.positiveWeightCharacter_balance_of_centralizer_eq hT zeta eta hEq

/-- The determinant discrepancy restricts to zero on the common split torus. -/
theorem characterRestrict_centralizingDeterminantSquareDefect_eq_zero :
    characterRestrict j
      (centralizingDeterminantSquareDefect zeta eta iZ hZ hZ' hU hV hC cU cV cC) = 0 := by
  rw [centralizingDeterminantSquareDefect, map_sub,
    characterRestrict_centralizingDeterminant_square_of_centralizer_eq
      hroot hT zeta eta hEq iZ hZ hZ' hU hV hC j hj cU cV cC, sub_self]

/-- Restriction injectivity upgrades the equal-centralizer torus balance to
an equality of actual characters on the entire acting group. -/
theorem centralizingDeterminant_square_of_centralizer_eq
    (hinj : Function.Injective (characterRestrict j)) :
    (centralizingUnipotentAction
        (CommGroupScheme.groupHom zeta ≫ i) iZ hZ hU).determinantCharacter cU +
      (centralizingUnipotentAction
        (CommGroupScheme.groupHom eta ≫ i) iZ hZ' hV).determinantCharacter cV =
      2 • (centralizingUnipotentIntersectionAction
        (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
        iZ hZ hZ' hC).determinantCharacter cC :=
  hinj (characterRestrict_centralizingDeterminant_square_of_centralizer_eq
    hroot hT zeta eta hEq iZ hZ hZ' hU hV hC j hj cU cV cC)

/-- Injectivity of restriction forces the determinant discrepancy itself to
vanish on the full acting group. -/
theorem centralizingDeterminantSquareDefect_eq_zero
    (hinj : Function.Injective (characterRestrict j)) :
    centralizingDeterminantSquareDefect zeta eta iZ hZ hZ' hU hV hC cU cV cC = 0 := by
  rw [centralizingDeterminantSquareDefect,
    centralizingDeterminant_square_of_centralizer_eq
      hroot hT zeta eta hEq iZ hZ hZ' hU hV hC j hj cU cV cC hinj, sub_self]

/-- Under the same explicit detection hypothesis, the actual determinant
values satisfy the square identity at every rational acting point. -/
theorem rationalCharacterEval_centralizingDeterminant_square_of_centralizer_eq
    (hinj : Function.Injective (characterRestrict j)) (z : rationalPoints Z) :
    rationalCharacterEval
        ((centralizingUnipotentAction
          (CommGroupScheme.groupHom zeta ≫ i) iZ hZ hU).determinantCharacter cU) z *
      rationalCharacterEval
        ((centralizingUnipotentAction
          (CommGroupScheme.groupHom eta ≫ i) iZ hZ' hV).determinantCharacter cV) z =
      (rationalCharacterEval
        ((centralizingUnipotentIntersectionAction
          (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
          iZ hZ hZ' hC).determinantCharacter cC) z) ^ 2 := by
  have h := congrArg (fun χ => rationalCharacterEval χ z)
    (centralizingDeterminant_square_of_centralizer_eq
      hroot hT zeta eta hEq iZ hZ hZ' hU hV hC j hj cU cV cC hinj)
  simpa only [rationalCharacterEval_add, two_smul, pow_two] using h

end Determinants

end Dynamic
end Langlands.GroupScheme
