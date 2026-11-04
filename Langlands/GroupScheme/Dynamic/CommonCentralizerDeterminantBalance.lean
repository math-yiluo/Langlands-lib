import Langlands.GroupScheme.Dynamic.CommonTorusIntersectionDeterminants

/-! # Actual common-centralizer actions and torus determinant balance -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators Classical

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Dynamic

section Actions

variable {S : Scheme.{u}} {G Z U : GroupScheme S}
  (chi psi : (Gm S).toGrp ⟶ G) (iZ : Z ⟶ G) {iU : U ⟶ G}

/-- A homomorphism whose range centralizes a cocharacter normalizes its
actual represented identity-limit subgroup, on every test scheme. -/
theorem range_unipotent_isNormalizedBy_of_centralizing
    (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
    (hU : (unipotent chi).IsRepresentedBy iU) :
    (SubgroupFunctor.range iU).IsNormalizedBy (SubgroupFunctor.range iZ) := by
  rw [hU.2]
  intro V z g hz hg
  exact unipotent_isNormalizedBy_parabolic chi V z g
    (centralizer_le_parabolic chi V (hZ V hz)) hg

/-- Actual conjugation on a represented identity-limit subgroup by a
homomorphism whose image centralizes the cocharacter. -/
def centralizingUnipotentAction
    (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
    (hU : (unipotent chi).IsRepresentedBy iU) :
    AutomorphicAction Z U :=
  have : Mono iU.hom.hom := hU.1
  AutomorphicAction.ofNormalizedConjugation iU iZ
    (range_unipotent_isNormalizedBy_of_centralizing chi iZ hZ hU)

theorem centralizingUnipotentAction_act_comp
    (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
    (hU : (unipotent chi).IsRepresentedBy iU)
    {V : Over S} (z : V ⟶ Z.X) (g : V ⟶ U.X) :
    (centralizingUnipotentAction chi iZ hZ hU).act z g ≫ iU.hom.hom =
      (z ≫ iZ.hom.hom) * (g ≫ iU.hom.hom) * (z ≫ iZ.hom.hom)⁻¹ :=
  SubgroupFunctor.lift_comp_normalizedConjugation_comp iU iZ
    (range_unipotent_isNormalizedBy_of_centralizing chi iZ hZ hU) z g

/-- A homomorphism centralizing both cocharacters normalizes the actual
intersection of their identity-limit subgroups. -/
theorem range_unipotentIntersection_isNormalizedBy_of_centralizing
    (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
    (hZ' : SubgroupFunctor.range iZ ≤ centralizer psi)
    (hU : (unipotent chi ⊓ unipotent psi).IsRepresentedBy iU) :
    (SubgroupFunctor.range iU).IsNormalizedBy (SubgroupFunctor.range iZ) := by
  rw [hU.2]
  intro V z g hz hg
  exact ⟨unipotent_isNormalizedBy_parabolic chi V z g
      (centralizer_le_parabolic chi V (hZ V hz)) hg.1,
    unipotent_isNormalizedBy_parabolic psi V z g
      (centralizer_le_parabolic psi V (hZ' V hz)) hg.2⟩

/-- Actual conjugation on the represented common identity-limit subgroup
by a homomorphism centralizing both cocharacters. -/
def centralizingUnipotentIntersectionAction
    (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
    (hZ' : SubgroupFunctor.range iZ ≤ centralizer psi)
    (hU : (unipotent chi ⊓ unipotent psi).IsRepresentedBy iU) :
    AutomorphicAction Z U :=
  have : Mono iU.hom.hom := hU.1
  AutomorphicAction.ofNormalizedConjugation iU iZ
    (range_unipotentIntersection_isNormalizedBy_of_centralizing chi psi iZ hZ hZ' hU)

theorem centralizingUnipotentIntersectionAction_act_comp
    (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
    (hZ' : SubgroupFunctor.range iZ ≤ centralizer psi)
    (hU : (unipotent chi ⊓ unipotent psi).IsRepresentedBy iU)
    {V : Over S} (z : V ⟶ Z.X) (g : V ⟶ U.X) :
    (centralizingUnipotentIntersectionAction chi psi iZ hZ hZ' hU).act z g ≫
        iU.hom.hom =
      (z ≫ iZ.hom.hom) * (g ≫ iU.hom.hom) * (z ≫ iZ.hom.hom)⁻¹ :=
  SubgroupFunctor.lift_comp_normalizedConjugation_comp iU iZ
    (range_unipotentIntersection_isNormalizedBy_of_centralizing chi psi iZ hZ hZ' hU) z g

/-- A homomorphism centralizing both cocharacters normalizes the actual
unipotent/centralizer intersection. -/
theorem range_unipotentCentralizerIntersection_isNormalizedBy_of_centralizing
    (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
    (hZ' : SubgroupFunctor.range iZ ≤ centralizer psi)
    (hU : (unipotent chi ⊓ centralizer psi).IsRepresentedBy iU) :
    (SubgroupFunctor.range iU).IsNormalizedBy (SubgroupFunctor.range iZ) := by
  rw [hU.2]
  intro V z g hz hg
  exact ⟨unipotent_isNormalizedBy_parabolic chi V z g
      (centralizer_le_parabolic chi V (hZ V hz)) hg.1,
    ((centralizer psi).carrier V).mul_mem
      (((centralizer psi).carrier V).mul_mem (hZ' V hz) hg.2)
      (((centralizer psi).carrier V).inv_mem (hZ' V hz))⟩

/-- Actual conjugation on the represented unipotent/centralizer
intersection by a homomorphism centralizing both cocharacters. -/
def centralizingUnipotentCentralizerIntersectionAction
    (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
    (hZ' : SubgroupFunctor.range iZ ≤ centralizer psi)
    (hU : (unipotent chi ⊓ centralizer psi).IsRepresentedBy iU) :
    AutomorphicAction Z U :=
  have : Mono iU.hom.hom := hU.1
  AutomorphicAction.ofNormalizedConjugation iU iZ
    (range_unipotentCentralizerIntersection_isNormalizedBy_of_centralizing
      chi psi iZ hZ hZ' hU)

theorem centralizingUnipotentCentralizerIntersectionAction_act_comp
    (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
    (hZ' : SubgroupFunctor.range iZ ≤ centralizer psi)
    (hU : (unipotent chi ⊓ centralizer psi).IsRepresentedBy iU)
    {V : Over S} (z : V ⟶ Z.X) (g : V ⟶ U.X) :
    (centralizingUnipotentCentralizerIntersectionAction chi psi iZ hZ hZ' hU).act z g ≫
        iU.hom.hom =
      (z ≫ iZ.hom.hom) * (g ≫ iU.hom.hom) * (z ≫ iZ.hom.hom)⁻¹ :=
  SubgroupFunctor.lift_comp_normalizedConjugation_comp iU iZ
    (range_unipotentCentralizerIntersection_isNormalizedBy_of_centralizing
      chi psi iZ hZ hZ' hU) z g

end Actions

section Equivariance

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G Z U : GroupScheme S}
  (i : T.toGrp ⟶ G) (iZ : Z ⟶ G) {iU : U ⟶ G}
  (j : T.toGrp ⟶ Z) (hj : j ≫ iZ = i)

include hj

/-- Every actual conjugation action through `iZ` restricts along the
displayed torus factorization to ambient conjugation through `i`. -/
theorem restrict_isEquivariant_conjugation_of_act_comp
    (a : AutomorphicAction Z U)
    (ha : ∀ {V : Over S} (z : V ⟶ Z.X) (g : V ⟶ U.X),
      a.act z g ≫ iU.hom.hom =
        (z ≫ iZ.hom.hom) * (g ≫ iU.hom.hom) * (z ≫ iZ.hom.hom)⁻¹) :
    (a.restrict j).IsEquivariant (AutomorphicAction.conjugation i) iU := by
  intro V t g
  rw [AutomorphicAction.restrict_act, ha, AutomorphicAction.conjugation_act,
    Category.assoc, ← Grp.comp_hom_hom, hj]

end Equivariance

section Determinants

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffine Z.X.left] [IsAffineHom U.X.hom]
  (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
  (zeta eta : cocharacterLattice T) (iZ : Z ⟶ G) {iU : U ⟶ G}
  (j : T.toGrp ⟶ Z) (hj : j ≫ iZ = i)

include hT hj

/-- The actual full identity-limit determinant restricts to the positive
weight character even when the acting group is a smaller common centralizer. -/
theorem centralizingUnipotentAction_characterRestrict_determinant
    (hZ : SubgroupFunctor.range iZ ≤ centralizer (CommGroupScheme.groupHom zeta ≫ i))
    (hU : (unipotent (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy iU)
    {d : ℕ} (c : Lie.FiniteCoordinates U d) :
    characterRestrict j
        ((centralizingUnipotentAction (CommGroupScheme.groupHom zeta ≫ i) iZ hZ hU).determinantCharacter c) =
      positiveWeightCharacter i zeta := by
  have ha :
      ((centralizingUnipotentAction
        (CommGroupScheme.groupHom zeta ≫ i) iZ hZ hU).restrict j).IsEquivariant
        (AutomorphicAction.conjugation i) iU :=
    restrict_isEquivariant_conjugation_of_act_comp i iZ j hj
      (centralizingUnipotentAction (CommGroupScheme.groupHom zeta ≫ i) iZ hZ hU)
      (centralizingUnipotentAction_act_comp (CommGroupScheme.groupHom zeta ≫ i) iZ hZ hU)
  rw [characterRestrict_determinant_of_tangentRegion hT i _ j hU ha
    (fun α => 0 < latticePairing T α zeta) (by
      intro α
      rw [weightSpace_inf_tangentSubmodule_unipotent hT i zeta]
      split_ifs <;> rfl) c]
  unfold regionWeightCharacter positiveWeightCharacter
  apply finsum_congr
  intro α
  split_ifs <;> rfl

/-- The actual common positive intersection determinant restricts to its
dimension-weighted positive/positive region. -/
theorem centralizingUnipotentIntersectionAction_characterRestrict_determinant
    (hZ : SubgroupFunctor.range iZ ≤ centralizer (CommGroupScheme.groupHom zeta ≫ i))
    (hZ' : SubgroupFunctor.range iZ ≤ centralizer (CommGroupScheme.groupHom eta ≫ i))
    (hU : (unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
      unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iU)
    {d : ℕ} (c : Lie.FiniteCoordinates U d) :
    characterRestrict j
        ((centralizingUnipotentIntersectionAction
          (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
          iZ hZ hZ' hU).determinantCharacter c) =
      regionWeightCharacter i
        (fun α => 0 < latticePairing T α zeta ∧ 0 < latticePairing T α eta) := by
  apply characterRestrict_determinant_unipotent_inf_unipotent hT i _ j zeta eta hU
  exact restrict_isEquivariant_conjugation_of_act_comp i iZ j hj _
    (centralizingUnipotentIntersectionAction_act_comp
      (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
      iZ hZ hZ' hU)

/-- The actual positive/zero intersection determinant restricts to its
dimension-weighted positive/zero region. -/
theorem centralizingUnipotentCentralizerIntersectionAction_characterRestrict_determinant
    (hZ : SubgroupFunctor.range iZ ≤ centralizer (CommGroupScheme.groupHom zeta ≫ i))
    (hZ' : SubgroupFunctor.range iZ ≤ centralizer (CommGroupScheme.groupHom eta ≫ i))
    (hU : (unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
      centralizer (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iU)
    {d : ℕ} (c : Lie.FiniteCoordinates U d) :
    characterRestrict j
        ((centralizingUnipotentCentralizerIntersectionAction
          (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
          iZ hZ hZ' hU).determinantCharacter c) =
      regionWeightCharacter i
        (fun α => 0 < latticePairing T α zeta ∧ latticePairing T α eta = 0) := by
  apply characterRestrict_determinant_unipotent_inf_centralizer hT i _ j zeta eta hU
  exact restrict_isEquivariant_conjugation_of_act_comp i iZ j hj _
    (centralizingUnipotentCentralizerIntersectionAction_act_comp
      (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
      iZ hZ hZ' hU)

end Determinants

section Balance

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z U V A B C : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffine Z.X.left]
  [IsAffineHom U.X.hom] [IsAffineHom V.X.hom]
  [IsAffineHom A.X.hom] [IsAffineHom B.X.hom] [IsAffineHom C.X.hom]
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
  (zeta eta : cocharacterLattice T)
  (iZ : Z ⟶ G)
  {iU : U ⟶ G} {iV : V ⟶ G} {iA : A ⟶ G} {iB : B ⟶ G} {iC : C ⟶ G}
  (hZ : SubgroupFunctor.range iZ ≤ centralizer (CommGroupScheme.groupHom zeta ≫ i))
  (hZ' : SubgroupFunctor.range iZ ≤ centralizer (CommGroupScheme.groupHom eta ≫ i))
  (hU : (unipotent (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy iU)
  (hV : (unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iV)
  (hA : (unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
    centralizer (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iA)
  (hB : (unipotent (CommGroupScheme.groupHom eta ≫ i) ⊓
    centralizer (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy iB)
  (hC : (unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
    unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iC)
  (j : T.toGrp ⟶ Z) (hj : j ≫ iZ = i)
  {dU dV dA dB dC : ℕ}
  (cU : Lie.FiniteCoordinates U dU) (cV : Lie.FiniteCoordinates V dV)
  (cA : Lie.FiniteCoordinates A dA) (cB : Lie.FiniteCoordinates B dB)
  (cC : Lie.FiniteCoordinates C dC)

include hroot hT hj

/-- The five actual common-centralizer conjugation determinants satisfy
the axis/intersection balance after restriction to the common split torus. -/
theorem characterRestrict_centralizingDeterminant_balance :
    characterRestrict j
        ((centralizingUnipotentAction
          (CommGroupScheme.groupHom zeta ≫ i) iZ hZ hU).determinantCharacter cU +
         (centralizingUnipotentAction
          (CommGroupScheme.groupHom eta ≫ i) iZ hZ' hV).determinantCharacter cV) =
      characterRestrict j
        ((centralizingUnipotentCentralizerIntersectionAction
          (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
          iZ hZ hZ' hA).determinantCharacter cA +
         (centralizingUnipotentCentralizerIntersectionAction
          (CommGroupScheme.groupHom eta ≫ i) (CommGroupScheme.groupHom zeta ≫ i)
          iZ hZ' hZ hB).determinantCharacter cB +
         2 • (centralizingUnipotentIntersectionAction
          (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
          iZ hZ hZ' hC).determinantCharacter cC) := by
  simp only [map_add, map_nsmul,
    centralizingUnipotentAction_characterRestrict_determinant hT i zeta iZ j hj hZ hU cU,
    centralizingUnipotentAction_characterRestrict_determinant hT i eta iZ j hj hZ' hV cV,
    centralizingUnipotentCentralizerIntersectionAction_characterRestrict_determinant
      hT i zeta eta iZ j hj hZ hZ' hA cA,
    centralizingUnipotentCentralizerIntersectionAction_characterRestrict_determinant
      hT i eta zeta iZ j hj hZ' hZ hB cB,
    centralizingUnipotentIntersectionAction_characterRestrict_determinant
      hT i zeta eta iZ j hj hZ hZ' hC cC]
  rw [hroot.positiveWeightCharacter_balance hT zeta eta]
  congr 2
  congr 1
  funext α
  exact propext (and_comm ..)

/-- On image points of the displayed common split torus, the two full
determinants equal the two axis determinants times the square of the
common-positive determinant. -/
theorem rationalCharacterEval_centralizingDeterminant_product_square
    (t : rationalPoints T.toGrp) :
    rationalCharacterEval
        ((centralizingUnipotentAction
          (CommGroupScheme.groupHom zeta ≫ i) iZ hZ hU).determinantCharacter cU)
        (rationalPoints.map j t) *
      rationalCharacterEval
        ((centralizingUnipotentAction
          (CommGroupScheme.groupHom eta ≫ i) iZ hZ' hV).determinantCharacter cV)
        (rationalPoints.map j t) =
      rationalCharacterEval
        ((centralizingUnipotentCentralizerIntersectionAction
          (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
          iZ hZ hZ' hA).determinantCharacter cA)
        (rationalPoints.map j t) *
      rationalCharacterEval
        ((centralizingUnipotentCentralizerIntersectionAction
          (CommGroupScheme.groupHom eta ≫ i) (CommGroupScheme.groupHom zeta ≫ i)
          iZ hZ' hZ hB).determinantCharacter cB)
        (rationalPoints.map j t) *
      (rationalCharacterEval
        ((centralizingUnipotentIntersectionAction
          (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
          iZ hZ hZ' hC).determinantCharacter cC)
        (rationalPoints.map j t)) ^ 2 := by
  have h := congrArg (fun χ => rationalCharacterEval χ t)
    (characterRestrict_centralizingDeterminant_balance
      hroot hT zeta eta iZ hZ hZ' hU hV hA hB hC j hj cU cV cA cB cC)
  simpa only [rationalCharacterEval_characterRestrict, rationalCharacterEval_add,
    two_smul, pow_two] using h

end Balance

end Dynamic

end Langlands.GroupScheme
