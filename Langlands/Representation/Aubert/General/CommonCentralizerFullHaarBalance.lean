import Langlands.Representation.Aubert.General.CommonCentralizerHaarBalance

/-! # Full common-centralizer Haar balance under character detection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.Dynamic

section Determinants

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

local notation "DU" => AutomorphicAction.determinantCharacter (centralizingUnipotentAction
  (CommGroupScheme.groupHom zeta ≫ i) iZ hZ hU) cU
local notation "DV" => AutomorphicAction.determinantCharacter (centralizingUnipotentAction
  (CommGroupScheme.groupHom eta ≫ i) iZ hZ' hV) cV
local notation "DA" => AutomorphicAction.determinantCharacter (centralizingUnipotentCentralizerIntersectionAction
  (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
  iZ hZ hZ' hA) cA
local notation "DB" => AutomorphicAction.determinantCharacter (centralizingUnipotentCentralizerIntersectionAction
  (CommGroupScheme.groupHom eta ≫ i) (CommGroupScheme.groupHom zeta ≫ i)
  iZ hZ' hZ hB) cB
local notation "DC" => AutomorphicAction.determinantCharacter (centralizingUnipotentIntersectionAction
  (CommGroupScheme.groupHom zeta ≫ i) (CommGroupScheme.groupHom eta ≫ i)
  iZ hZ hZ' hC) cC

/-- The actual additive determinant discrepancy for the five subgroups.
Its evaluation is the product of the two full determinants divided by both
axis determinants and the squared common-intersection determinant. -/
def centralizingDeterminantBalanceDefect : rationalCharacters Z :=
  DU + DV - (DA + DB + 2 • DC)

include hroot hT hj

/-- The five-factor discrepancy restricts to zero on the displayed split
torus, without any character detection hypothesis. -/
theorem characterRestrict_centralizingDeterminantBalanceDefect_eq_zero :
    characterRestrict j
      (centralizingDeterminantBalanceDefect zeta eta iZ hZ hZ' hU hV hA hB hC
        cU cV cA cB cC) = 0 := by
  rw [centralizingDeterminantBalanceDefect, map_sub,
    characterRestrict_centralizingDeterminant_balance
      hroot hT zeta eta iZ hZ hZ' hU hV hA hB hC j hj cU cV cA cB cC, sub_self]

/-- Explicit detection upgrades vanishing of the restricted five-factor
discrepancy to vanishing of the actual character on the acting group. -/
theorem centralizingDeterminantBalanceDefect_eq_zero_of_characterRestrict_injective
    (hinj : Function.Injective (characterRestrict j)) :
    centralizingDeterminantBalanceDefect zeta eta iZ hZ hZ' hU hV hA hB hC
      cU cV cA cB cC = 0 := by
  apply hinj
  rw [map_zero]
  exact characterRestrict_centralizingDeterminantBalanceDefect_eq_zero
    hroot hT zeta eta iZ hZ hZ' hU hV hA hB hC j hj cU cV cA cB cC

/-- Character detection extends the five-factor determinant balance from the
common split torus to the entire acting group. -/
theorem centralizingDeterminant_balance_of_characterRestrict_injective
    (hinj : Function.Injective (characterRestrict j)) :
    DU + DV = DA + DB + 2 • DC :=
  hinj (characterRestrict_centralizingDeterminant_balance
    hroot hT zeta eta iZ hZ hZ' hU hV hA hB hC j hj cU cV cA cB cC)

/-- Evaluate the detected five-factor determinant equality at any original
rational point of the acting group. -/
theorem rationalCharacterEval_centralizingDeterminant_product_square_of_characterRestrict_injective
    (hinj : Function.Injective (characterRestrict j)) (z : rationalPoints Z) :
    rationalCharacterEval DU z * rationalCharacterEval DV z =
      rationalCharacterEval DA z * rationalCharacterEval DB z *
        (rationalCharacterEval DC z) ^ 2 := by
  have h := congrArg (fun χ => rationalCharacterEval χ z)
    (centralizingDeterminant_balance_of_characterRestrict_injective
      hroot hT zeta eta iZ hZ hZ' hU hV hA hB hC j hj cU cV cA cB cC hinj)
  simpa only [rationalCharacterEval_add, two_smul, pow_two] using h

end Determinants

end Langlands.GroupScheme.Dynamic

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

section Haar

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z U V A B C : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  [IsAffine Z.X.left]
  [IsAffineHom U.X.hom] [IsAffineHom V.X.hom]
  [IsAffineHom A.X.hom] [IsAffineHom B.X.hom] [IsAffineHom C.X.hom]
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
  (zeta eta : cocharacterLattice T)
  (iZ : Z ⟶ G)

variable
  (hZ : SubgroupFunctor.range iZ ≤
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i))
  (hZ' : SubgroupFunctor.range iZ ≤
    Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i))
  {iU : U ⟶ G} {iV : V ⟶ G} {iA : A ⟶ G} {iB : B ⟶ G} {iC : C ⟶ G}
  (hU : (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy iU)
  (hV : (Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iV)
  (hA : (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
    Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iA)
  (hB : (Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i) ⊓
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy iB)
  (hC : (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
    Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iC)
  (j : T.toGrp ⟶ Z) (hj : j ≫ iZ = i)
  {dU dV dA dB dC : ℕ}
  (cU : Lie.FiniteCoordinates U dU) (cV : Lie.FiniteCoordinates V dV)
  (cA : Lie.FiniteCoordinates A dA) (cB : Lie.FiniteCoordinates B dB)
  (cC : Lie.FiniteCoordinates C dC)

local instance commonCentralizerFullHaarBalancePointTopology : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hUc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).carrier
    (Over.mk (𝟙 _)) :
    Set (RationalPoint k G.X)))
  (hVc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).carrier
    (Over.mk (𝟙 _)) :
    Set (RationalPoint k G.X)))
  (hAc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
    Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).carrier
    (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)))
  (hBc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i) ⊓
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier
    (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)))
  (hCc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
    Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).carrier
    (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)))

local notation "chi" => CommGroupScheme.groupHom zeta ≫ i
local notation "psi" => CommGroupScheme.groupHom eta ≫ i

local notation "deltaU" => centralizingUnipotentHaarCharacter chi iZ hZ hUc
local notation "deltaV" => centralizingUnipotentHaarCharacter psi iZ hZ' hVc
local notation "deltaA" => centralizingUnipotentCentralizerHaarCharacter chi psi iZ hZ hZ' hAc
local notation "deltaB" => centralizingUnipotentCentralizerHaarCharacter psi chi iZ hZ' hZ hBc
local notation "deltaC" => centralizingUnipotentIntersectionHaarCharacter chi psi iZ hZ hZ' hCc

include hroot hT hU hV hA hB hC hj cU cV cA cB cC

/-- Under explicit algebraic character detection, the five actual forward
Haar characters balance on the entire acting group. -/
theorem centralizingHaarCharacter_product_square_of_characterRestrict_injective
    (hinj : Function.Injective (characterRestrict j)) :
    deltaU * deltaV = deltaA * deltaB * deltaC ^ 2 := by
  have hchi : SubgroupFunctor.range chi ≤ Dynamic.centralizer psi := by
    intro W x hx
    apply torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom eta) W
    apply range_le_torusCentralizer i W
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨t ≫ (CommGroupScheme.groupHom zeta).hom.hom, ?_⟩
    rw [Grp.comp_hom_hom, Category.assoc]
  have hpsi : SubgroupFunctor.range psi ≤ Dynamic.centralizer chi := by
    intro W x hx
    apply torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom zeta) W
    apply range_le_torusCentralizer i W
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨t ≫ (CommGroupScheme.groupHom eta).hom.hom, ?_⟩
    rw [Grp.comp_hom_hom, Category.assoc]
  apply MonoidHom.ext
  intro z
  apply Units.ext
  change (deltaU z : ℝ≥0) * (deltaV z : ℝ≥0) =
    (deltaA z : ℝ≥0) * (deltaB z : ℝ≥0) * (deltaC z : ℝ≥0) ^ 2
  rw [show (deltaU z : ℝ≥0) = _ from
      smoothAffineCentralizingUnipotentHaarDeterminant G chi iZ hZ hU cU hUc z,
    show (deltaV z : ℝ≥0) = _ from
      smoothAffineCentralizingUnipotentHaarDeterminant G psi iZ hZ' hV cV hVc z,
    unipotentCentralizerHaarDeterminant G chi psi hchi iZ hZ hZ' hA cA hAc,
    unipotentCentralizerHaarDeterminant G psi chi hpsi iZ hZ' hZ hB cB hBc,
    unipotentIntersectionHaarDeterminant G chi psi hchi iZ hZ hZ' hC cC hCc]
  rw [← map_mul, ← map_mul, ← map_pow, ← map_mul]
  exact congrArg (MeasureTheory.distribHaarChar k)
    (Dynamic.rationalCharacterEval_centralizingDeterminant_product_square_of_characterRestrict_injective
      hroot hT zeta eta iZ hZ hZ' hU hV hA hB hC j hj cU cV cA cB cC hinj z)

/-- Positive square roots of the full Haar balance retain one complete
common-intersection modulus on the entire acting group. -/
theorem centralizingHaarCharacter_positiveHalf_product_of_characterRestrict_injective
    (hinj : Function.Injective (characterRestrict j)) :
    Jacquet.positiveHalfCharacter deltaU * Jacquet.positiveHalfCharacter deltaV =
      Jacquet.positiveHalfCharacter deltaA * Jacquet.positiveHalfCharacter deltaB *
        deltaC := by
  have h := centralizingHaarCharacter_product_square_of_characterRestrict_injective
    hroot hT zeta eta iZ hZ hZ' hU hV hA hB hC j hj cU cV cA cB cC
    hUc hVc hAc hBc hCc hinj
  apply MonoidHom.ext
  intro z
  have hz := congrArg (fun f : rationalPoints Z →* ℝ≥0ˣ => f z) h
  have hs := congrArg (Units.map NNReal.sqrtHom.toMonoidHom) hz
  simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, map_mul, map_pow] at hs
  change Jacquet.positiveHalfCharacter deltaU z *
      Jacquet.positiveHalfCharacter deltaV z =
    Jacquet.positiveHalfCharacter deltaA z *
      Jacquet.positiveHalfCharacter deltaB z *
      Jacquet.positiveHalfCharacter deltaC z ^ 2 at hs
  rw [Jacquet.positiveHalfCharacter_sq] at hs
  exact hs

/-- The two factorized correction expressions are reciprocal on every
acting point once the five actual Haar factors satisfy character detection. -/
theorem centralizingHaarCharacter_correctionProduct_eq_one_of_characterRestrict_injective
    (hinj : Function.Injective (characterRestrict j)) :
    (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter deltaV) *
        Jacquet.inverseHalfCharacter deltaB * Jacquet.inverseHalfCharacter deltaC) *
      (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter deltaU) *
        Jacquet.inverseHalfCharacter deltaA * Jacquet.inverseHalfCharacter deltaC) = 1 := by
  have h := centralizingHaarCharacter_positiveHalf_product_of_characterRestrict_injective
    hroot hT zeta eta iZ hZ hZ' hU hV hA hB hC j hj cU cV cA cB cC
    hUc hVc hAc hBc hCc hinj
  apply MonoidHom.ext
  intro z
  have hz := congrArg (fun f : rationalPoints Z →* ℝ≥0ˣ => f z) h
  have hc := congrArg
    (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom) hz
  simp only [MonoidHom.mul_apply, map_mul] at hc
  let u := Jacquet.complexCharacter (Jacquet.positiveHalfCharacter deltaU) z
  let v := Jacquet.complexCharacter (Jacquet.positiveHalfCharacter deltaV) z
  let a := Jacquet.complexCharacter (Jacquet.positiveHalfCharacter deltaA) z
  let b := Jacquet.complexCharacter (Jacquet.positiveHalfCharacter deltaB) z
  let c := Jacquet.complexCharacter (Jacquet.positiveHalfCharacter deltaC) z
  change u * v = a * b * Jacquet.complexCharacter deltaC z at hc
  have hsq := congrArg
    (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
    (Jacquet.positiveHalfCharacter_sq deltaC z)
  simp only [map_pow] at hsq
  change c ^ 2 = Jacquet.complexCharacter deltaC z at hsq
  rw [← hsq] at hc
  change (v * b⁻¹ * c⁻¹) * (u * a⁻¹ * c⁻¹) = 1
  calc
    _ = (u * v) * (a * b * c ^ 2)⁻¹ := by
      simp only [pow_two, mul_inv_rev]
      ac_rfl
    _ = 1 := by rw [hc, mul_inv_cancel]

end Haar

end Langlands.Aubert.General.RationalPointFamily
