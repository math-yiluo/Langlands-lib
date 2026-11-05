import Langlands.GroupScheme.Dynamic.EqualCentralizerDeterminantBalance
import Langlands.Representation.Aubert.General.CommonCentralizerHaarBalance

/-! # Three-factor Haar balance for equal dynamic centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

section Balance

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z U V C : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  [IsAffine Z.X.left]
  [IsAffineHom U.X.hom] [IsAffineHom V.X.hom] [IsAffineHom C.X.hom]
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  (hroot : HasRelativeRootSystem i) (hT : IsSplitTorus T.toGrp)
  (zeta eta : cocharacterLattice T)
  (hEq : Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) =
    Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i))
  (iZ : Z ⟶ G)
  (hZ : SubgroupFunctor.range iZ ≤
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i))
  (hZ' : SubgroupFunctor.range iZ ≤
    Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i))
  {iU : U ⟶ G} {iV : V ⟶ G} {iC : C ⟶ G}
  (hU : (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy iU)
  (hV : (Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iV)
  (hC : (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
    Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy iC)
  (j : T.toGrp ⟶ Z) (hj : j ≫ iZ = i)
  {dU dV dC : ℕ}
  (cU : Lie.FiniteCoordinates U dU) (cV : Lie.FiniteCoordinates V dV)
  (cC : Lie.FiniteCoordinates C dC)

local instance equalCentralizerHaarBalancePointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hUc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).carrier
    (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)))
  (hVc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).carrier
    (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)))
  (hCc : IsClosed ((Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ⊓
    Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).carrier
    (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)))

local notation "chi" => CommGroupScheme.groupHom zeta ≫ i
local notation "psi" => CommGroupScheme.groupHom eta ≫ i
local notation "deltaU" => centralizingUnipotentHaarCharacter chi iZ hZ hUc
local notation "deltaV" => centralizingUnipotentHaarCharacter psi iZ hZ' hVc
local notation "deltaC" =>
  centralizingUnipotentIntersectionHaarCharacter chi psi iZ hZ hZ' hCc

include hroot hT hEq hU hV hC hj cU cV cC

/-- If character restriction detects the acting group, the actual forward
Haar characters of equal-centralizer radicals have the three-factor square
identity at every rational acting point. -/
theorem centralizingHaarCharacter_product_square_of_centralizer_eq
    (hinj : Function.Injective (characterRestrict j)) :
    deltaU * deltaV = deltaC ^ 2 := by
  have hchi : SubgroupFunctor.range chi ≤ Dynamic.centralizer psi := by
    rw [← hEq]
    exact Dynamic.range_le_centralizer chi
  apply MonoidHom.ext
  intro z
  apply Units.ext
  change (deltaU z : ℝ≥0) * (deltaV z : ℝ≥0) = (deltaC z : ℝ≥0) ^ 2
  rw [show (deltaU z : ℝ≥0) = _ from
      smoothAffineCentralizingUnipotentHaarDeterminant G chi iZ hZ hU cU hUc z,
    show (deltaV z : ℝ≥0) = _ from
      smoothAffineCentralizingUnipotentHaarDeterminant G psi iZ hZ' hV cV hVc z,
    unipotentIntersectionHaarDeterminant G chi psi hchi iZ hZ hZ' hC cC hCc]
  rw [← map_mul, ← map_pow]
  exact congrArg (MeasureTheory.distribHaarChar k)
    (Dynamic.rationalCharacterEval_centralizingDeterminant_square_of_centralizer_eq
      hroot hT zeta eta hEq iZ hZ hZ' hU hV hC j hj cU cV cC hinj z)

/-- In nonnegative-real values the full acting-group Haar balance is the
product of the two radical moduli equal to the squared intersection modulus. -/
theorem centralizingHaarCharacter_values_square_of_centralizer_eq
    (hinj : Function.Injective (characterRestrict j)) (z : rationalPoints Z) :
    (deltaU z : ℝ≥0) * (deltaV z : ℝ≥0) = (deltaC z : ℝ≥0) ^ 2 := by
  have h := congrArg (fun f : rationalPoints Z →* ℝ≥0ˣ => (f z : ℝ≥0))
    (centralizingHaarCharacter_product_square_of_centralizer_eq
      hroot hT zeta eta hEq iZ hZ hZ' hU hV hC j hj cU cV cC hUc hVc hCc hinj)
  exact h

end Balance

end Langlands.Aubert.General.RationalPointFamily
