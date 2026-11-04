import Langlands.Representation.Aubert.General.UnipotentCentralizerHaarDeterminant
import Langlands.Representation.Aubert.General.UnipotentIntersectionHaarDeterminant
import Langlands.Representation.Jacquet.PositiveCharacter

/-! # Actual Haar balance on the common split-torus image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

section Character

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G Z : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The forward Haar character of the original centralizing point map on
the full dynamic unipotent subgroup. -/
def centralizingUnipotentHaarCharacter :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [IsTopologicalGroup (RationalPoint k G.X)]
      (chi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (iZ : Z ⟶ G)
      (_hZ : SubgroupFunctor.range iZ ≤ Dynamic.centralizer chi)
      (_hUc : IsClosed ((Dynamic.unipotent chi).carrier (Over.mk (𝟙 _)) :
        Set (RationalPoint k G.X))),
      rationalPoints Z →* ℝ≥0ˣ := by
  intro _ _ chi iZ hZ hUc
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  exact (HaarModulus.closedNormalizerCharacter _ hUc).comp
    (Dynamic.centralizingUnipotentNormalizerHom chi iZ hZ)

end Character

section Commuting

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
  (i : T.toGrp ⟶ G) (alpha beta : (Gm S).toGrp ⟶ T.toGrp)

private theorem range_cocharacter_le_commonCentralizer :
    SubgroupFunctor.range (alpha ≫ i) ≤ Dynamic.centralizer (beta ≫ i) := by
  intro V x hx
  apply torusCentralizer_le_dynamicCentralizer i beta V
  apply range_le_torusCentralizer i V
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨t ≫ alpha.hom.hom, ?_⟩
  change (t ≫ alpha.hom.hom) ≫ i.hom.hom = t ≫ (alpha ≫ i).hom.hom
  rw [Grp.comp_hom_hom, Category.assoc]

end Commuting

section Balance

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

local instance commonCentralizerHaarBalancePointTopology : TopologicalSpace (RationalPoint k G.X) := pointTopology

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

/-- The actual forward Haar characters satisfy the five-subgroup product
identity after pullback along the displayed common split torus. -/
theorem centralizingHaarCharacter_product_square_on_torus :
    (deltaU * deltaV).comp (rationalPoints.map j) =
      (deltaA * deltaB * deltaC ^ 2).comp (rationalPoints.map j) := by
  apply MonoidHom.ext
  intro t
  apply Units.ext
  change (deltaU (rationalPoints.map j t) : ℝ≥0) *
      (deltaV (rationalPoints.map j t) : ℝ≥0) =
    (deltaA (rationalPoints.map j t) : ℝ≥0) *
      (deltaB (rationalPoints.map j t) : ℝ≥0) *
      (deltaC (rationalPoints.map j t) : ℝ≥0) ^ 2
  rw [show (deltaU (rationalPoints.map j t) : ℝ≥0) = _ from
      smoothAffineCentralizingUnipotentHaarDeterminant G chi iZ hZ hU cU hUc _,
    show (deltaV (rationalPoints.map j t) : ℝ≥0) = _ from
      smoothAffineCentralizingUnipotentHaarDeterminant G psi iZ hZ' hV cV hVc _,
    unipotentCentralizerHaarDeterminant G chi psi
      (range_cocharacter_le_commonCentralizer i
        (CommGroupScheme.groupHom zeta) (CommGroupScheme.groupHom eta))
      iZ hZ hZ' hA cA hAc,
    unipotentCentralizerHaarDeterminant G psi chi
      (range_cocharacter_le_commonCentralizer i
        (CommGroupScheme.groupHom eta) (CommGroupScheme.groupHom zeta))
      iZ hZ' hZ hB cB hBc,
    unipotentIntersectionHaarDeterminant G chi psi
      (range_cocharacter_le_commonCentralizer i
        (CommGroupScheme.groupHom zeta) (CommGroupScheme.groupHom eta))
      iZ hZ hZ' hC cC hCc]
  rw [← map_mul, ← map_mul, ← map_pow, ← map_mul]
  exact congrArg (MeasureTheory.distribHaarChar k)
    (Dynamic.rationalCharacterEval_centralizingDeterminant_product_square
      hroot hT zeta eta iZ hZ hZ' hU hV hA hB hC j hj cU cV cA cB cC t)

/-- Canonical positive square roots turn the same actual Haar balance into
the half-modulus identity, retaining the full common-intersection factor. -/
theorem centralizingHaarCharacter_positiveHalf_product_on_torus :
    (Jacquet.positiveHalfCharacter deltaU * Jacquet.positiveHalfCharacter deltaV).comp
        (rationalPoints.map j) =
      (Jacquet.positiveHalfCharacter deltaA * Jacquet.positiveHalfCharacter deltaB *
        deltaC).comp (rationalPoints.map j) := by
  have h := centralizingHaarCharacter_product_square_on_torus
    hroot hT zeta eta iZ hZ hZ' hU hV hA hB hC j hj cU cV cA cB cC
    hUc hVc hAc hBc hCc
  apply MonoidHom.ext
  intro t
  have ht := congrArg (fun f : rationalPoints T.toGrp →* ℝ≥0ˣ => f t) h
  have hs := congrArg (Units.map NNReal.sqrtHom.toMonoidHom) ht
  simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.pow_apply,
    map_mul, map_pow] at hs
  change Jacquet.positiveHalfCharacter deltaU (rationalPoints.map j t) *
      Jacquet.positiveHalfCharacter deltaV (rationalPoints.map j t) =
    Jacquet.positiveHalfCharacter deltaA (rationalPoints.map j t) *
      Jacquet.positiveHalfCharacter deltaB (rationalPoints.map j t) *
      Jacquet.positiveHalfCharacter deltaC (rationalPoints.map j t) ^ 2 at hs
  rw [Jacquet.positiveHalfCharacter_sq] at hs
  exact hs

/-- The inverse half characters used by normalized Jacquet functors retain
the inverse of the full common-intersection modulus on the common torus. -/
theorem centralizingHaarCharacter_inverseHalf_product_on_torus :
    (Jacquet.inverseHalfCharacter deltaU * Jacquet.inverseHalfCharacter deltaV).comp
        (rationalPoints.map j) =
      (Jacquet.inverseHalfCharacter deltaA * Jacquet.inverseHalfCharacter deltaB *
        (Jacquet.complexCharacter deltaC)⁻¹).comp (rationalPoints.map j) := by
  have h := centralizingHaarCharacter_positiveHalf_product_on_torus
    hroot hT zeta eta iZ hZ hZ' hU hV hA hB hC j hj cU cV cA cB cC
    hUc hVc hAc hBc hCc
  apply MonoidHom.ext
  intro t
  have ht := congrArg (fun f : rationalPoints T.toGrp →* ℝ≥0ˣ => f t) h
  have hc := congrArg
    (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom) ht
  simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, map_mul] at hc
  change Jacquet.complexCharacter (Jacquet.positiveHalfCharacter deltaU)
        (rationalPoints.map j t) *
      Jacquet.complexCharacter (Jacquet.positiveHalfCharacter deltaV)
        (rationalPoints.map j t) =
    Jacquet.complexCharacter (Jacquet.positiveHalfCharacter deltaA)
        (rationalPoints.map j t) *
      Jacquet.complexCharacter (Jacquet.positiveHalfCharacter deltaB)
        (rationalPoints.map j t) *
      Jacquet.complexCharacter deltaC (rationalPoints.map j t) at hc
  simpa only [Jacquet.inverseHalfCharacter, MonoidHom.comp_apply,
    MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv] using congrArg Inv.inv hc

end Balance

end Langlands.Aubert.General.RationalPointFamily
