import Langlands.GroupScheme.Rational.EvenChainPatternProducts
import Langlands.GroupScheme.Torus.FundamentalWeightPermutation
import Langlands.GroupScheme.Torus.KernelDiagonalizable
import Langlands.GroupScheme.SimplyConnected.SplitNecessity

/-! # Actual simple-coroot coordinates on a pinned torus -/

noncomputable section

local instance : ∀ (α : Sort*), DecidableEq α := Classical.decEq

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G) (hspan : p.rootDatum.corootSpan ℤ = ⊤)

/-- The actual torus point supplied by a simple coroot and a unit coordinate. -/
def simpleCorootPoint (a : p.base.support) : kˣ →* rationalPoints p.torus.toGrp :=
  (rationalPoints.map (CommGroupScheme.groupHom (p.rootDatum.coroot a))).comp
    (Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm.toMonoidHom

/-- Evaluation at the integral fundamental weight dual to the specified simple coroot. -/
def fundamentalWeightEval (a : p.base.support) :
    rationalPoints p.torus.toGrp →* kˣ :=
  rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm
    (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan a))

private theorem eval_cocharacter (χ : characterLattice p.torus)
    (ν : cocharacterLattice p.torus) (t : kˣ) :
    rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm χ)
      ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm t ≫
        (CommGroupScheme.groupHom ν).hom.hom) =
      t ^ latticePairing p.torus χ ν := by
  rw [rationalCharacterEval_apply]
  change Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))
    (((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm t ≫
      (CommGroupScheme.groupHom ν).hom.hom) ≫
      (CommGroupScheme.groupHom χ).hom.hom) = _
  rw [Category.assoc]
  change Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))
    ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm t ≫
      (CommGroupScheme.groupHom (ν ≫ χ)).hom.hom) = _
  conv_lhs => rw [← (gmEndEquiv k).symm_apply_apply (ν ≫ χ)]
  rw [gmEndEquiv_symm_comp, map_zpow, MulEquiv.apply_symm_apply, latticePairing_apply]

@[simp]
theorem fundamentalWeightEval_simpleCorootPoint (a b : p.base.support) (t : kˣ) :
    p.fundamentalWeightEval hspan a (p.simpleCorootPoint b t) =
      if b = a then t else 1 := by
  classical
  unfold fundamentalWeightEval simpleCorootPoint
  simp only [MonoidHom.comp_apply, rationalPoints.map_apply, MulEquiv.coe_toMonoidHom]
  rw [eval_cocharacter,
    ← p.isRootDatum.1, Langlands.RootDatum.fundamentalWeightBasis_pairing]
  split_ifs <;> simp

/-- The commutative product of all actual simple-coroot points. -/
def simpleCorootProduct (c : p.base.support → kˣ) : rationalPoints p.torus.toGrp :=
  ∏ a, p.simpleCorootPoint a (c a)

@[simp]
theorem fundamentalWeightEval_simpleCorootProduct (c : p.base.support → kˣ)
    (a : p.base.support) :
    p.fundamentalWeightEval hspan a (p.simpleCorootProduct c) = c a := by
  classical
  simp [simpleCorootProduct, map_prod]

private def pointWeightValues (x : rationalPoints p.torus.toGrp) :
    characterLattice p.torus →+ Additive kˣ where
  toFun χ := Additive.ofMul
    (rationalCharacterEval ((rationalCharacters.equivCharacterLattice p.torus).symm χ) x)
  map_zero' := by
    simp [rationalCharacterEval_zero]
  map_add' χ ψ := by
    simp only [map_add, rationalCharacterEval_add]
    rfl

/-- Fundamental weights separate actual points of the split pinned torus. -/
theorem eq_of_fundamentalWeightEval_eq {x y : rationalPoints p.torus.toGrp}
    (h : ∀ a, p.fundamentalWeightEval hspan a x =
      p.fundamentalWeightEval hspan a y) :
    x = y := by
  have he : p.pointWeightValues x = p.pointWeightValues y := by
    apply AddMonoidHom.toIntLinearMap_injective
    apply (Langlands.RootDatum.fundamentalWeightBasis p.rootDatum p.base hspan).ext
    intro a
    exact congrArg Additive.ofMul (h a)
  apply (characterLattice.pointCharactersEquiv p.torus p.isSplitTorus _).injective
  apply MonoidHom.ext
  intro χ
  have hc := congrArg (fun f : characterLattice p.torus →+ Additive kˣ => f χ.toAdd) he
  change Additive.ofMul (rationalCharacterEval
      ((rationalCharacters.equivCharacterLattice p.torus).symm χ.toAdd) x) =
    Additive.ofMul (rationalCharacterEval
      ((rationalCharacters.equivCharacterLattice p.torus).symm χ.toAdd) y) at hc
  have hu := congrArg Additive.toMul hc
  exact Units.map_injective
    (f := (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom)
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.injective hu

/-- Every torus point is the product of its simple-coroot coordinates. -/
theorem simpleCorootProduct_fundamentalWeightEval (x : rationalPoints p.torus.toGrp) :
    p.simpleCorootProduct (fun a => p.fundamentalWeightEval hspan a x) = x := by
  apply p.eq_of_fundamentalWeightEval_eq hspan
  intro a
  exact p.fundamentalWeightEval_simpleCorootProduct hspan _ a

/-- Simple-coroot coordinates identify the actual torus points with a product of units. -/
def simpleCorootCoordinates : rationalPoints p.torus.toGrp ≃*
    (p.base.support → kˣ) where
  toFun x a := p.fundamentalWeightEval hspan a x
  invFun := p.simpleCorootProduct
  left_inv := p.simpleCorootProduct_fundamentalWeightEval hspan
  right_inv c := funext (p.fundamentalWeightEval_simpleCorootProduct hspan c)
  map_mul' x y := by
    funext a
    exact map_mul (p.fundamentalWeightEval hspan a) x y

/-- Algebraic simple connectedness supplies the full integral coroot span. -/
theorem simpleCorootSpan_eq_top (hG : IsSimplyConnected G) :
    p.rootDatum.corootSpan ℤ = ⊤ :=
  splitSimplyConnectedCorootSpan k G hG p.torus p.isSplitTorus
    p.inclusion p.isMaximalTorus p.rootIndex p.rootDatum p.isRootDatum
    p.isReduced

end Langlands.GroupScheme.SplitPinning
