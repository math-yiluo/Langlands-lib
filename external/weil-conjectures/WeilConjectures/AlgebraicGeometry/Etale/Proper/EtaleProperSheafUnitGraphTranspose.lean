/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperGraphTransfer.EtaleProperGraphTransfer
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

import WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperSheafGraphMap
import WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperSheafTransposeNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperGraphTransferNormalization
import all WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperGraphDerivedMate

/-! # The graph transpose of the normalized sheaf map -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance 2000] Abelian.toPreadditive
attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  derivedEtaleLowerShriekUpperStarAdjunction etaleLowerShriekUpperStarAdjunction

/-- A sheaf map normalized into the common direct image has the graph transfer as
its transpose after passage through the right-derived units.
Source: Stacks Project, Tag 0F7B, case (b), and Tag 0F4L, graph support description.
(blueprint: lem-pur-proper-sheaf-unit-graph-transpose).

Proof in words: on sheaves, transpose tau under v_! adjoint to v^*, and follow by
base change for c.g. Its restriction to the clopen graph is the adjunction unit
for c.i. Its restriction to the complementary open is zero. To see this, compose
with the inclusion into the common direct image; hτ gives exactly the proper
support inclusion, and that inclusion is monic. Thus the transpose is proper
composition through the graph followed by its extension-by-zero unit.
Apply this equality degreewise. The mixed derived mate unit formula transports
ordinary base change to exact derived base change. Naturality of the
right-derived units and the unit identity for proper direct-image composition
move the q-unit to the front. The derived comparison for the clopen graph is
the derived sheaf isomorphism, so its unit cancels. What remains is the displayed
transfer, with the q-unit in front. This calculation uses only the sheaf map,
base change and ordinary derived direct images; it makes no reference to
compact-support composition or its chosen comparisons. -/
theorem properSheafUnit_graph_transpose
    (A : Type (u + 1)) [CommRing A]
    {W V Y : Scheme.{u}}
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v]
    {f : W ⟶ Y} (hf : f = q ≫ v)
    (c : Compactification f)
    (τ : lowerStar (ModuleCat.{u + 1} A) q ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (hτ : ∀ F : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A),
      τ.app F ≫ (compactificationSheafToDirectImage A c).app F =
        etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
            ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) q v f hf).hom.app F)
    (J : HomotopyCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance).homEquiv
        _ _
        ((etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategoryFactorsh.hom.app
            ((lowerStar (ModuleCat.{u + 1} A) q).mapHomotopyCategory (.up ℤ) |>.obj J) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app J) ≫
          (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
            (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
            (lowerStar (ModuleCat.{u + 1} A) c.g)).app J) ≫
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback c.g v).toCommSq).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
            (DerivedCategory.Qh.obj J)) =
      (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctorUnit.app J ≫
        ProperGraphTransfer.transfer q v hf c A (DerivedCategory.Qh.obj J) := by
  have hs := homotopy_normalized_transpose
    (lowerStar (ModuleCat.{u + 1} A) q)
    (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance)
    (upperStar (ModuleCat.{u + 1} A) v)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
    (lowerStar (ModuleCat.{u + 1} A) c.g)
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst c.g v))
    (lowerStar (ModuleCat.{u + 1} A) (pullback.snd c.g v))
    (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
    τ (baseChangeMap (ModuleCat.{u + 1} A) (IsPullback.of_hasPullback c.g v).toCommSq)
    (lowerStar (ModuleCat.{u + 1} A) (ProperGraphTransfer.graph q v hf c))
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) (ProperGraphTransfer.graph q v hf c))
    (lowerStarComp (ModuleCat.{u + 1} A) (ProperGraphTransfer.graph q v hf c)
      (pullback.snd c.g v) q (ProperGraphTransfer.graph_snd q v hf c).symm).inv
    (asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A)
      (ProperGraphTransfer.graph q v hf c))).inv
    (openImmersionLowerShriekBaseChange (ModuleCat.{u + 1} A)
      (ProperGraphTransfer.graph q v hf c) (pullback.fst c.g v) c.i
      (ProperGraphTransfer.graph_fst q v hf c))
    (properSheaf_graph_map A q v hf c τ hτ) J
  erw [properSheaf_transpose_normal A q v c τ J,
    properGraphTransfer_normal A q v hf c J, hs]

end AlgebraicGeometry.Etale
