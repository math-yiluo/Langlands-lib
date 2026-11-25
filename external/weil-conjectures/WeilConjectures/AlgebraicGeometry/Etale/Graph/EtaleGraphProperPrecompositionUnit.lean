/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphChosenComparisons
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale

import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphProperPrecompositionUnitKInjective

/-! # A proper-first tower compared with one compactification

Source: Stacks Project, Tags 0F7B, 0F7I and 0F7J.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor canonicalEtaleCompactSupportComparison
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

/-- Normalize just the proper-first tower against a single compactification of its composite.
There is no second proper/etale factorization in this assertion.
Source: Stacks Project, more-etale.tex Tags 0F7B, 0F7I and 0F7J; graph normalization:
etale-cohomology.tex Tag 0F4L.
(blueprint: lem-pur-graph-proper-precomposition-unit).

Proof in words: compactify v by d and q followed by d.i by e. The every-tower formula
computes the chosen composition by the proper/open interchange for this tower. On a
K-injective complex J on W, q_*J is K-injective. Expand the inverse graph comparison for v:
it is degreewise graph extension followed by the right-derived unit of d.g. The
proper/open interchange is the section-preserving map of Tag 0F7B followed by direct
image of a resolution map. The sheaf composition identifies its sections with the
proper-support subsheaf for q followed by v. The normalization of tau identifies its
sections with that same subsheaf, because the compactification inclusion is monic.
The graph refinement equation and the normalized refinement equation transport this
calculation from d.comp e to c; the refinement cocycle makes the transport independent
of the common refinement. Naturality of the right-derived units then identifies the
result with degreewise tau followed by the unit for c.g. This is the asserted equality
on J. For an arbitrary complex, map it to a K-injective resolution and use naturality:
the target functor factors through Qh, so its map of that resolution is invertible and
can be cancelled. This proves the equality on every homotopy object. Identity proper
maps remove an identity-open factor; empty schemes and zero coefficients give zero maps.
No exactness of q_* and no Cartesian square are used. -/
theorem graph_proper_precomposition_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W V Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian V] [IsNoetherian Y]
    (q : W ⟶ V) [IsProper q]
    (v : V ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    [HasCompactification v] [HasCompactification (q ≫ v)]
    {f : W ⟶ Y} (hf : f = q ≫ v) [HasCompactification f]
    (c : Compactification f)
    (τ : lowerStar (ModuleCat.{u + 1} A) q ⋙
        etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (hτ : ∀ F : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A),
      τ.app F ≫ (compactificationSheafToDirectImage A c).app F =
        etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) v
            ((lowerStar (ModuleCat.{u + 1} A) q).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) q v f hf).hom.app F) :
    Functor.rightDerivedFunctorCompMapDerivedCategoryUnit
        (lowerStar (ModuleCat.{u + 1} A) q)
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance) ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
            (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≪≫
          Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q)
            (graphChosenEtaleComparison A v).symm ≪≫
          unboundedEtaleLowerShriekCompIso A q v ≪≫
          unboundedEtaleLowerShriekCongr A hf.symm ≪≫
          (rightDerivedLowerShriekIso A c).symm).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (.up ℤ)) DerivedCategory.Qh ≫
        Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
      (lowerStar (ModuleCat.{u + 1} A) c.g) := by
  apply NatTrans.ext
  funext J
  exact graph_proper_precomposition_unit_component A q v hf c τ hτ J

end AlgebraicGeometry.Etale
