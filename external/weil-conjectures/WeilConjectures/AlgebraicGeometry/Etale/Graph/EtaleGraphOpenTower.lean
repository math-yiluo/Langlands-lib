/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphOpenTowerFactor

/-! # Graph compatibility with the open leg

Source: Stacks Project, Tags 0F4L, 0F7B and 0F7J.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction mapDerivedUpperStarLowerStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

/-- Normalization of the etale-first composition through its open leg.
This involves only one compact-support composition, and no proper/etale interchange.
Source: Stacks Project, etale-cohomology.tex Tag 0F4L (graph comparison), and
more-etale.tex Tags 0F7B and 0F7J (the proper/open composition tower).
(blueprint: lem-pur-etale-graph-open-tower).

Proof in words:
Take the tower e over c. The every-tower composition formula writes the left
side using the compactification e.restrict of v'. Replace its inverse comparison
by the explicit graph-derived map. On sheaves, extending a sheet section first
to the clopen graph of v' and then across c.i agrees with extending it to the
graph of r = v' followed by c.i. Both sections agree on that graph and vanish
off it. The sheaf axiom, followed by sum-presheaf sheafification, identifies the
maps. Transposition under the two composite sum/open adjunctions identifies the
change of factorization with a inverse followed by s. Apply the equality
termwise, compose with the right-derived direct-image units, and use the unit
characterization of direct-image composition. The graph-derived component
formula and homotopy localization give the equality on every unbounded input.
Finally the normalized refinement equation and the comparison cocycle replace
the tower's terminal compactification by e.postcomp p. Identity opens reduce to
the triangle identities; empty graphs and zero coefficients give zero maps. -/
theorem etaleGraph_open_tower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Z' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Z']
    {f : X ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [Etale v'] [IsSeparated v'] [QuasiCompact v']
    [HasCompactification f] [HasCompactification v']
    [HasCompactification (v' ≫ f)] [QuasiCompact (v' ≫ f)]
    (c : Compactification f) (j' : X' ⟶ Z') [IsOpenImmersion j']
    (b : Z' ⟶ c.Z) [Etale b] [IsSeparated b]
    (osq : CommSq v' j' c.i b)
    (e : Compactification (v' ≫ c.i))
    [HasCompactification ((v' ≫ c.i) ≫ c.g)]
    (M : DerivedCategoryModule A X') :
    let r := v' ≫ c.i
    let p := c.g
    let va := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v' inferInstance
    let ba := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance
    let ja := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i
    let j'a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j'
    let a := (conjugateIsoEquiv (va.comp ja) (j'a.comp ba)).symm
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) osq.flip)
    let s := (conjugateIsoEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) r inferInstance)
      (j'a.comp ba)).symm
      (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) j' b r osq.w) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm)
    let dv' := (rightDerivedLowerShriekIso A
      (HasCompactification.compactification v')).symm ≪≫
      canonicalEtaleCompactSupportComparison A v' (HasCompactification.compactification v')
    let w : v' ≫ f = r ≫ p :=
      (congrArg (fun h : X ⟶ Y ↦ v' ≫ h) c.comm).trans (Category.assoc _ _ _).symm
    let l := Functor.isoWhiskerRight dv'.symm
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
      unboundedEtaleLowerShriekCompIso A v' f ≪≫ unboundedEtaleLowerShriekCongr A w
    let k := Functor.isoWhiskerRight
      (canonicalEtaleCompactSupportComparison A r e).symm
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) p) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.i).mapDerivedCategory
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g p) ≪≫
      rightDerivedLowerShriekIso A (e.postcomp p)
    (rightDerivedLowerShriekIso A c).hom.app
        ((etaleLowerShriek (ModuleCat.{u + 1} A) v' inferInstance).mapDerivedCategory.obj M) ≫
      l.hom.app M =
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) p).map (a.inv.app M) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) p).map (s.hom.app M) ≫ k.hom.app M := by
  dsimp only
  apply (cancel_mono ((Functor.isoWhiskerRight
    (canonicalEtaleCompactSupportComparison A (v' ≫ c.i) e).symm
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) e.i).mapDerivedCategory
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.g c.g) ≪≫
    rightDerivedLowerShriekIso A (e.postcomp c.g)).inv.app M)).1
  have h := etaleGraph_open_tower_factor A c j' b osq e M
  rw [Category.assoc, h]
  simp [Category.assoc]

end AlgebraicGeometry.Etale
