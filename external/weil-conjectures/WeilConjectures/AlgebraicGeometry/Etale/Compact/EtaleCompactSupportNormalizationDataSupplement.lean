/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.AlgebraicGeometry.EtaleCompactificationGraphMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.BaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportNormalizationData

/-!
# Constructed graph comparisons for compact supports

Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tag 03S6
(blueprint: def-asd-compact-support-graph-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The compact-support exchange as a 2-square, for canonical pasting.
Source: SGA 4 XVII 5.2.2
(blueprint: def-asd-compact-support-graph-comparison). -/
noncomputable def exactCompactSupportExchangeSquare
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    {f : U ⟶ X} (c : Compactification f) (g : X' ⟶ X) :=
  TwoSquare.mk _ _ _ _ (exactCompactSupportExchange A c g)

/-- The specified sum exchange as a 2-square, for the same canonical pasting.
Source: Stacks Project Tag 03S6
(blueprint: def-asd-compact-support-graph-comparison). -/
noncomputable def exactEtaleSumExchangeSquare
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    (f : U ⟶ X) [Etale f] (g : X' ⟶ X) :=
  TwoSquare.mk _ _ _ _ (exactEtaleSumExchange A f g).hom

/-- Regard a proper refinement as a compactification of the coarser open immersion.
Source: SGA 4 XVII 6.2.11
(blueprint: def-asd-compact-support-graph-comparison). -/
def refinementOpenCompactification
    {U X : Scheme.{u}} {f : U ⟶ X} {c d : Compactification f}
    (r : c.Refinement d) : Compactification d.i where
  Z := c.Z
  g := r.hom
  i := c.i
  comm := r.i_hom.symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

section IdentityNormalization
attribute [local instance 2000] Abelian.toPreadditive

/-- Identity normalization: remove the exact derived direct image of the identity.
Source: SGA 4 XVII 6.2.11
(blueprint: def-asd-compact-support-graph-comparison). -/
noncomputable def identityEtaleCompactSupportComparison
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper (𝟙 X)) ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) inferInstance).mapDerivedCategory :=
  Functor.isoWhiskerLeft
      (etaleLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) inferInstance).mapDerivedCategory
      ((lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
        Functor.mapDerivedCategoryIdIso _) ≪≫
    Functor.rightUnitor _

end IdentityNormalization

/-- Core comparison data: the geometric and degreewise normalization maps.
Source: SGA 4 XVII 5.2.2 and 6.2.11 (blueprint: def-asd-compact-support-graph-comparison). -/
structure EtaleCompactSupportCore (A : Type (u + 1)) [CommRing A] where
  comparison : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f),
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory
  /-- Inverse comparison on sheaves: extend each sheet section by zero off its graph. -/
  sheafComparison : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f),
    etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g
  /-- The sheaf map is the specified graph-extension map inside direct image. -/
  sheaf_normalization : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f) (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
    (sheafComparison f c).app M ≫ (compactificationSheafToDirectImage A c).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M
  /-- On every homotopy representative, descend the preceding sheaf map degreewise and
  then apply the total-right-derived unit. -/
  derived_normalization : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f)
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (ComplexShape.up ℤ)),
    (comparison f c).inv.app (DerivedCategory.Qh.obj K) =
      compactSupportComparisonOnHomotopy A f c (sheafComparison f c) K

/-- Base-change, refinement and identity equations for normalized core data. -/
structure EtaleCompactSupportCoherence (A : Type (u + 1)) [CommRing A]
    (core : EtaleCompactSupportCore A) : Prop where
  base_change : ∀ {U X X' : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [QuasiCompact f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian X'] [CompactSpace X'] (c : Compactification f) (g : X' ⟶ X),
    exactCompactSupportExchange A c g ≫
        Functor.whiskerLeft
          (upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory
          (core.comparison (pullback.fst g f)
            (c.ofIsPullback (IsPullback.of_hasPullback g f).flip)).hom =
      Functor.whiskerRight (core.comparison f c).hom
          (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≫
        (exactEtaleSumExchange A f g).hom
  /-- Under a proper refinement, use the core.comparison for the coarser open immersion,
  normalized by graph extension (hence identity over U), and then compose direct images. -/
  refinement : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c d : Compactification f) (r : c.Refinement d)
    [IsLocallyNoetherian d.Z] [CompactSpace d.Z],
    Functor.whiskerRight (core.comparison d.i (refinementOpenCompactification r)).inv
        (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} A) r.hom)
          (lowerStar (ModuleCat.{u + 1} A) d.g)
          (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm)).hom ≫
      (core.comparison f c).hom = (core.comparison f d).hom
  /-- For an identity morphism the normalized core.comparison is the identity after removing
  the identity functor. Refinement compatibility supplies every other compactification. -/
  identity : ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X],
    core.comparison (𝟙 X) (Compactification.ofIsProper (𝟙 X)) =
      identityEtaleCompactSupportComparison A X

end AlgebraicGeometry.Etale
