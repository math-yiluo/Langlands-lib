/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows

/-! # Section-normalized ordinary scalar restriction

Source: Stacks Project, Tags 03CY, 03D7, 03D8, 03DA, 03DI, 03DJ and 0F7B;
blueprint fix-prop-coherence, coefficient comparisons of adjunction units and counits
(blueprint: def-sf-semilinear-scalar-ordinary-interface).

The interface records one simultaneous package on the actual ordinary
semilinear-system and strict-tower categories. Every comparison has a section or
adjunction normalization. The constant-tower beta, projector and alpha in the package
are fixed by the same intrinsic ordinary words as their varying-ring counterparts.
The existence and uniqueness theorems are in `SemilinearScalarOrdinaryComparison`.
No choice of a package is made into a definition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
  (B : Type (u + 1)) [CommRing B] (ψ : ∀ n : ℕ, CommRingCat.of B ⟶ R n)

/-- The given scalar map on constant sheaves, with no flatness condition.
Source: Stacks 03CZ (blueprint: lem-sf-semilinear-scalar-ordinary-comparison). -/
def ordinaryScalarMap (X : Scheme.{u}) (n : ℕ) :
    StrictTower.coefficients B X ⟶ coefficients R X n :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map (ψ n)

/-- The specified termwise ordinary inverse/direct-image adjunction.
Source: Stacks 03D7 (blueprint: lem-sf-semilinear-scalar-ordinary-comparison). -/
def scalarTowerAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    StrictTower.towerPullback B f ⊣ StrictTower.towerDirectImage B f :=
  (Scheme.proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
    (StrictTower.coefficients B X) (StrictTower.constantRingIso B f)).whiskerRight ℕᵒᵖ

/-- The specified termwise ordinary open adjunction.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-scalar-ordinary-comparison). -/
def scalarTowerOpenAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    StrictTower.towerJ B j ⊣ StrictTower.towerPullback B j :=
  (StrictTower.moduleJAdj B j).whiskerRight ℕᵒᵖ

/-- The ordinary constant-tower pullback square uses the recorded compositors.
Source: Stacks 03D8 (blueprint: lem-sf-semilinear-scalar-ordinary-comparison). -/
def scalarTowerSquare {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    StrictTower.towerPullback B i ⋙ StrictTower.towerPullback B r ≅
      StrictTower.towerPullback B p ⋙ StrictTower.towerPullback B k :=
  (StrictTower.towerGComp B r i).symm ≪≫
    eqToIso (congrArg (StrictTower.towerPullback B) h.symm) ≪≫
      StrictTower.towerGComp B k p

/-- The ordinary open compositor is the unit-preserving adjoint comparison.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-scalar-ordinary-comparison). -/
def scalarTowerOpenComp {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] :
    StrictTower.towerJ B j ⋙ StrictTower.towerJ B k ≅ StrictTower.towerJ B (j ≫ k) :=
  Adjunction.leftAdjointCompIso (scalarTowerOpenAdj B j) (scalarTowerOpenAdj B k)
    (scalarTowerOpenAdj B (j ≫ k)) (StrictTower.towerGComp B j k).symm

/-- Ordinary extension respects equality of the open scheme map.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-scalar-ordinary-comparison).
Proof: substitute the equality of maps. Proof irrelevance identifies the open-immersion
instances, so both chosen adjoints are definitionally the same functor. -/
theorem scalarTowerOpen_congr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    StrictTower.towerJ B f = StrictTower.towerJ B g := by
  subst g
  rfl

/-- All ordinary scalar comparisons with their defining normalizations. The level
isomorphisms identify the actual restricted module sheaves, including the B action;
transition and morphism equations retain the underlying section maps.
Source: Stacks 03D7, 03DI and 0F7B; blueprint fix-prop-coherence
(blueprint: lem-sf-semilinear-scalar-ordinary-comparison). -/
structure OrdinaryScalarComparison where
  /-- Restriction from actual semilinear systems to actual strict B towers. -/
  rho : ∀ X : Scheme.{u}, Modules R φ X ⥤ StrictTower.Towers B X
  /-- Additivity on the unchanged underlying maps. -/
  additive : ∀ X : Scheme.{u}, (rho X).Additive
  /-- Left exactness. -/
  limits : ∀ X : Scheme.{u}, PreservesFiniteLimits (rho X)
  /-- Right exactness, including nonflat scalar maps. -/
  colimits : ∀ X : Scheme.{u}, PreservesFiniteColimits (rho X)
  /-- Each level is the existing restriction-of-scalars functor. -/
  level : ∀ (X : Scheme.{u}) (n : ℕ),
    rho X ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) ≅
      eval R φ X n ⋙ res (ordinaryScalarMap R B ψ X n)
  /-- Identification is identity on sections. -/
  level_sections : ∀ (X : Scheme.{u}) (n : ℕ) (M : Modules R φ X) (H : X.ProEtᵒᵖ),
    ∀ x : (((rho X).obj M).obj (op n)).val.obj H,
      HEq (((level X n).hom.app M).val.app H x) x
  /-- Under the level identification all transitions are the original section restrictions. -/
  transitions : ∀ (X : Scheme.{u}) (M : Modules R φ X) (n : ℕ) (H : X.ProEtᵒᵖ)
      (x : (((rho X).obj M).obj (op (n + 1))).val.obj H),
    ((level X n).hom.app M).val.app H
        ((((rho X).obj M).map (homOfLE (Nat.le_succ n)).op).val.app H x) =
      M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 H.unop)).op
        (((level X (n + 1)).hom.app M).val.app H x)
  /-- The inverse-image coefficient comparison b. -/
  b : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    pull R φ f ⋙ rho X ≅ rho Y ⋙ StrictTower.towerPullback B f
  /-- The direct-image coefficient comparison d. -/
  d : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    push R φ f ⋙ rho Y ≅ rho X ⋙ StrictTower.towerDirectImage B f
  /-- Direct image is identity on precisely the prescribed fibre-product sections. -/
  d_sections : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ X)
      (n : ℕ) (H : Y.ProEtᵒᵖ),
    ∀ x : (((rho Y).obj ((push R φ f).obj M)).obj (op n)).val.obj H,
      HEq ((((d f).hom.app M).app (op n)).val.app H x) x
  /-- Both specified adjunction units are preserved. -/
  unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ Y),
    (rho Y).map ((moduleAdj R φ f).unit.app M) ≫
        (d f).hom.app ((pull R φ f).obj M) ≫
        (StrictTower.towerDirectImage B f).map ((b f).hom.app M) =
      (scalarTowerAdj B f).unit.app ((rho Y).obj M)
  /-- Both specified adjunction counits are preserved. -/
  counit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Modules R φ X),
    (StrictTower.towerPullback B f).map ((d f).hom.app N) ≫
        (scalarTowerAdj B f).counit.app ((rho X).obj N) =
      (b f).inv.app ((push R φ f).obj N) ≫
        (rho X).map ((moduleAdj R φ f).counit.app N)
  /-- The orientation is d = mate of the inverse of b. -/
  mate : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (mateEquiv (moduleAdj R φ f) (scalarTowerAdj B f) (b f).inv) = (d f).hom
  /-- Ordinary open-extension comparison a. -/
  a : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    extension R φ j ⋙ rho X ≅ rho U ⋙ StrictTower.towerJ B j
  /-- The prescribed open units normalize a. -/
  open_unit : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (M : Modules R φ U),
    (rho U).map ((moduleJAdj R φ j).unit.app M) ≫
        (b j).hom.app ((extension R φ j).obj M) ≫
        (StrictTower.towerPullback B j).map ((a j).hom.app M) =
      (scalarTowerOpenAdj B j).unit.app ((rho U).obj M)
  /-- The constant-tower cartesian open comparison, fixed by its transpose below. -/
  beta : ∀ {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (_h : gU ≫ j = j' ≫ g) (_hsq : IsPullback gU j' j g),
    StrictTower.towerJ B j ⋙ StrictTower.towerPullback B g ≅
      StrictTower.towerPullback B gU ⋙ StrictTower.towerJ B j'
  /-- The inverse beta is exactly the open-unit transpose. -/
  beta_unit : ∀ {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) (M : StrictTower.Towers B U),
    ((scalarTowerOpenAdj B j').homEquiv _ _)
        ((beta gU j' j g h hsq).inv.app M) =
      (StrictTower.towerPullback B gU).map ((scalarTowerOpenAdj B j).unit.app M) ≫
        (scalarTowerSquare B gU j' j g h).inv.app ((StrictTower.towerJ B j).obj M)
  /-- Restriction preserves that canonical beta, before deriving or evaluation. -/
  beta_comparison : ∀ {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (h : gU ≫ j = j' ≫ g) (hsq : IsPullback gU j' j g) (M : Modules R φ U),
    (rho X').map ((moduleBeta R φ gU j' j g h hsq).hom.app M) ≫
        (a j').hom.app ((pull R φ gU).obj M) ≫
        (StrictTower.towerJ B j').map ((b gU).hom.app M) =
      (b g).hom.app ((extension R φ j).obj M) ≫
        (StrictTower.towerPullback B g).map ((a j).hom.app M) ≫
        (beta gU j' j g h hsq).hom.app ((rho U).obj M)
  /-- The clopen extension/direct comparison, normalized by the inverse open unit. -/
  clopen : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s],
    StrictTower.towerJ B s ≅ StrictTower.towerDirectImage B s
  /-- This equation specifies the canonical open-to-direct map, rather than an arbitrary iso. -/
  clopen_unit : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
      [IsClosedImmersion s] (N : StrictTower.Towers B U),
    (scalarTowerOpenAdj B s).unit.app N ≫
        ((scalarTowerAdj B s).homEquiv _ _).symm ((clopen s).hom.app N) = 𝟙 N
  /-- The clopen projection is the direct-image unit followed by inverse open-to-direct. -/
  pi : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s],
    𝟭 (StrictTower.Towers B X) ⟶ StrictTower.towerPullback B s ⋙ StrictTower.towerJ B s
  /-- The intrinsic projector word. -/
  pi_eq : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
      [IsClosedImmersion s] (M : StrictTower.Towers B X),
    (pi s).app M = (scalarTowerAdj B s).unit.app M ≫
      (clopen s).inv.app ((StrictTower.towerPullback B s).obj M)
  /-- Preservation of the actual ordinary clopen projector. -/
  pi_comparison : ∀ {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s]
      [IsClosedImmersion s] (M : Modules R φ X),
    (rho X).map ((modulePi R φ s).app M) ≫
        (a s).hom.app ((pull R φ s).obj M) ≫
        (StrictTower.towerJ B s).map ((b s).hom.app M) = (pi s).app ((rho X).obj M)
  /-- The constant ordinary alpha, specified by its full clopen word below. -/
  alpha : ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T)
    (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k]
    [QuasiCompact i] [IsProper r] [IsProper p] (_h : k ≫ p = r ≫ i),
    StrictTower.towerJ B i ⋙ StrictTower.towerPullback B p ⟶
      StrictTower.towerPullback B r ⋙ StrictTower.towerJ B k
  /-- Alpha is beta, then the clopen projector, then the canonical compositors. -/
  alpha_eq : ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T)
    (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k]
    [QuasiCompact i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (M : StrictTower.Towers B S),
    (alpha k r p i h).app M =
      (beta (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm
        (IsPullback.of_hasPullback p i).flip).hom.app M ≫
      (StrictTower.towerJ B (pullback.fst p i)).map
        ((pi (StrictTower.squareLift k r p i h)).app
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (scalarTowerOpenComp B (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom.app
        ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).obj
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (eqToIso (scalarTowerOpen_congr B (pullback.lift_fst k r h))).hom.app
        ((StrictTower.towerPullback B (StrictTower.squareLift k r p i h)).obj
          ((StrictTower.towerPullback B (pullback.snd p i)).obj M)) ≫
      (StrictTower.towerJ B k).map
        ((StrictTower.towerGComp B (StrictTower.squareLift k r p i h)
          (pullback.snd p i)).inv.app M ≫
          (eqToIso (congrArg (StrictTower.towerPullback B) (pullback.lift_snd k r h))).hom.app M)
  /-- Preservation of the intrinsic ordinary alpha for every proper/open square. -/
  alpha_comparison : ∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (M : Modules R φ S),
    (rho W).map ((moduleAlpha R φ k r p i h).app M) ≫
        (a k).hom.app ((pull R φ r).obj M) ≫
        (StrictTower.towerJ B k).map ((b r).hom.app M) =
      (b p).hom.app ((extension R φ i).obj M) ≫
        (StrictTower.towerPullback B p).map ((a i).hom.app M) ≫
        (alpha k r p i h).app ((rho S).obj M)

end AlgebraicGeometry.ProEtale.VaryingRing
