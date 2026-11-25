/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.StrictTowerOperations

/-! # Canonical operations on strict module towers

Source: blueprint completed-exchange-coherence, first two proof sentences;
Stacks 07A7 and 0D6D (blueprint: def-weil-pbc-strict-tower-operations).

## Main definitions

* `exchangeTowerPull`, `exchangeTowerPush`: strict diagram derived functors.
* `exchangeTowerAdjunction`: the derived termwise normalized module adjunction.
* `StrictTowerRingedSquare.exchangeTowerSquare`: canonical pullback composition.
* `StrictTowerRingedSquare.exchangeTowerMate`: its specified adjunction mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Coefficient sheaves and their compatible inverse-image identifications on a square.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
structure StrictTowerRingedSquare
    {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) where
  RY : Sheaf (ProEt.topology Y) CommRingCat.{t + 1}
  RX : Sheaf (ProEt.topology X) CommRingCat.{t + 1}
  RY' : Sheaf (ProEt.topology Y') CommRingCat.{t + 1}
  RX' : Sheaf (ProEt.topology X') CommRingCat.{t + 1}
  cf : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj RY ≅ RX
  cg : (proEtaleSheafInverseImage g CommRingCat.{t + 1}).obj RY ≅ RY'
  cg' : (proEtaleSheafInverseImage g' CommRingCat.{t + 1}).obj RX ≅ RX'
  cf' : (proEtaleSheafInverseImage f' CommRingCat.{t + 1}).obj RY' ≅ RX'
  coherent : HEq (proEtaleRingCompositeCoefficients g' f RY RX RX' cf cg')
    (proEtaleRingCompositeCoefficients f' g RY RY' RX' cg cf')

/-- Strict towers over an arbitrary coefficient sheaf on the original small site.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
abbrev exchangeTowers (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  ℕᵒᵖ ⥤ proEtaleRingModules T R

/-- Standard localization of strict towers, with the actual two site universes retained.
Source: strict normalization, paragraph 2
(blueprint: def-weil-pbc-strict-tower-operations). -/
instance exchangeTowers_hasDerived (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :
    HasDerivedCategory (exchangeTowers T R) := HasDerivedCategory.standard _

variable {U V : Scheme.{t}} (f : U ⟶ V)
  (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
  (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)

/-- Termwise inverse image of strict module towers with identified coefficients.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
abbrev exchangeTowerModulePull : exchangeTowers V R ⥤ exchangeTowers U S :=
  (Functor.whiskeringRight _ _ _).obj (proEtaleRingModulePullback f R S c)

/-- Termwise direct image, including all transition maps.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
abbrev exchangeTowerModulePush : exchangeTowers U S ⥤ exchangeTowers V R :=
  (Functor.whiskeringRight _ _ _).obj (proEtaleRingModuleDirectImage f R S c)

/-- Exactness of termwise inverse image on the whole strict diagram category.
Source: strict normalization, proof step 1; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations).
Proof: kernels and cokernels in the functor category are pointwise. The ordinary
identified-coefficient module inverse image preserves both, since its coefficient
map is an isomorphism. Evaluation at every index proves both preservation claims. -/
theorem exchangeTowerModulePull_exact :
    PreservesFiniteLimits (exchangeTowerModulePull f R S c) ∧
      PreservesFiniteColimits (exchangeTowerModulePull f R S c) := by
  constructor
  · exact ⟨fun _ _ _ ↦ inferInstance⟩
  · exact ⟨fun _ _ _ ↦ inferInstance⟩

/-- Left exactness on strict towers. Source: strict normalization, proof step 1
(blueprint: def-weil-pbc-strict-tower-operations). -/
instance exchangeTowerModulePull_finiteLimits :
    PreservesFiniteLimits (exchangeTowerModulePull f R S c) :=
  (exchangeTowerModulePull_exact f R S c).1

/-- Right exactness on strict towers. Source: strict normalization, proof step 1
(blueprint: def-weil-pbc-strict-tower-operations). -/
instance exchangeTowerModulePull_finiteColimits :
    PreservesFiniteColimits (exchangeTowerModulePull f R S c) :=
  (exchangeTowerModulePull_exact f R S c).2

/-- Exact termwise inverse image descends to the localization of strict towers.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
abbrev exchangeTowerPull : DerivedCategory (exchangeTowers V R) ⥤
    DerivedCategory (exchangeTowers U S) :=
  (exchangeTowerModulePull f R S c).mapDerivedCategory

/-- Total right derived termwise direct image, using K-injective strict towers.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
abbrev exchangeTowerPush : DerivedCategory (exchangeTowers U S) ⥤
    DerivedCategory (exchangeTowers V R) :=
  (exchangeTowerModulePush f R S c).rightDerivedFunctor

/-- The ordinary adjunction on strict towers is the termwise normalized module adjunction.
Source: strict normalization, proof step 1; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
def exchangeTowerModuleAdjunction :
    exchangeTowerModulePull f R S c ⊣ exchangeTowerModulePush f R S c :=
  (proEtaleRingModuleAdjunction f R S c).whiskerRight ℕᵒᵖ

/-- The derived adjunction uses precisely the termwise normalized module adjunction.
Source: strict normalization, proof step 1; Stacks 0DVC
(blueprint: def-weil-pbc-strict-tower-operations). -/
def exchangeTowerAdjunction :
    exchangeTowerPull f R S c ⊣ exchangeTowerPush f R S c :=
  (exchangeTowerModuleAdjunction f R S c).mapDerivedCategoryRightDerivedAdjunction

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

/-- The two coefficient paths agree over the equality of composite scheme maps.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations).
Proof: the commutative scheme square identifies f' followed by g with g' followed
by f. The coefficient coherence field, in the reverse direction, identifies the
isomorphism components over that equality. Dependent-pair extensionality gives
the displayed equality, so transport does not choose any additional ring map. -/
theorem StrictTowerRingedSquare.exchangeCoefficients_eq (r : StrictTowerRingedSquare sq) :
    (⟨f' ≫ g, proEtaleRingCompositeCoefficients f' g r.RY r.RY' r.RX' r.cg r.cf'⟩ :
      Σ q : X' ⟶ Y,
        (proEtaleSheafInverseImage q CommRingCat.{t + 1}).obj r.RY ≅ r.RX') =
      ⟨g' ≫ f, proEtaleRingCompositeCoefficients g' f r.RY r.RX r.RX' r.cf r.cg'⟩ := by
  exact Sigma.ext sq.w.symm r.coherent.symm

/-- The canonical module pullback comparison around the chosen ringed square.
Source: strict normalization, paragraph 2; Stacks 07A7, 0D6D
(blueprint: def-weil-pbc-strict-tower-operations). -/
def StrictTowerRingedSquare.exchangeModuleSquare (r : StrictTowerRingedSquare sq) :
    proEtaleRingModulePullback g r.RY r.RY' r.cg ⋙
        proEtaleRingModulePullback f' r.RY' r.RX' r.cf' ≅
      proEtaleRingModulePullback f r.RY r.RX r.cf ⋙
        proEtaleRingModulePullback g' r.RX r.RX' r.cg' := by
  let a := (exchangeModuleComposition f' g r.RY r.RY' r.RX' r.cg r.cf').symm
  let b := exchangeModuleComposition g' f r.RY r.RX r.RX' r.cf r.cg'
  let F := fun z : (Σ q : X' ⟶ Y,
      (proEtaleSheafInverseImage q CommRingCat.{t + 1}).obj r.RY ≅ r.RX') ↦
    proEtaleRingModulePullback z.1 r.RY r.RX' z.2
  have hfun := congrArg F r.exchangeCoefficients_eq
  let a' :
      proEtaleRingModulePullback g r.RY r.RY' r.cg ⋙
          proEtaleRingModulePullback f' r.RY' r.RX' r.cf' ≅
        proEtaleRingModulePullback (g' ≫ f) r.RY r.RX'
          (proEtaleRingCompositeCoefficients g' f r.RY r.RX r.RX' r.cf r.cg') :=
    a ≪≫ eqToIso hfun
  exact a' ≪≫ b

/-- The strict square is obtained by termwise application before localization.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
def StrictTowerRingedSquare.exchangeTowerSquare (r : StrictTowerRingedSquare sq) :
    exchangeTowerPull g r.RY r.RY' r.cg ⋙ exchangeTowerPull f' r.RY' r.RX' r.cf' ≅
      exchangeTowerPull f r.RY r.RX r.cf ⋙ exchangeTowerPull g' r.RX r.RX' r.cg' :=
  (Functor.mapDerivedCategoryCompIso
    (exchangeTowerModulePull g r.RY r.RY' r.cg)
    (exchangeTowerModulePull f' r.RY' r.RX' r.cf')) ≪≫
  Functor.mapDerivedCategoryNatIso
    (F := exchangeTowerModulePull g r.RY r.RY' r.cg ⋙
      exchangeTowerModulePull f' r.RY' r.RX' r.cf')
    (G := exchangeTowerModulePull f r.RY r.RX r.cf ⋙
      exchangeTowerModulePull g' r.RX r.RX' r.cg')
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso r.exchangeModuleSquare) ≪≫
  (Functor.mapDerivedCategoryCompIso
    (exchangeTowerModulePull f r.RY r.RX r.cf)
    (exchangeTowerModulePull g' r.RX r.RX' r.cg')).symm

/-- The canonical mate in the derived category of strict towers.
Source: strict normalization, paragraph 2; Stacks 07A7
(blueprint: def-weil-pbc-strict-tower-operations). -/
def StrictTowerRingedSquare.exchangeTowerMate (r : StrictTowerRingedSquare sq) :
    exchangeTowerPush f r.RY r.RX r.cf ⋙ exchangeTowerPull g r.RY r.RY' r.cg ⟶
      exchangeTowerPull g' r.RX r.RX' r.cg' ⋙ exchangeTowerPush f' r.RY' r.RX' r.cf' :=
  mateEquiv (exchangeTowerAdjunction f r.RY r.RX r.cf)
    (exchangeTowerAdjunction f' r.RY' r.RX' r.cf') r.exchangeTowerSquare.hom

end AlgebraicGeometry.Scheme
