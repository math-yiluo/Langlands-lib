/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPullback

/-! # Twisting for canonical tower classes

Source: blueprint main-20261015, chap-Smooth-purity,
`sk-prop-sp-tower-geometric-classes` (blueprint: def-sp-tower-class-twisting).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual ring object of the coefficient tower on the vertical sequence site.
Source: coefficient convention (blueprint: def-sp-tower-class-twisting). -/
abbrev systemRing (T : Scheme.{u}) :=
  SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)

/-- Tensor by the actual Tate line before localization.
Source: definition-tate-twists (blueprint: def-sp-tower-class-twisting). -/
def positive {T : Scheme.{u}} (c : Chern l E T) :
    Systems T (Arings l E T) ⥤ Systems T (Arings l E T) :=
  letI := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  letI := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  SheafOfModules.siteSheafTensorRight (A := systemRing l E T) (lineModule l E c)

/-- Pure tensors in that exact, ordinary line twist.
Source: definition-tate-twists (blueprint: def-sp-tower-class-twisting). -/
def pure {T : Scheme.{u}} (c : Chern l E T)
    (M : Systems T (Arings l E T)) (U : (ℕ × T.ProEt)ᵒᵖ)
    (x : M.val.obj U) (y : (lineModule l E c).val.obj U) :
    ((positive l E c).obj M).val.obj U :=
  letI := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  letI := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  SheafOfModules.siteSheafTensorTmul M (lineModule l E c) U x y

local instance coefficientSectionSMul {T : Scheme.{u}}
    (c : Chern l E T) (U : (ℕ × T.ProEt)ᵒᵖ) :
    SMul ((coefficient T (Arings l E T)).val.obj U) ((lineModule l E c).val.obj U) :=
  inferInstanceAs (SMul ((systemRing l E T).obj.obj U) ((lineModule l E c).val.obj U))

/-- Line twisting is the actual tensor/Hom equivalence. The coevaluation and
 evaluation are fixed on local sections, including their signs. Neither an arbitrary
 equivalence nor a second, independently chosen inverse line occurs.
Source: classes (4); definition-tate-twists negative powers
(blueprint: def-sp-tower-class-twisting). -/
structure Twisting {T : Scheme.{u}} (c : Chern l E T) where
  equivalence : Systems T (Arings l E T) ≌ Systems T (Arings l E T)
  forward : equivalence.functor = positive l E c
  backward : ∀ M : Systems T (Arings l E T),
    equivalence.inverse.obj M = SheafOfModules.homObj
      (R := SemilinearSections.systemRing.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
    (lineModule l E c) M
  backward_maps : ∀ {M N : Systems T (Arings l E T)} (f : M ⟶ N),
    HEq (equivalence.inverse.map f)
      (SheafOfModules.homObjMap (R := systemRing l E T) (𝟙 (lineModule l E c)) f)
  coevaluation : ∀ (M : Systems T (Arings l E T)) (U : (ℕ × T.ProEt)ᵒᵖ)
    (x : M.val.obj U)
    (z : (SheafOfModules.homObj (R := SemilinearSections.systemRing.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
    (lineModule l E c)
      (equivalence.functor.obj M)).val.obj U),
    HEq z ((equivalence.unitIso.app M).hom.val.app U x) →
    ∀ y : (lineModule l E c).val.obj U,
      HEq (z.app (op (Over.mk (𝟙 U.unop))) y) (pure l E c M U x y)
  evaluation : ∀ (M : Systems T (Arings l E T)) (U : (ℕ × T.ProEt)ᵒᵖ)
    (z : (equivalence.inverse.obj M).val.obj U)
    (z' : (SheafOfModules.homObj (R := SemilinearSections.systemRing.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
    (lineModule l E c) M).val.obj U)
    (y : (lineModule l E c).val.obj U)
    (v : (equivalence.functor.obj (equivalence.inverse.obj M)).val.obj U),
    HEq z z' → HEq v (pure l E c (equivalence.inverse.obj M) U z y) →
      (equivalence.counitIso.app M).hom.val.app U v =
        z'.app (op (Over.mk (𝟙 U.unop))) y
  [additive : equivalence.functor.Additive]
  [inverseAdditive : equivalence.inverse.Additive]
  [limits : PreservesFiniteLimits equivalence.functor]
  [colimits : PreservesFiniteColimits equivalence.functor]
  [inverseLimits : PreservesFiniteLimits equivalence.inverse]
  [inverseColimits : PreservesFiniteColimits equivalence.inverse]
  unitIso : equivalence.functor.obj (coefficient T (Arings l E T)) ≅ lineModule l E c
  unit_normalization : ∀ (U : (ℕ × T.ProEt)ᵒᵖ)
    (a : (coefficient T (Arings l E T)).val.obj U)
    (y : (lineModule l E c).val.obj U)
    (v : (equivalence.functor.obj (coefficient T (Arings l E T))).val.obj U),
    HEq v (pure l E c (coefficient T (Arings l E T)) U a y) →
      unitIso.hom.val.app U v = a • y

attribute [instance] Twisting.additive Twisting.inverseAdditive Twisting.limits
  Twisting.colimits Twisting.inverseLimits Twisting.inverseColimits

/-- Positive line twist in the ordinary unbounded derived category.
Source: classes (4) (blueprint: def-sp-tower-class-twisting). -/
abbrev Twisting.T {T : Scheme.{u}} {c : Chern l E T} (t : Twisting l E c) :=
  t.equivalence.functor.mapDerivedCategory

/-- Negative twist in the same ordinary localization.
Source: classes (4) (blueprint: def-sp-tower-class-twisting). -/
abbrev Twisting.N {T : Scheme.{u}} {c : Chern l E T} (t : Twisting l E c) :=
  t.equivalence.inverse.mapDerivedCategory

/-- The inverse line is the negative twist of the unit, identified termwise.
Source: classes (4) (blueprint: def-sp-tower-class-twisting). -/
def Twisting.inverseUnit {T : Scheme.{u}} {c : Chern l E T} (t : Twisting l E c) :
    (t.N l E).obj (unit T (Arings l E T)) ≅ inverseLine l E c :=
  (t.equivalence.inverse.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).mapIso
      (eqToIso (t.backward (coefficient T (Arings l E T))))

/-- The positive twist of the unit is the actual Tate line.
Source: classes (4) (blueprint: def-sp-tower-class-twisting). -/
def Twisting.positiveUnit {T : Scheme.{u}} {c : Chern l E T} (t : Twisting l E c) :
    (t.T l E).obj (unit T (Arings l E T)) ≅ line l E c :=
  (t.equivalence.functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).mapIso t.unitIso

/-- Evaluation contracts the inverse Tate line against the Tate line.
Source: classes (4) (blueprint: def-sp-tower-class-twisting). -/
def Twisting.contract {T : Scheme.{u}} {c : Chern l E T} (t : Twisting l E c) :
    (t.T l E).obj (inverseLine l E c) ≅ unit T (Arings l E T) :=
  (t.T l E).mapIso (t.inverseUnit l E).symm ≪≫
    (Functor.mapDerivedCategoryCompIso t.equivalence.inverse t.equivalence.functor).app
      (unit T (Arings l E T)) ≪≫
    (Functor.mapDerivedCategoryNatIso t.equivalence.counitIso).app
      (unit T (Arings l E T)) ≪≫
    (Functor.mapDerivedCategoryIdIso (Systems T (Arings l E T))).app
      (unit T (Arings l E T))

/-- Pullback of positive twisting is fixed before deriving: its adjoint sends a
local pure tensor to the tensor of the two ordinary adjunction units. The second
factor uses the normalized root/coefficient pullback, rather than a chosen scalar.
Source: classes (4), projection mate (blueprint: def-sp-tower-class-twisting). -/
structure PositivePullback {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : SpTowerShriek.Geometry l E b f)
    {cY : Chern l E Y} {cX : Chern l E X}
    (tY : Twisting l E cY) (tX : Twisting l E cX)
    (p : LinePullback l E f g cY cX) where
  iso : tY.equivalence.functor ⋙ g.pull ≅ g.pull ⋙ tX.equivalence.functor
  normalization : ∀ (M : Systems Y (Arings l E Y)) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop)))
    (y : (lineModule l E cY).val.obj (op (n, U.unop)))
    (v : ((SpTowerShriek.ev l E Y n).obj (tY.equivalence.functor.obj M)).val.obj U)
    (x' : (g.pull.obj M).val.obj (op (n, (chart f U).unop)))
    (y' : (lineModule l E cX).val.obj (op (n, (chart f U).unop))),
    HEq v (pure l E cY M (op (n, U.unop)) x y) →
    HEq x' (adjointSection l E g (𝟙 (g.pull.obj M)) n U x) →
    HEq y' (adjointSection l E g p.iso.hom n U y) →
    HEq (adjointSection l E g (iso.hom.app M) n U v)
      (pure l E cX (g.pull.obj M) (op (n, (chart f U).unop)) x' y')

/-- Termwise localization of the ordinary, section-normalized twist comparison.
Source: classes (4) (blueprint: def-sp-tower-class-twisting). -/
def PositivePullback.derivedIso {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    {f : X ⟶ Y} {g : SpTowerShriek.Geometry l E b f}
    {cY : Chern l E Y} {cX : Chern l E X}
    {tY : Twisting l E cY} {tX : Twisting l E cX}
    {p : LinePullback l E f g cY cX} (v : PositivePullback l E f g tY tX p) :
    tY.T l E ⋙ SpTowerShriek.pull l E b g ≅
      SpTowerShriek.pull l E b g ⋙ tX.T l E :=
  letI := tY.additive
  letI := tX.additive
  letI := g.pullAdditive
  letI := g.pullLimits
  letI := g.pullColimits
  Functor.mapDerivedCategoryCompIso tY.equivalence.functor g.pull ≪≫
    Functor.mapDerivedCategoryNatIso v.iso ≪≫
    (Functor.mapDerivedCategoryCompIso g.pull tX.equivalence.functor).symm

/-- The canonical projection map is the counit mate of the specified inverse-image
comparison. It is formed in the tower category, before any finite evaluation.
Source: classes (4), proof step 15 (blueprint: def-sp-tower-class-twisting). -/
def projection {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}}
    {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    {cY : Chern l E Y} {cX : Chern l E X}
    {tY : Twisting l E cY} {tX : Twisting l E cX}
    {p : LinePullback l E f g cY cX} (v : PositivePullback l E f g tY tX p)
    (M : D X (Arings l E X)) :
    (tY.T l E).obj ((SpTowerShriek.push l E b g).obj M) ⟶
      (SpTowerShriek.push l E b g).obj ((tX.T l E).obj M) :=
  (SpTowerShriek.adjunction l E b g).homEquiv _ _
    ((v.derivedIso l E).hom.app ((SpTowerShriek.push l E b g).obj M) ≫
      (tX.T l E).map ((SpTowerShriek.adjunction l E b g).counit.app M))

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
