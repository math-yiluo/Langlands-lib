/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows

/-!
# The two factors of the clopen inverse-image arrow

Source: Stacks Project, Tag 0F7B, open case
(blueprint: def-sp-varying-ring-clopen-arrow-factors).
The cartesian open comparison and the subsequent clopen section projection are
kept separate, before taking proper-adjunction mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

/-- Exact localization of a transformation between two composites.
Source: Stacks 05RU (blueprint: def-sp-varying-ring-clopen-arrow-factors). -/
def localizedArrow
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (K : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (t : F ⋙ G ⟶ H ⋙ K) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ K.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F G).hom ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ)) _ _
      (F ⋙ G).mapDerivedCategory (H ⋙ K).mapDerivedCategory
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex t (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso H K).inv

private theorem localizedArrow_comp
    {A B C D E : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F₁ : A ⥤ B) (F₂ : B ⥤ E) (H₁ : A ⥤ C) (H₂ : C ⥤ E)
    (G₁ : A ⥤ D) (G₂ : D ⥤ E)
    [F₁.Additive] [F₂.Additive] [H₁.Additive] [H₂.Additive]
    [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits H₁] [PreservesFiniteColimits H₁]
    [PreservesFiniteLimits H₂] [PreservesFiniteColimits H₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (t : F₁ ⋙ F₂ ⟶ H₁ ⋙ H₂) (s : H₁ ⋙ H₂ ⟶ G₁ ⋙ G₂) :
    localizedArrow F₁ F₂ H₁ H₂ t ≫ localizedArrow H₁ H₂ G₁ G₂ s =
      localizedArrow F₁ F₂ G₁ G₂ (t ≫ s) := by
  unfold localizedArrow
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [NatTrans.mapHomologicalComplex_comp, Functor.whiskerRight_comp,
    Localization.comp_liftNatTrans_assoc]

/-- The exact cartesian open comparison, prior to the clopen projection.
Source: Stacks 09AE (blueprint: def-sp-varying-ring-clopen-arrow-factors). -/
def openBaseChange {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (hsq : IsPullback a j' j g) : J R φ j ⋙ G R φ g ⟶ G R φ a ⋙ J R φ j' :=
  localizedArrow (extension R φ j) (pull R φ g) (pull R φ a) (extension R φ j')
    (moduleBeta R φ a j' j g h hsq).hom

/-- The clopen section projection, with its outgoing open and pullback compositors.
Source: Stacks 0F7B (blueprint: def-sp-varying-ring-clopen-arrow-factors). -/
def moduleSectionArrow {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    pull R φ (pullback.snd p i) ⋙ extension R φ (pullback.fst p i) ⟶
      pull R φ r ⋙ extension R φ k :=
  Functor.whiskerRight (Functor.whiskerLeft (pull R φ (pullback.snd p i))
    (modulePi R φ (StrictTower.squareLift k r p i h))) (extension R φ (pullback.fst p i)) ≫
  Functor.whiskerRight
    (Functor.associator (pull R φ (pullback.snd p i)) (pull R φ (StrictTower.squareLift k r p i h))
      (extension R φ (StrictTower.squareLift k r p i h))).inv (extension R φ (pullback.fst p i)) ≫
  (Functor.associator (pull R φ (pullback.snd p i) ⋙ pull R φ (StrictTower.squareLift k r p i h))
    (extension R φ (StrictTower.squareLift k r p i h)) (extension R φ (pullback.fst p i))).hom ≫
  Functor.whiskerLeft (pull R φ (pullback.snd p i) ⋙ pull R φ (StrictTower.squareLift k r p i h))
    ((moduleJComp R φ (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
      (moduleJCongr R φ (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((moduleGComp R φ (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (pull R φ) (pullback.lift_snd k r h))).hom) (extension R φ k)

/-- Exact localization of the clopen section projection.
Source: Stacks 0F7B (blueprint: def-sp-varying-ring-clopen-arrow-factors). -/
def sectionArrow {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    G R φ (pullback.snd p i) ⋙ J R φ (pullback.fst p i) ⟶ G R φ r ⋙ J R φ k :=
  localizedArrow (pull R φ (pullback.snd p i)) (extension R φ (pullback.fst p i))
    (pull R φ r) (extension R φ k) (moduleSectionArrow R φ k r p i h)

/-- The same clopen section factor in the existing strict-tower calculus.
Source: Stacks 0F7B (blueprint: def-sp-varying-ring-clopen-arrow-factors). -/
def strictSectionArrow (B : Type (u + 1)) [CommRing B]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    StrictTower.G B (pullback.snd p i) ⋙ StrictTower.J B (pullback.fst p i) ⟶
      StrictTower.G B r ⋙ StrictTower.J B k := by
  letI := StrictTower.squareLift_open k r p i h
  letI := StrictTower.squareLift_closed k r p i h
  exact
    Functor.whiskerRight (Functor.whiskerLeft (StrictTower.G B (pullback.snd p i))
      (StrictTower.pi B (StrictTower.squareLift k r p i h))) (StrictTower.J B (pullback.fst p i)) ≫
    Functor.whiskerRight
      (Functor.associator (StrictTower.G B (pullback.snd p i))
        (StrictTower.G B (StrictTower.squareLift k r p i h))
        (StrictTower.J B (StrictTower.squareLift k r p i h))).inv
      (StrictTower.J B (pullback.fst p i)) ≫
    (Functor.associator
      (StrictTower.G B (pullback.snd p i) ⋙ StrictTower.G B (StrictTower.squareLift k r p i h))
      (StrictTower.J B (StrictTower.squareLift k r p i h))
      (StrictTower.J B (pullback.fst p i))).hom ≫
    Functor.whiskerLeft
      (StrictTower.G B (pullback.snd p i) ⋙ StrictTower.G B (StrictTower.squareLift k r p i h))
      ((StrictTower.jComp B (StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
        (StrictTower.jCongr B (pullback.lift_fst k r h)).hom) ≫
    Functor.whiskerRight
      ((StrictTower.gComp B (StrictTower.squareLift k r p i h) (pullback.snd p i)).inv ≫
        (eqToIso (congrArg (StrictTower.G B) (pullback.lift_snd k r h))).hom) (StrictTower.J B k)

/-- The varying-system arrow is the composite of its two separately localized factors.
Source: Stacks 0F7B (blueprint: def-sp-varying-ring-clopen-arrow-factors).
Proof: localization preserves composition; the original moduleAlpha is the open
base-change comparison followed by moduleSectionArrow, with the same associators. -/
theorem alpha_factorization {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    alpha R φ k r p i h =
      openBaseChange R φ (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip ≫
      sectionArrow R φ k r p i h := by
  rw [openBaseChange, sectionArrow, localizedArrow_comp]
  rfl

/-- The strict-tower arrow has the identical two-factor expression.
Source: Stacks 0F7B (blueprint: def-sp-varying-ring-clopen-arrow-factors).
Proof: expand the two definitions and associate their composites. -/
theorem strictAlpha_factorization (B : Type (u + 1)) [CommRing B]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    StrictTower.alpha B k r p i h =
      (StrictTower.beta B (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom ≫
      strictSectionArrow B k r p i h := rfl

end AlgebraicGeometry.ProEtale.VaryingRing
