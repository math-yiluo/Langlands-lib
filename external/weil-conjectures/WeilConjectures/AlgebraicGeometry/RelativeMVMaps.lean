/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-! # Canonical maps of the relative Mayer--Vietoris sequence

Source: Stacks Project, Cohomology, Tags 08HY and 08HZ.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace AlgebraicGeometry

variable [d : ∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The adjunction pinned to the recorded derived counits and units.
Source: Stacks, Tag 079W (blueprint: def-pc-relative-mv-maps). -/
def relativeMVAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPullback f ⊣ schemeDerivedDirectImage f :=
  Classical.choose (@exists_schemeDerivedAdjunction.{u, w} X Y f (d X) (d Y)
    ((Classical.choose (@exists_derivedPullbackComposition.{u, w} d)) f)
    ((Classical.choose (Classical.choose_spec (@exists_derivedPullbackComposition.{u, w} d))) f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec (@exists_derivedPullbackComposition.{u, w} d)))) f))

/-- The canonical pullback composition comparison.
Source: Stacks, Tag 08HY (blueprint: def-pc-relative-mv-maps). -/
def relativeMVComp {X Y Z : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Z) :
    derivedPullback f ⋙ derivedPullback j ≅ derivedPullback (j ≫ f) :=
  (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (@exists_derivedPullbackComposition.{u, w} d))))) j f

/-- The right-adjoint mate of the canonical pullback composition comparison.
Source: Stacks, Tags 08HY and 0D5T (blueprint: def-pc-relative-mv-maps). -/
def relativeMVImageComp {X Y Z : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Z) :
    schemeDerivedDirectImage j ⋙ schemeDerivedDirectImage f ≅
      schemeDerivedDirectImage (j ≫ f) :=
  (((relativeMVAdj f).comp (relativeMVAdj j)).ofNatIsoLeft
    (relativeMVComp j f)).rightAdjointUniq (relativeMVAdj (j ≫ f))

/-- The relative restriction unit for an open immersion (defined for any morphism).
Source: Stacks, Tag 08HZ (blueprint: def-pc-relative-mv-maps). -/
def relativeMVUnit {A X S : Scheme.{u}} (j : A ⟶ X) (f : X ⟶ S)
    (K : schemeDerivedCategory X) :
    (schemeDerivedDirectImage f).obj K ⟶
      (schemeDerivedDirectImage (j ≫ f)).obj ((derivedPullback j).obj K) :=
  (schemeDerivedDirectImage f).map ((relativeMVAdj j).unit.app K) ≫
    (relativeMVImageComp j f).hom.app ((derivedPullback j).obj K)

/-- Restriction of a relative open term along a factorization of its open immersion.
It is the adjoint of the restricted counit, using the canonical pullback comparisons.
Source: Stacks, Tags 08BV and 08HZ (blueprint: def-pc-relative-mv-maps). -/
def relativeMVRestriction {B A X S : Scheme.{u}} (k : B ⟶ A) (j : A ⟶ X)
    (l : B ⟶ X) (h : k ≫ j = l) (f : X ⟶ S) (K : schemeDerivedCategory X) :
    (schemeDerivedDirectImage (j ≫ f)).obj ((derivedPullback j).obj K) ⟶
      (schemeDerivedDirectImage (l ≫ f)).obj ((derivedPullback l).obj K) := by
  let c := relativeMVComp k j ≪≫ eqToIso (congrArg (fun t : B ⟶ X ↦ derivedPullback t) h)
  let b := ((relativeMVAdj l).homEquiv _ _)
    (c.inv.app ((schemeDerivedDirectImage j).obj ((derivedPullback j).obj K)) ≫
      (derivedPullback k).map ((relativeMVAdj j).counit.app ((derivedPullback j).obj K)) ≫
      c.hom.app K)
  exact (relativeMVImageComp j f).inv.app ((derivedPullback j).obj K) ≫
    (schemeDerivedDirectImage f).map b ≫
    (relativeMVImageComp l f).hom.app ((derivedPullback l).obj K)

/-- The first relative Mayer--Vietoris map after applying a functor.
Source: Stacks, Tag 08HZ (blueprint: def-pc-relative-mv-maps). -/
def relativeMVFirst {A B X S T : Scheme.{u}} (jU : A ⟶ X) (jV : B ⟶ X)
    (f : X ⟶ S) (F : schemeDerivedCategory S ⥤ schemeDerivedCategory T)
    (K : schemeDerivedCategory X) :=
  biprod.lift (F.map (relativeMVUnit jU f K)) (F.map (relativeMVUnit jV f K))

/-- The second relative Mayer--Vietoris map, with its usual difference sign.
Source: Stacks, Tags 08BV and 08HZ (blueprint: def-pc-relative-mv-maps). -/
def relativeMVSecond {A B D X S T : Scheme.{u}} (jU : A ⟶ X) (jV : B ⟶ X)
    (jW : D ⟶ X) (kU : D ⟶ A) (kV : D ⟶ B)
    (hU : kU ≫ jU = jW) (hV : kV ≫ jV = jW) (f : X ⟶ S)
    (F : schemeDerivedCategory S ⥤ schemeDerivedCategory T) (K : schemeDerivedCategory X) :=
  biprod.desc (F.map (relativeMVRestriction kU jU jW hU f K))
    (-(F.map (relativeMVRestriction kV jV jW hV f K)))

/-- The inclusion of the inverse-image opens, expressed on the chosen pullbacks.
Source: Stacks, Tag 08HY (blueprint: def-pc-relative-mv-maps). -/
def relativeMVOpenLift {X X' : Scheme.{u}} (g' : X' ⟶ X) {W U : X.Opens}
    (i : W ≤ U) : pullback g' W.ι ⟶ pullback g' U.ι :=
  pullback.lift (pullback.fst g' W.ι) (pullback.snd g' W.ι ≫ X.homOfLE i)
    (by rw [Category.assoc, Scheme.homOfLE_ι, pullback.condition])

/-- The first map on the pullback cover.
Source: Stacks, Tag 08HZ (blueprint: def-pc-relative-mv-maps). -/
def relativeMVTargetFirst {X X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (U V : X.Opens) (K' : schemeDerivedCategory X') :=
  relativeMVFirst (pullback.fst g' U.ι) (pullback.fst g' V.ι) f' (𝟭 _) K'

/-- The difference of restrictions on the pullback cover.
Source: Stacks, Tag 08HZ (blueprint: def-pc-relative-mv-maps). -/
def relativeMVTargetSecond {X X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (U V : X.Opens) (K' : schemeDerivedCategory X') :=
  relativeMVSecond (pullback.fst g' U.ι) (pullback.fst g' V.ι)
    (pullback.fst g' (U ⊓ V).ι) (relativeMVOpenLift g' inf_le_left)
    (relativeMVOpenLift g' inf_le_right) (pullback.lift_fst _ _ _)
    (pullback.lift_fst _ _ _) f' (𝟭 _) K'

/-- The first map after derived pullback of the relative triangle.
Source: Stacks, Tag 08HZ (blueprint: def-pc-relative-mv-maps). -/
def relativeMVSourceFirst {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (U V : X.Opens) (K : schemeDerivedCategory X) :=
  relativeMVFirst U.ι V.ι f (derivedPullback g) K

/-- The difference map after derived pullback of the relative triangle.
Source: Stacks, Tag 08HZ (blueprint: def-pc-relative-mv-maps). -/
def relativeMVSourceSecond {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (U V : X.Opens) (K : schemeDerivedCategory X) :=
  relativeMVSecond U.ι V.ι (U ⊓ V).ι (X.homOfLE inf_le_left)
    (X.homOfLE inf_le_right) (Scheme.homOfLE_ι X _) (Scheme.homOfLE_ι X _)
    f (derivedPullback g) K

/-- The canonical local comparison, including the specified restriction of the object map.
Source: Stacks, Tag 08HY (blueprint: def-pc-relative-mv-maps). -/
def relativeMVLocalArrow
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (W : X.Opens) : Arrow (schemeDerivedCategory S') :=
  Arrow.mk (schemeDerivedBaseChangeMap (W.ι ≫ f)
      (pullback.fst g' W.ι ≫ f') g (pullback.snd g' W.ι)
      (by rw [← pullback.condition_assoc, Category.assoc, hpull.w, ← Category.assoc])
      ((derivedPullback W.ι).obj K) ≫
      (schemeDerivedDirectImage (pullback.fst g' W.ι ≫ f')).map
        ((relativeMVComp (pullback.snd g' W.ι) W.ι).hom.app K ≫
        eqToHom (congrArg (fun k => (derivedPullback k).obj K)
          (pullback.condition (f := g') (g := W.ι)).symm) ≫
        (relativeMVComp (pullback.fst g' W.ι) g').inv.app K ≫
        (derivedPullback (pullback.fst g' W.ι)).map φ))

/-- The global base-change comparison followed by the given object map.
Source: Stacks, Tag 08HY (blueprint: def-pc-relative-mv-maps). -/
def relativeMVGlobalArrow
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') : Arrow (schemeDerivedCategory S') :=
  Arrow.mk (schemeDerivedBaseChangeMap f f' g g' hpull.w K ≫
    (schemeDerivedDirectImage f').map φ)

end AlgebraicGeometry
