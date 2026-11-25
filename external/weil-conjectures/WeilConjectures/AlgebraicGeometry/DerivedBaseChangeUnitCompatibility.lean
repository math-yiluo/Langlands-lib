/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
import WeilConjectures.AlgebraicGeometry.HomotopyBaseChangeCounit

/-! # Derived and ordinary exchange on the right-derived unit

Source: Stacks Project, Tag 08HY, mate description and derived adjunction compatibility.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section

/-- Termwise ordinary exchange, with the composition identifications on homotopy categories.
Source: Stacks Project, Tag 08HY.
(blueprint: lem-pc-derived-base-change-unit-compatibility). -/
def moduleHomotopyBaseChange
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive] :
    (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      (Scheme.Modules.tensorPullback p).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.pushforward f').mapHomotopyCategory (ComplexShape.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g))
    (ComplexShape.up ℤ)).hom ≫
  NatTrans.mapHomotopyCategory
    { app := Scheme.Modules.moduleBaseChangeMap f f' g p h
      naturality := fun _ _ a ↦
        Scheme.Modules.moduleBaseChangeMap_naturality f f' g p h a }
    (ComplexShape.up ℤ) ≫
  (Functor.mapHomotopyCategoryCompIso (Iso.refl
    (Scheme.Modules.tensorPullback p ⋙ Scheme.Modules.pushforward f'))
    (ComplexShape.up ℤ)).inv

private theorem exchange_unit_of_counit
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
    [Category* D₀] [Category* D₁] [Category* D₂] [Category* D₃]
    (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂) (Q₃ : C₃ ⥤ D₃)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (P : C₀ ⥤ C₃) (F' : C₃ ⥤ C₂)
    (H : C₁ ⥤ C₀) (H' : C₂ ⥤ C₃)
    (L : D₁ ⥤ D₀) (L' : D₂ ⥤ D₃) (LG : D₁ ⥤ D₂) (LP : D₀ ⥤ D₃)
    (R : D₀ ⥤ D₁) (R' : D₃ ⥤ D₂)
    (af : H ⊣ F) (af' : H' ⊣ F') (ad : L ⊣ R) (ad' : L' ⊣ R')
    (β : F ⋙ Q₁ ⟶ Q₀ ⋙ R) (β' : F' ⋙ Q₂ ⟶ Q₃ ⋙ R')
    (ε : Q₁ ⋙ L ⟶ H ⋙ Q₀) (ε' : Q₂ ⋙ L' ⟶ H' ⋙ Q₃)
    (εg : Q₁ ⋙ LG ⟶ G ⋙ Q₂) (εp : Q₀ ⋙ LP ⟶ P ⋙ Q₃)
    (t : LG ⋙ L' ⟶ L ⋙ LP) (s : G ⋙ H' ⟶ H ⋙ P) (b : F ⋙ G ⟶ P ⋙ F')
    (hpin : ∀ M K (a : H.obj M ⟶ K),
      ad.homEquiv _ _ (ε.app M ≫ Q₀.map a) =
        Q₁.map (af.homEquiv _ _ a) ≫ β.app K)
    (hpin' : ∀ M K (a : H'.obj M ⟶ K),
      ad'.homEquiv _ _ (ε'.app M ≫ Q₃.map a) =
        Q₂.map (af'.homEquiv _ _ a) ≫ β'.app K)
    (hsquare : ∀ M K (a : H.obj M ⟶ K),
      t.app (Q₁.obj M) ≫ LP.map (ε.app M ≫ Q₀.map a) ≫ εp.app K =
        L'.map (εg.app M) ≫ ε'.app (G.obj M) ≫
          Q₃.map (s.app M ≫ P.map a))
    (hordinary : ∀ K,
      s.app (F.obj K) ≫ P.map (af.counit.app K) =
        (af'.homEquiv _ _).symm (b.app K)) (K : C₀) :
    LG.map (β.app K) ≫
        ad'.homEquiv _ _ (t.app (R.obj (Q₀.obj K)) ≫ LP.map (ad.counit.app (Q₀.obj K))) ≫
        R'.map (εp.app K) =
      εg.app (F.obj K) ≫ Q₂.map (b.app K) ≫ β'.app (P.obj K) := by
  dsimp only [Functor.comp_obj, Functor.id_obj] at *
  have hc := hpin (F.obj K) K (af.counit.app K)
  have hid : af.homEquiv (F.obj K) K (af.counit.app K) = 𝟙 (F.obj K) := by
    rw [← af.homEquiv_symm_id]
    exact (af.homEquiv _ K).apply_symm_apply _
  rw [hid, CategoryTheory.Functor.map_id, Category.id_comp] at hc
  have hcounit : L.map (β.app K) ≫ ad.counit.app (Q₀.obj K) =
      ε.app (F.obj K) ≫ Q₀.map (af.counit.app K) :=
    (ad.homEquiv _ _).symm_apply_eq.mpr hc.symm
  have hs := hsquare (F.obj K) K (af.counit.app K)
  rw [hordinary] at hs
  have ht :
      L'.map (LG.map (β.app K)) ≫ t.app (R.obj (Q₀.obj K)) ≫
        LP.map (ad.counit.app (Q₀.obj K)) ≫ εp.app K =
      L'.map (εg.app (F.obj K)) ≫
        (ε'.app (G.obj (F.obj K)) ≫ Q₃.map ((af'.homEquiv _ _).symm (b.app K))) := by
    have hn := t.naturality (β.app K)
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hcounit]
    simpa only [Category.assoc] using hs
  have hp := hpin' (G.obj (F.obj K)) (P.obj K)
    ((af'.homEquiv _ _).symm (b.app K))
  rw [Equiv.apply_symm_apply] at hp
  rw [← Category.assoc, ← ad'.homEquiv_naturality_left, ← ad'.homEquiv_naturality_right]
  simp only [Category.assoc]
  rw [ht]
  rw [ad'.homEquiv_naturality_left]
  dsimp only [Functor.comp_obj] at ⊢
  rw [hp]

/-- The pinned derived mate agrees with ordinary exchange before resolving the input.
There is no acyclicity, flatness, affine-base or cover hypothesis.
Source: Stacks Project, Tag 08HY, transposition of the mate; the derived adjunction
compatibility of Tag 09T5.
(blueprint: lem-pc-derived-base-change-unit-compatibility).

Proof: Transpose both composites under the pinned derived adjunction for f'.
The defining compatibility of that adjunction identifies a counit followed by
localization of an ordinary map with its ordinary adjoint followed by the
right-derived unit. Apply this first to p and then to f. The defining universal
property of the pinned composition comparisons replaces the successive left-derived
counits by the counit for the composite pullback. The commutativity of the square
identifies the composites. Naturality of the right-derived units moves these units
past the ordinary exchange, and the two adjunction triangle identities cancel the
remaining units and counits. The resulting ordinary adjoint is the pushforward of
the p-pullback unit followed by pushforward composition, precisely the definition
of moduleBaseChangeMap. Descend termwise to the homotopy categories and localize;
injectivity of the pinned Hom equivalence gives the equation. -/
theorem derivedBaseChange_unit_compatibility
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g)
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback p).Additive]
    (D : HomotopyCategory X.Modules (ComplexShape.up ℤ)) :
    (derivedPullback g).map
        ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app D) ≫
      schemeDerivedBaseChangeMap f f' g p h (DerivedCategory.Qh.obj D) ≫
      (schemeDerivedDirectImage f').map
        (((Classical.choose (Classical.choose_spec
          exists_derivedPullbackComposition.{u, w})) p).app D) =
    ((Classical.choose (Classical.choose_spec
        exists_derivedPullbackComposition.{u, w})) g).app
        (((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj D) ≫
      DerivedCategory.Qh.map ((moduleHomotopyBaseChange f f' g p h).app D) ≫
      (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (ComplexShape.up ℤ)).obj D)
    := by
  classical
  rename_i d _ _
  let ε := @Classical.choose _ _ (Classical.choose_spec
    exists_derivedPullbackComposition.{u, w})
  let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
  let a : ∀ {A B : Scheme.{u}} (k : A ⟶ B),
      derivedPullback.{u, w} k ⊣ schemeDerivedDirectImage.{u, w, w} k :=
    fun {A B : Scheme.{u}} (k : A ⟶ B) ↦
    Classical.choose (exists_schemeDerivedAdjunction k
      (hAdd := (Classical.choose exists_derivedPullbackComposition) k)
      (ε k) ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) k))
  have := (Classical.choose exists_derivedPullbackComposition.{u, w}) f
  have := (Classical.choose exists_derivedPullbackComposition.{u, w}) f'
  let af := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
    |>.mapHomotopyCategory (.up ℤ)
  let af' := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f'))
    |>.mapHomotopyCategory (.up ℤ)
  let F := (Scheme.Modules.pushforward f).mapHomotopyCategory (.up ℤ)
  let G := (Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)
  let P := (Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)
  let : HasDerivedCategory.{w} X.Modules := d X
  let : HasDerivedCategory.{w} S.Modules := d S
  let : HasDerivedCategory.{w} X'.Modules := d X'
  let : HasDerivedCategory.{w} S'.Modules := d S'
  let β : F ⋙ DerivedCategory.Qh.{w} ⟶
      DerivedCategory.Qh.{w} ⋙ schemeDerivedDirectImage.{u, w, w} f :=
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit
  let β' : (Scheme.Modules.pushforward f').mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh.{w} ⟶ DerivedCategory.Qh.{w} ⋙ schemeDerivedDirectImage.{u, w, w} f' :=
    (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit
  let t : derivedPullback.{u, w} g ⋙ derivedPullback.{u, w} f' ⟶
      derivedPullback.{u, w} f ⋙ derivedPullback.{u, w} p :=
    { app := fun E ↦ (c f' g).hom.app E ≫
        eqToHom (congrArg (fun k : X' ⟶ S ↦ (derivedPullback.{u, w} k).obj E) h.symm) ≫
        (c p f).inv.app E
      naturality := fun E E' z ↦ by
        have hn := ((c f' g).hom ≫
          eqToHom (congrArg (fun k : X' ⟶ S ↦ derivedPullback.{u, w} k) h.symm) ≫
          (c p f).inv).naturality z
        simpa only [NatTrans.comp_app, eqToHom_app] using hn }
  have square := homotopyPullbackSquare_localization.{u, w} f f' g p h
  have ordinary := moduleHomotopyBaseChange_counit f f' g p h
  have pin := fun {A B : Scheme.{u}} (k : A ⟶ B) ↦
    Classical.choose_spec (exists_schemeDerivedAdjunction k
      (hAdd := (Classical.choose exists_derivedPullbackComposition) k)
      (ε k) ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) k))
  set_option backward.isDefEq.respectTransparency true in
  have result := exchange_unit_of_counit
    (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings S.toRingedSpace)))
    (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace)))
    (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings X'.toRingedSpace)))
    F G P ((Scheme.Modules.pushforward f').mapHomotopyCategory (.up ℤ))
    ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ))
    ((Scheme.Modules.tensorPullback f').mapHomotopyCategory (.up ℤ))
    (derivedPullback.{u, w} f) (derivedPullback.{u, w} f')
    (derivedPullback.{u, w} g) (derivedPullback.{u, w} p)
    (schemeDerivedDirectImage.{u, w, w} f) (schemeDerivedDirectImage.{u, w, w} f')
    af af' (a f) (a f') β β' (ε f) (ε f') (ε g) (ε p) t
    (moduleHomotopyPullbackSquare f f' g p h) (moduleHomotopyBaseChange f f' g p h)
    (pin f) (pin f')
    (fun M K z ↦ by
      simpa only [t, NatTrans.comp_app, eqToHom_app, Category.assoc] using square M K z)
    ordinary D
  change (derivedPullback g).map (β.app D) ≫
      (a f').homEquiv _ _
        ((c f' g).hom.app ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj D)) ≫
          eqToHom (congrArg (fun k : X' ⟶ S ↦
            (derivedPullback k).obj ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj D)))
            h.symm) ≫
          (c p f).inv.app ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj D)) ≫
          (derivedPullback p).map ((a f).counit.app (DerivedCategory.Qh.obj D))) ≫
      (schemeDerivedDirectImage f').map ((ε p).app D) =
    (ε g).app (F.obj D) ≫ DerivedCategory.Qh.map ((moduleHomotopyBaseChange f f' g p h).app D) ≫
      β'.app (P.obj D)
  simp only [P, t, Category.assoc, Functor.id_obj, Functor.comp_obj] at result ⊢
  exact result

end
end AlgebraicGeometry
