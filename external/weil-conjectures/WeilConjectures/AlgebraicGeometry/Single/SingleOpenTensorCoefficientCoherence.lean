/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.Picard.Termwise.PicardTermwiseSingleMapComposition
import all WeilConjectures.AlgebraicGeometry.Picard.Termwise.PicardTermwiseSingleMapComposition
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionAssociativity
import WeilConjectures.AlgebraicGeometry.PerfectHomCochainCounit

/-! # Single-module coefficients in an open square

## References

* Stacks Project, Tags 06YJ, 0D5S and 01JR
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option cleanup.letToHave false
set_option maxRecDepth 2048

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackCompositionIso Scheme.Modules.tensorPullbackObj
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] Scheme.Modules.Hom DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh HomotopyCategory.singleFunctors

private theorem cancel_single_maps
    {C D : Type*} [Category C] [Category D] (S : C ⥤ D)
    {X Y : D} {M N : C} (f : X ⟶ Y) (g : Y ⟶ S.obj M) (a : M ≅ N) :
    (f ≫ g ≫ S.map a.hom) ≫ S.map a.inv = f ≫ g := by
  simp only [Category.assoc, ← S.map_comp, a.hom_inv_id, S.map_id, Category.comp_id]

private theorem map_iso_cancel {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z : C} (a : X ⟶ Z) (s : Y ≅ Z) :
    F.map (a ≫ s.inv) ≫ F.map s.hom = F.map a := by
  rw [← F.map_comp, Category.assoc, s.inv_hom_id, Category.comp_id]

private theorem naturality_two {D : Type*} [Category D]
    {A₀ A₁ A₂ B₀ B₁ B₂ : D}
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂)
    (a₀ : A₀ ⟶ A₁) (a₁ : A₁ ⟶ A₂) (b₀ : B₀ ⟶ B₁) (b₁ : B₁ ⟶ B₂)
    (p : A₀ ⟶ A₂) (q : B₀ ⟶ B₂)
    (h₀ : f₀ ≫ b₀ = a₀ ≫ f₁) (h₁ : f₁ ≫ b₁ = a₁ ≫ f₂)
    (hp : p = a₀ ≫ a₁) (hq : q = b₀ ≫ b₁) :
    f₀ ≫ q = p ≫ f₂ := by
  rw [hp, hq, ← Category.assoc, h₀, Category.assoc, h₁, Category.assoc]

private theorem invert_square {Cat : Type*} [Category Cat] {A B C D : Cat}
    (x : A ≅ B) (y : B ≅ C) (z : A ≅ D) (w : D ≅ C)
    (h : x.hom ≫ y.hom = z.hom ≫ w.hom) :
    w.hom ≫ y.inv ≫ x.inv = z.inv := by
  apply (cancel_epi z.hom).mp
  calc
    _ = (z.hom ≫ w.hom) ≫ y.inv ≫ x.inv := by simp only [Category.assoc]
    _ = (x.hom ≫ y.hom) ≫ y.inv ≫ x.inv :=
      congrArg (fun a ↦ a ≫ y.inv ≫ x.inv) h.symm
    _ = _ := by simp only [Category.assoc, y.hom_inv_id_assoc, x.hom_inv_id,
      z.hom_inv_id]

private theorem normalized_square_algebra
    {C : Type*} [Category C]
    {A B D R K F U V E₀ E₁ E₂ E₃ E₄ E₅ E₆ E₇ : C}
    (a : A ⟶ B) (p : B ⟶ D) (d : R ≅ D) (b : R ⟶ K) (ρ : K ⟶ F)
    (r : D ⟶ E₀) (u : E₀ ⟶ F) (s : E₀ ≅ E₁)
    (a' : B ⟶ E₂) (q : E₂ ⟶ E₁) (t : A ⟶ E₃)
    (l : E₃ ⟶ E₂) (q' : E₃ ⟶ E₄) (l' : E₄ ⟶ E₁)
    (c : A ⟶ U) (e : U ⟶ E₅) (g : E₅ ⟶ E₄)
    (d' : V ≅ U) (b' : V ⟶ E₆) (r' : E₆ ⟶ E₇)
    (f : E₅ ⟶ E₇) (β : E₆ ⟶ K) (v : E₇ ⟶ F)
    (hd : d.hom ≫ r ≫ u = b ≫ ρ)
    (hs : p ≫ r ≫ s.hom = a' ≫ q)
    (ha : a ≫ a' = t ≫ l) (hn : l ≫ q = q' ≫ l')
    (hc : c ≫ e ≫ g = t ≫ q')
    (hd' : d'.hom ≫ e ≫ f = b' ≫ r')
    (hβ : β ≫ ρ = r' ≫ v)
    (hg : g ≫ l' ≫ s.inv ≫ u = f ≫ v) [Mono ρ] :
    a ≫ p ≫ d.inv ≫ b = c ≫ d'.inv ≫ b' ≫ β := by
  apply (cancel_mono ρ).mp
  have hd₀ : d.inv ≫ b ≫ ρ = r ≫ u := by
    rw [← hd, d.inv_hom_id_assoc]
  have hs₀ : p ≫ r = a' ≫ q ≫ s.inv := by
    apply (cancel_mono s.hom).mp
    simpa only [Category.assoc, s.inv_hom_id, Category.comp_id] using hs
  have hd'₀ : d'.inv ≫ b' ≫ r' = e ≫ f := by
    rw [← hd', d'.inv_hom_id_assoc]
  simp only [Category.assoc]
  rw [hd₀]
  calc
    a ≫ p ≫ r ≫ u = a ≫ (p ≫ r) ≫ u := by simp only [Category.assoc]
    _ = a ≫ (a' ≫ q ≫ s.inv) ≫ u := congrArg (fun z ↦ a ≫ z ≫ u) hs₀
    _ = (a ≫ a') ≫ q ≫ s.inv ≫ u := by simp only [Category.assoc]
    _ = (t ≫ l) ≫ q ≫ s.inv ≫ u :=
      congrArg (fun z ↦ z ≫ q ≫ s.inv ≫ u) ha
    _ = t ≫ (l ≫ q) ≫ s.inv ≫ u := by simp only [Category.assoc]
    _ = t ≫ (q' ≫ l') ≫ s.inv ≫ u :=
      congrArg (fun z ↦ t ≫ z ≫ s.inv ≫ u) hn
    _ = (t ≫ q') ≫ l' ≫ s.inv ≫ u := by simp only [Category.assoc]
    _ = (c ≫ e ≫ g) ≫ l' ≫ s.inv ≫ u :=
      congrArg (fun z ↦ z ≫ l' ≫ s.inv ≫ u) hc.symm
    _ = c ≫ e ≫ (g ≫ l' ≫ s.inv ≫ u) := by simp only [Category.assoc]
    _ = c ≫ e ≫ (f ≫ v) := congrArg (fun z ↦ c ≫ e ≫ z) hg
    _ = c ≫ (e ≫ f) ≫ v := by simp only [Category.assoc]
    _ = c ≫ (d'.inv ≫ b' ≫ r') ≫ v :=
      congrArg (fun z ↦ c ≫ z ≫ v) hd'₀.symm
    _ = c ≫ d'.inv ≫ b' ≫ (r' ≫ v) := by simp only [Category.assoc]
    _ = c ≫ d'.inv ≫ b' ≫ (β ≫ ρ) :=
      congrArg (fun z ↦ c ≫ d'.inv ≫ b' ≫ z) hβ.symm
    _ = _ := by rfl

private theorem single_map_eq {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {M N : C} (a : M ⟶ N) :
    DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map a) =
      (DerivedCategory.singleFunctor C 0).map a := by
  have h := (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality a
  simpa only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app,
    Functor.comp_map, Category.id_comp, Category.comp_id] using h.symm

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

private theorem tensor_single_normalize {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) :
    let := Scheme.Modules.canonicalTensorPullbackAdditive f
    Scheme.picardTermwiseSingleMap f M =
      (perfectHomTensorCounit f).app
        ((HomotopyCategory.singleFunctor _ 0).obj M) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.tensorPullback f) (.up ℤ) 0).hom.app M)) := by
  exact Scheme.single_map_normalize f M

private theorem tensor_single_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) :
    let := Scheme.Modules.canonicalTensorPullbackAdditive f
    Scheme.picardTermwiseSingleMap f M =
      (Scheme.picardTermwiseCounit f).app ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ≫
      DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback f) (.up ℤ) 0).hom.app M) := by
  let := Scheme.Modules.canonicalTensorPullbackAdditive f
  have hnorm (A : schemeDerivedCategory Y) (B : HomotopyCategory X.Modules (.up ℤ))
      (a : (derivedPullback f).obj A ⟶ DerivedCategory.Qh.obj B) :
      (derivedPullback f).map (𝟙 A) ≫ a ≫ DerivedCategory.Qh.map (𝟙 B) ≫
        𝟙 (DerivedCategory.Qh.obj B) = a := by
    simp
  rw [tensor_single_normalize]
  simp only [Scheme.picardTermwiseCounit, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv]
  exact congrArg (fun a ↦ a ≫ DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.tensorPullback f) (.up ℤ) 0).hom.app M)) (hnorm _ _ _).symm

attribute [local irreducible] Scheme.picardTermwiseSingleMap Scheme.picardTermwiseCounit
  Scheme.Modules.canonicalSinglePullbackMap

-- The selected derived counit has a large dependent type.
private theorem tensor_single_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (a : M ⟶ N) :
    (derivedPullback f).map ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map a) ≫
        Scheme.picardTermwiseSingleMap f N =
      Scheme.picardTermwiseSingleMap f M ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
            ((Scheme.Modules.tensorPullback f).map a) := by
  let := Scheme.Modules.canonicalTensorPullbackAdditive f
  let ε := perfectHomTensorCounit f
  let H := HomotopyCategory.quotient X.Modules (.up ℤ)
  let s := HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.tensorPullback f) (.up ℤ) 0
  let HY := HomotopyCategory.singleFunctor Y.Modules 0
  let SY := DerivedCategory.singleFunctor Y.Modules 0
  let SX := DerivedCategory.singleFunctor X.Modules 0
  let T := (Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)
  have hε := ε.naturality (HY.map a)
  change (derivedPullback f).map (SY.map a) ≫ ε.app (HY.obj N) =
    ε.app (HY.obj M) ≫ DerivedCategory.Qh.map (T.map (HY.map a)) at hε
  have hs := congrArg (fun b ↦ DerivedCategory.Qh.map (H.map b)) (s.hom.naturality a)
  simp only [Functor.map_comp, Functor.comp_map] at hs
  change DerivedCategory.Qh.map (T.map (HY.map a)) ≫
      DerivedCategory.Qh.map (H.map (s.hom.app N)) =
    DerivedCategory.Qh.map (H.map (s.hom.app M)) ≫
      SX.map ((Scheme.Modules.tensorPullback f).map a) at hs
  exact naturality_two
    ((derivedPullback f).map (SY.map a)) (DerivedCategory.Qh.map (T.map (HY.map a)))
    (SX.map ((Scheme.Modules.tensorPullback f).map a))
    (ε.app (HY.obj M)) (DerivedCategory.Qh.map (H.map (s.hom.app M)))
    (ε.app (HY.obj N)) (DerivedCategory.Qh.map (H.map (s.hom.app N)))
    (Scheme.picardTermwiseSingleMap f M) (Scheme.picardTermwiseSingleMap f N)
    hε hs (tensor_single_normalize f M) (tensor_single_normalize f N)

private theorem tensor_single_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : X ⟶ Z) (h : f ≫ g = a) (M : Z.Modules) :
    (relativeMVComp f g).hom.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj M) ≫
        eqToHom (congrArg (fun b ↦ (derivedPullback b).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj M)) h) ≫
        Scheme.picardTermwiseSingleMap a M ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
            ((Scheme.Modules.tensorPullbackCompositionIso f g a h).hom.app M) =
      (derivedPullback f).map (Scheme.picardTermwiseSingleMap g M) ≫
        Scheme.picardTermwiseSingleMap f ((Scheme.Modules.tensorPullback g).obj M) := by
  let := Scheme.Modules.canonicalTensorPullbackAdditive f
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
  let Q := DerivedCategory.Q
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let s := (HomologicalComplex.singleMapHomologicalComplex
    (W₁ := SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (W₂ := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (Scheme.Modules.tensorPullback f) (.up ℤ) 0).app
      ((Scheme.Modules.tensorPullback g).obj M)
  let u := (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).mapIso
      ((Scheme.Modules.tensorPullbackCompositionIso f g a h).app M) ≪≫ s.symm
  have hu : Q.map u.hom ≫ Q.map s.hom =
      S.map ((Scheme.Modules.tensorPullbackCompositionIso f g a h).hom.app M) := by
    have hh := map_iso_cancel Q
      ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
          ((Scheme.Modules.tensorPullbackCompositionIso f g a h).hom.app M)) s
    have hh' : Q.map u.hom ≫ Q.map s.hom = Q.map
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map
            ((Scheme.Modules.tensorPullbackCompositionIso f g a h).hom.app M)) := by
      simpa only [u, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom] using hh
    exact hh'.trans (single_map_eq _)
  have hc := Scheme.picardTermwiseSingleMap_composition f g a h M
  dsimp only at hc
  change ((relativeMVComp f g) ≪≫ eqToIso
      (congrArg (fun b ↦ derivedPullback b) h)).hom.app
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj M) ≫
      Scheme.picardTermwiseSingleMap a M ≫ Q.map u.hom =
    (derivedPullback f).map (Scheme.picardTermwiseSingleMap g M) ≫
      (Scheme.picardTermwiseCounit f).app
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          ((Scheme.Modules.tensorPullback g).obj M)) at hc
  have hh := congrArg (fun b ↦ b ≫ Q.map s.hom) hc
  simp only [Category.assoc] at hh
  rw [hu] at hh
  have hf := tensor_single_counit f ((Scheme.Modules.tensorPullback g).obj M)
  change Scheme.picardTermwiseSingleMap f ((Scheme.Modules.tensorPullback g).obj M) =
    (Scheme.picardTermwiseCounit f).app
      ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback g).obj M)) ≫ Q.map s.hom at hf
  rw [← hf] at hh
  simpa only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    S, Q, Category.assoc] using hh

end

/-- Normalized single-module coefficient comparisons commute with an open square.
This is an equality of coefficient maps, before any direct image or base-change mate. -/
theorem single_open_tensor_coefficient_coherence
    {W Z X' P J J' : Scheme.{u}}
    (z : Z ⟶ W) (q : X' ⟶ W) (t : P ⟶ Z)
    (i : J ⟶ W) (r : J' ⟶ X') (k : J' ⟶ J)
    (e : J ≅ Z) (e' : J' ≅ P)
    (hi : e.hom ≫ z = i) (ht : k ≫ e.hom = e'.hom ≫ t)
    (hsq : k ≫ i = r ≫ q) (N : W.Modules) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let K := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings W.toRingedSpace)) 0).obj N
    let M := Scheme.Modules.tensorPullbackObj z N
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj M
    let E' := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0).obj
        (Scheme.Modules.tensorPullbackObj t M)
    let K' := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
        (Scheme.Modules.tensorPullbackObj q N)
    let phi0 := (relativeMVComp k i).hom.app K ≫
      eqToHom (congrArg (fun a ↦ (derivedPullback a).obj K) hsq) ≫
      (relativeMVComp r q).inv.app K ≫
      (derivedPullback r).map (Scheme.picardTermwiseSingleMap q N)
    let aN := (Scheme.Modules.tensorPullbackCompositionIso e.hom z i hi).symm.app N
    let heq : (e'.hom ≫ t) ≫ z = r ≫ q := by
      rw [← ht, Category.assoc, hi, hsq]
    let bN := (Scheme.Modules.tensorPullbackCompositionIso
        e'.hom t (e'.hom ≫ t) rfl).symm.app M ≪≫
      (Scheme.Modules.tensorPullbackCompositionIso
        (e'.hom ≫ t) z (r ≫ q) heq).symm.app N ≪≫
      (Scheme.Modules.tensorPullbackCompositionIso r q (r ≫ q) rfl).app N
    IsIso (Scheme.picardTermwiseSingleMap r (Scheme.Modules.tensorPullbackObj q N)) →
    ∀ (alpha : (derivedPullback e.hom).obj E ⟶ (derivedPullback i).obj K)
      (beta : (derivedPullback e'.hom).obj E' ⟶ (derivedPullback r).obj K'),
      alpha ≫ Scheme.picardTermwiseSingleMap i N =
        Scheme.picardTermwiseSingleMap e.hom M ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings J.toRingedSpace)) 0).map aN.hom →
      beta ≫ Scheme.picardTermwiseSingleMap r (Scheme.Modules.tensorPullbackObj q N) =
        Scheme.picardTermwiseSingleMap e'.hom (Scheme.Modules.tensorPullbackObj t M) ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings J'.toRingedSpace)) 0).map bN.hom →
      (derivedPullback k).map alpha ≫ phi0 =
        (relativeMVComp k e.hom).hom.app E ≫
        eqToHom (congrArg (fun a ↦ (derivedPullback a).obj E) ht) ≫
        (relativeMVComp e'.hom t).inv.app E ≫
        (derivedPullback e'.hom).map (Scheme.picardTermwiseSingleMap t M) ≫
        beta := by
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  dsimp only
  intro hIso alpha beta ha hb
  let : IsIso (Scheme.picardTermwiseSingleMap r
      ((Scheme.Modules.tensorPullback q).obj N)) := hIso
  let S (X : Scheme.{u}) := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
  let M := (Scheme.Modules.tensorPullback z).obj N
  let aN := (Scheme.Modules.tensorPullbackCompositionIso e.hom z i hi).symm.app N
  have heq : (e'.hom ≫ t) ≫ z = r ≫ q := by
    rw [← ht, Category.assoc, hi, hsq]
  let bN := (Scheme.Modules.tensorPullbackCompositionIso
      e'.hom t (e'.hom ≫ t) rfl).symm.app M ≪≫
    (Scheme.Modules.tensorPullbackCompositionIso
      (e'.hom ≫ t) z (r ≫ q) heq).symm.app N ≪≫
    (Scheme.Modules.tensorPullbackCompositionIso r q (r ≫ q) rfl).app N
  have hki := tensor_single_composition k i (r ≫ q) hsq N
  have hrq := tensor_single_composition r q (r ≫ q) rfl N
  have hke := tensor_single_composition k e.hom (e'.hom ≫ t) ht M
  have het := tensor_single_composition e'.hom t (e'.hom ≫ t) rfl M
  have hn := tensor_single_naturality k aN.hom
  have hα := congrArg (fun a ↦ (derivedPullback k).map a) ha
  simp only [Functor.map_comp] at hα
  have hassoc := Scheme.Modules.tensorPullbackCompositionIso_associativity
    z e.hom k (e'.hom ≫ t) (r ≫ q) i ht hi heq hsq N
  let x := (Scheme.Modules.tensorPullbackCompositionIso k i (r ≫ q) hsq).app N
  let y := (Scheme.Modules.tensorPullback k).mapIso
    ((Scheme.Modules.tensorPullbackCompositionIso e.hom z i hi).app N)
  let v := (Scheme.Modules.tensorPullbackCompositionIso
    (e'.hom ≫ t) z (r ≫ q) heq).app N
  let w := (Scheme.Modules.tensorPullbackCompositionIso
    k e.hom (e'.hom ≫ t) ht).app M
  have hassoc' : x.hom ≫ y.hom = v.hom ≫ w.hom := hassoc
  have hinv := invert_square x y v w hassoc'
  have hcoef : w.hom ≫ (Scheme.Modules.tensorPullback k).map aN.hom ≫
      x.inv ≫ (Scheme.Modules.tensorPullbackCompositionIso r q (r ≫ q) rfl).hom.app N =
    (Scheme.Modules.tensorPullbackCompositionIso
      e'.hom t (e'.hom ≫ t) rfl).hom.app M ≫ bN.hom := by
    have hh := congrArg (fun a ↦ a ≫
      (Scheme.Modules.tensorPullbackCompositionIso r q (r ≫ q) rfl).hom.app N) hinv
    simpa only [y, aN, Functor.mapIso_inv, Iso.app_inv, Iso.symm_hom,
      bN, v, M, Functor.comp_obj, Iso.trans_hom, Iso.app_hom, Category.assoc,
      Iso.hom_inv_id_app_assoc] using hh
  have hcoefS := congrArg (fun a ↦ (S J').map a) hcoef
  simp only [Functor.map_comp] at hcoefS
  have hrq' : (relativeMVComp r q).hom.app ((S W).obj N) ≫
      Scheme.picardTermwiseSingleMap (r ≫ q) N ≫
      (S J').map ((Scheme.Modules.tensorPullbackCompositionIso
        r q (r ≫ q) rfl).hom.app N) =
    (derivedPullback r).map (Scheme.picardTermwiseSingleMap q N) ≫
      Scheme.picardTermwiseSingleMap r ((Scheme.Modules.tensorPullback q).obj N) := by
    simpa only [eqToHom_refl, Category.id_comp] using hrq
  have het' : (relativeMVComp e'.hom t).hom.app ((S Z).obj M) ≫
      Scheme.picardTermwiseSingleMap (e'.hom ≫ t) M ≫
      (S J').map ((Scheme.Modules.tensorPullbackCompositionIso
        e'.hom t (e'.hom ≫ t) rfl).hom.app M) =
    (derivedPullback e'.hom).map (Scheme.picardTermwiseSingleMap t M) ≫
      Scheme.picardTermwiseSingleMap e'.hom ((Scheme.Modules.tensorPullback t).obj M) := by
    simpa only [eqToHom_refl, Category.id_comp] using het
  let s := (S J').mapIso x
  have h := normalized_square_algebra
    ((derivedPullback k).map alpha)
    ((relativeMVComp k i).hom.app ((S W).obj N) ≫
      eqToHom (congrArg (fun a ↦ (derivedPullback a).obj ((S W).obj N)) hsq))
    ((relativeMVComp r q).app ((S W).obj N))
    ((derivedPullback r).map (Scheme.picardTermwiseSingleMap q N))
    (Scheme.picardTermwiseSingleMap r ((Scheme.Modules.tensorPullback q).obj N))
    (Scheme.picardTermwiseSingleMap (r ≫ q) N)
    ((S J').map ((Scheme.Modules.tensorPullbackCompositionIso
      r q (r ≫ q) rfl).hom.app N)) s
    ((derivedPullback k).map (Scheme.picardTermwiseSingleMap i N))
    (Scheme.picardTermwiseSingleMap k ((Scheme.Modules.tensorPullback i).obj N))
    ((derivedPullback k).map (Scheme.picardTermwiseSingleMap e.hom M))
    ((derivedPullback k).map ((S J).map aN.hom))
    (Scheme.picardTermwiseSingleMap k ((Scheme.Modules.tensorPullback e.hom).obj M))
    ((S J').map ((Scheme.Modules.tensorPullback k).map aN.hom))
    ((relativeMVComp k e.hom).hom.app ((S Z).obj M) ≫
      eqToHom (congrArg (fun a ↦ (derivedPullback a).obj ((S Z).obj M)) ht))
    (Scheme.picardTermwiseSingleMap (e'.hom ≫ t) M)
    ((S J').map w.hom)
    ((relativeMVComp e'.hom t).app ((S Z).obj M))
    ((derivedPullback e'.hom).map (Scheme.picardTermwiseSingleMap t M))
    (Scheme.picardTermwiseSingleMap e'.hom ((Scheme.Modules.tensorPullback t).obj M))
    ((S J').map ((Scheme.Modules.tensorPullbackCompositionIso
      e'.hom t (e'.hom ≫ t) rfl).hom.app M)) beta ((S J').map bN.hom)
    hrq' (by simpa only [s, x, Functor.mapIso_hom, Iso.app_hom,
      Category.assoc] using hki) hα hn
    (by simpa only [w, Iso.app_hom, Category.assoc] using hke)
    het' hb (by simpa only [s, Functor.mapIso_inv, x, Iso.app_inv,
      Category.assoc] using hcoefS)
  simpa only [S, M, Scheme.Modules.tensorPullback, Iso.app_inv, Category.assoc] using h

end AlgebraicGeometry
