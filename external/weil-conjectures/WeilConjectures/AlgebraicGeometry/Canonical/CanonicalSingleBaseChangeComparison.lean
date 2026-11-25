/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
import WeilConjectures.AlgebraicGeometry.HomotopySingleBaseChangeComparison

/-! # Derived exchange on a single module

Source: Stacks Project, Tag 08HY, the mate construction and its derived unit compatibility.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

private theorem comparison_naturality
    {C : Type*} [Category C] {A B D E F G H I : C}
    (a : A ⟶ B) (ε₁ : B ⟶ D) (ε₀ : A ⟶ E) (a' : E ⟶ D)
    (x : D ⟶ F) (v₁ : F ⟶ G) (b : G ⟶ H) (b' : F ⟶ I)
    (v₀ : I ⟶ H) (z : E ⟶ I)
    (ha : a ≫ ε₁ = ε₀ ≫ a') (hb : b' ≫ v₀ = v₁ ≫ b)
    (hz : a' ≫ x ≫ b' = z) :
    a ≫ ε₁ ≫ x ≫ v₁ ≫ b = ε₀ ≫ z ≫ v₀ := by
  rw [← hb, ← Category.assoc a, ha]
  simp only [Category.assoc]
  rw [← Category.assoc a' x, ← Category.assoc (a' ≫ x),
    Category.assoc a' x b', hz]

private theorem comparison_naturality_map
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {A B E U : D} {X Y Z T : C}
    (a : A ⟶ B) (ε₁ : B ⟶ Q.obj Y) (ε₀ : A ⟶ Q.obj X)
    (a' : X ⟶ Y) (x : Y ⟶ Z) (v₁ : Q.obj Z ⟶ E)
    (b : E ⟶ U) (b' : Z ⟶ T) (v₀ : Q.obj T ⟶ U)
    (z : X ⟶ T)
    (ha : a ≫ ε₁ = ε₀ ≫ Q.map a')
    (hb : Q.map b' ≫ v₀ = v₁ ≫ b) (hz : a' ≫ x ≫ b' = z) :
    a ≫ ε₁ ≫ Q.map x ≫ v₁ ≫ b = ε₀ ≫ Q.map z ≫ v₀ := by
  apply comparison_naturality a ε₁ ε₀ (Q.map a') (Q.map x) v₁ b
    (Q.map b') v₀ (Q.map z) ha hb
  simpa only [Functor.map_comp] using congrArg Q.map hz

private theorem comparison_whisker
    {C : Type*} [Category C] {A B D E F G H I : C}
    (a : A ⟶ B) (u : B ⟶ D) (β : D ⟶ E) (e : E ⟶ F) (b : F ⟶ G)
    (ε : B ⟶ H) (x : H ⟶ I) (v : I ⟶ F) (z : A ⟶ G)
    (hu : u ≫ β ≫ e = ε ≫ x ≫ v) (hz : a ≫ ε ≫ x ≫ v ≫ b = z) :
    a ≫ u ≫ β ≫ e ≫ b = z := by
  calc
    _ = a ≫ (u ≫ β ≫ e) ≫ b := by simp only [Category.assoc]
    _ = a ≫ (ε ≫ x ≫ v) ≫ b := by rw [hu]
    _ = z := by simpa only [Category.assoc] using hz

private theorem single_comparison_finish
    {A B C D E V : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category V]
    (L : A ⥤ D) (R : B ⥤ D) (Q : C ⥤ B) (P : E ⥤ D) (S : V ⥤ E)
    {A₀ A₁ A₂ : A} {B₀ : B} {C₀ C₁ C₂ : C}
    {E₀ E₁ : E} {V₀ V₁ V₂ : V}
    (a : A₀ ⟶ A₁) (u : A₁ ⟶ A₂) (β : L.obj A₂ ⟶ R.obj B₀)
    (e : B₀ ⟶ Q.obj C₀) (b₀ : C₀ ⟶ C₁) (b₁ : C₁ ⟶ C₂)
    (ε : L.obj A₀ ⟶ P.obj E₀) (c : E₀ ⟶ S.obj V₀)
    (t : V₀ ≅ V₁) (k : V₀ ⟶ V₂) (d : S.obj V₂ ⟶ E₁)
    (v : P.obj E₁ ⟶ R.obj (Q.obj C₂))
    (h : L.map a ≫ L.map u ≫ β ≫ R.map e ≫ R.map (Q.map (b₀ ≫ b₁)) =
      ε ≫ P.map (c ≫ S.map k ≫ d) ≫ v) :
    L.map (a ≫ u) ≫ β ≫ R.map (e ≫ Q.map b₀ ≫ Q.map b₁) =
      (ε ≫ P.map c ≫ P.map (S.map t.hom)) ≫
        P.map (S.map (t.inv ≫ k)) ≫ (P.map d ≫ v) := by
  have ht : P.map (S.map t.hom) ≫ P.map (S.map t.inv) = 𝟙 _ := by
    rw [← P.map_comp, ← S.map_comp, t.hom_inv_id, S.map_id, P.map_id]
  simp only [Functor.map_comp, Category.assoc] at h ⊢
  rw [← Category.assoc (P.map (S.map t.hom)), ht, Category.id_comp]
  exact h

-- Keep the pinned functors behind their interfaces while comparing the single maps.
/-- Derived exchange commutes with the two canonical single-module comparisons.
This identity concerns an arbitrary module and has no structure-sheaf unit maps.
Source: Stacks Project, Tag 08HY, the mate construction.
(blueprint: lem-sc-canonical-single-base-change-comparison).

Proof: Apply derivedBaseChange_unit_compatibility at the homotopy single of M.
Precompose with derived pullback of the localized inverse single-map comparison
for pushforward f. Postcompose with derived pushforward of the localized single-map
comparison for tensor pullback p, followed by the single of the adjunction-preserving
isomorphism from tensor pullback to ordinary pullback. Naturality of the selected
left-derived counit moves the first comparison to its source; naturality of the
right-derived unit moves the second comparison to its target. The single-map
comparisons intertwine the termwise ordinary exchange with the single of ordinary
exchange: evaluate in degree zero, where the comparison maps are the canonical
single-object identifications, and in every other degree the source is zero.
The comparison from tensor to ordinary g-pullback cancels its inverse. Localizing
this identity and reassociating gives the equation. All steps are naturality,
functoriality and isomorphism cancellation, so no flatness, acyclicity, cartesianness
or nonemptiness of schemes is required. -/
theorem canonicalSingleBaseChangeComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) (M : X.Modules) :
    (AlgebraicGeometry.derivedPullback.{u, w} g).map (canonicalSingleDirectImageMap.{u, w} f M) ≫
      schemeDerivedBaseChangeMap f f' g p h
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) ≫
      (schemeDerivedDirectImage.{u, w, w} f').map (canonicalSinglePullbackMap.{u, w} p M) =
    canonicalSinglePullbackMap g ((pushforward f).obj M) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
        (((Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
          (pullbackPushforwardAdjunction g)).inv.app ((pushforward f).obj M) ≫
          moduleBaseChangeMap f f' g p h M ≫
          (pushforward f').map
            (((Classical.choose (exists_tensorPullbackAdjunction p)).leftAdjointUniq
              (pullbackPushforwardAdjunction p)).hom.app M)) ≫
      canonicalSingleDirectImageMap f' ((pullback p).obj M) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let C_X := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let C_S := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let C_X' := SheafOfModules.{u} (moduleRings X'.toRingedSpace)
  let C_S' := SheafOfModules.{u} (moduleRings S'.toRingedSpace)
  let := canonicalTensorPullbackAdditive g
  let := canonicalTensorPullbackAdditive p
  let E := (HomotopyCategory.singleFunctor C_X 0).obj M
  let Q_S := DerivedCategory.Qh.{w} (C := C_S)
  let Q_X' := DerivedCategory.Qh.{w} (C := C_X')
  let Q_S' := DerivedCategory.Qh.{w} (C := C_S')
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let G : C_S ⥤
      C_S' := tensorPullback g
  let H : C_X ⥤
      C_X' := tensorPullback p
  let I := RingedSpace.moduleDirectImage f'.toLRSHom.toShHom
  have : G.Additive := canonicalTensorPullbackAdditive g
  have : H.Additive := canonicalTensorPullbackAdditive p
  have : F.Additive := RingedSpace.moduleDirectImage_additive f.toLRSHom.toShHom
  have : I.Additive := RingedSpace.moduleDirectImage_additive f'.toLRSHom.toShHom
  let ε_g := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{u, w})) g
  let t_p := (Classical.choose (exists_tensorPullbackAdjunction p)).leftAdjointUniq
    (pullbackPushforwardAdjunction p)
  let a := (HomotopyCategory.quotient C_S (.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M)
  let b := (HomotopyCategory.quotient C_X' (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app M) ≫
    (HomotopyCategory.singleFunctor C_X' 0).map (t_p.hom.app M)
  let c := (HomotopyCategory.quotient C_S' (.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M))
  let d := (HomotopyCategory.quotient C_S' (.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0).inv.app
      ((pullback p).obj M))
  let k := moduleBaseChangeMap f f' g p h M ≫ I.map (t_p.hom.app M)
  have hm := homotopySingleBaseChangeComparison f f' g p h M
  have hu := derivedBaseChange_unit_compatibility f f' g p h E
  have hn := ε_g.naturality a
  let v : I.mapHomotopyCategory (.up ℤ) ⋙ Q_S' ⟶
      Q_X' ⋙ schemeDerivedDirectImage.{u, w, w} f' := I.rightDerivedFunctorUnit
  have hr := v.naturality b
  change (AlgebraicGeometry.derivedPullback.{u, w} g).map (Q_S.map a) ≫
      ε_g.app ((F.mapHomotopyCategory (.up ℤ)).obj E) =
    ε_g.app ((HomotopyCategory.singleFunctor C_S 0).obj (F.obj M)) ≫
      Q_S'.map ((G.mapHomotopyCategory (.up ℤ)).map a) at hn
  change Q_S'.map ((I.mapHomotopyCategory (.up ℤ)).map b) ≫
      (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.singleFunctor C_X' 0).obj ((pullback p).obj M)) =
    (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
      ((H.mapHomotopyCategory (.up ℤ)).obj E) ≫
      (schemeDerivedDirectImage.{u, w, w} f').map (Q_X'.map b) at hr
  have hz := comparison_naturality_map Q_S'
    ((AlgebraicGeometry.derivedPullback.{u, w} g).map (Q_S.map a))
    (ε_g.app ((F.mapHomotopyCategory (.up ℤ)).obj E))
    (ε_g.app ((HomotopyCategory.singleFunctor C_S 0).obj (F.obj M)))
    ((G.mapHomotopyCategory (.up ℤ)).map a)
    ((moduleHomotopyBaseChange f f' g p h).app E)
    (v.app ((H.mapHomotopyCategory (.up ℤ)).obj E))
    ((schemeDerivedDirectImage.{u, w, w} f').map (Q_X'.map b))
    ((I.mapHomotopyCategory (.up ℤ)).map b)
    (v.app ((HomotopyCategory.singleFunctor C_X' 0).obj ((pullback p).obj M)))
    (c ≫ (HomotopyCategory.singleFunctor C_S' 0).map k ≫ d) hn hr hm
  let ε_p := (Classical.choose (Classical.choose_spec
    exists_derivedPullbackComposition.{u, w})) p
  have hh := comparison_whisker
    ((AlgebraicGeometry.derivedPullback.{u, w} g).map (Q_S.map a))
    ((AlgebraicGeometry.derivedPullback.{u, w} g).map (F.rightDerivedFunctorUnit.app E))
    (schemeDerivedBaseChangeMap.{u, w} f f' g p h (DerivedCategory.Qh.obj E))
    ((schemeDerivedDirectImage.{u, w, w} f').map (ε_p.app E))
    ((schemeDerivedDirectImage.{u, w, w} f').map (Q_X'.map b))
    (ε_g.app ((F.mapHomotopyCategory (.up ℤ)).obj E))
    (Q_S'.map ((moduleHomotopyBaseChange f f' g p h).app E))
    (v.app ((H.mapHomotopyCategory (.up ℤ)).obj E))
    (ε_g.app ((HomotopyCategory.singleFunctor C_S 0).obj (F.obj M)) ≫
      Q_S'.map (c ≫ (HomotopyCategory.singleFunctor C_S' 0).map k ≫ d) ≫
      v.app ((HomotopyCategory.singleFunctor C_X' 0).obj ((pullback p).obj M))) hu hz
  let t_g := (Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (pullbackPushforwardAdjunction g)
  let sf := HomotopyCategory.singleFunctor C_S' 0
  let b₀ := (HomotopyCategory.quotient C_X' (.up ℤ)).map
    ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app M)
  let b₁ := (HomotopyCategory.singleFunctor C_X' 0).map (t_p.hom.app M)
  have hf := single_comparison_finish
    (A := DerivedCategory C_S) (B := DerivedCategory C_X')
    (C := HomotopyCategory C_X' (.up ℤ)) (D := DerivedCategory C_S')
    (E := HomotopyCategory C_S' (.up ℤ)) (V := C_S')
    (AlgebraicGeometry.derivedPullback.{u, w} g) (schemeDerivedDirectImage.{u, w, w} f')
    Q_X' Q_S' sf (Q_S.map a) (F.rightDerivedFunctorUnit.app E)
    (schemeDerivedBaseChangeMap.{u, w} f f' g p h (DerivedCategory.Qh.obj E))
    (ε_p.app E) b₀ b₁
    (ε_g.app ((HomotopyCategory.singleFunctor C_S 0).obj (F.obj M)))
    c (t_g.app (F.obj M)) k d
    (v.app ((HomotopyCategory.singleFunctor C_X' 0).obj ((pullback p).obj M))) hh
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  with_unfolding_all
    simpa only [canonicalSingleDirectImageMap, canonicalSinglePullbackMap, cast_eq,
      Category.assoc] using! hf

end AlgebraicGeometry.Scheme.Modules
