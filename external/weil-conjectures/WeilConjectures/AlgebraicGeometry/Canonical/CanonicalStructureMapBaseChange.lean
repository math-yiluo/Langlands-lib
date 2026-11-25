/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSingleBaseChangeComparison
import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapAlgebra

/-! # Canonical structure maps and derived exchange

Source: Stacks Project, Tag 08HY, the mate description, and Tag 0096.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

-- Comparing the two sheaf adjunctions requires unfolding their common right adjoint.
private theorem tensor_structure_transport {A B : Scheme.{u}} (k : A ⟶ B) :
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction k)).hom.app
        (SheafOfModules.unit B.ringCatSheaf) ≫
      SheafOfModules.pullbackObjUnitToUnit k.toRingCatSheafHom =
    Scheme.Modules.tensorPullbackObjUnitToUnit k := by
  apply (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).homEquiv _ _
    |>.injective
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_apply]
  simp only [← Adjunction.homEquiv_apply,
    Scheme.Modules.tensorPullbackObjUnitToUnit,
    Equiv.apply_symm_apply]
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    k.toRingCatSheafHom

private theorem compose_three_squares
    {C : Type*} [Category C] {A₀ A₁ B₀ B₁ D₀ D₁ E₀ E₁ : C}
    (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (d : D₀ ⟶ D₁) (e : E₀ ⟶ E₁)
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (v₀ : B₀ ⟶ D₀) (v₁ : B₁ ⟶ D₁)
    (w₀ : D₀ ⟶ E₀) (w₁ : D₁ ⟶ E₁)
    (hu : a ≫ u₁ = u₀ ≫ b) (hv : b ≫ v₁ = v₀ ≫ d)
    (hw : d ≫ w₁ = w₀ ≫ e) :
    a ≫ (u₁ ≫ v₁ ≫ w₁) = (u₀ ≫ v₀ ≫ w₀) ≫ e := by
  calc
    _ = u₀ ≫ b ≫ v₁ ≫ w₁ := by
      rw [← Category.assoc a u₁, hu]
      simp only [Category.assoc]
    _ = u₀ ≫ v₀ ≫ d ≫ w₁ := by
      rw [← Category.assoc b v₁, hv]
      simp only [Category.assoc]
    _ = _ := by rw [hw]; simp only [Category.assoc]

private theorem mapped_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B E G : C} (a : A ⟶ B) (b : E ⟶ G) (u : A ⟶ E) (v : B ⟶ G)
    (h : a ≫ v = u ≫ b) : F.map a ≫ F.map v = F.map u ≫ F.map b := by
  simpa only [Functor.map_comp] using congrArg F.map h

private theorem compose_two_squares
    {C : Type*} [Category C] {A₀ A₁ B₀ B₁ D₀ D₁ : C}
    (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (d : D₀ ⟶ D₁)
    (u₀ : A₀ ⟶ B₀) (u₁ : A₁ ⟶ B₁) (v₀ : B₀ ⟶ D₀) (v₁ : B₁ ⟶ D₁)
    (hu : a ≫ u₁ = u₀ ≫ b) (hv : b ≫ v₁ = v₀ ≫ d) :
    a ≫ (u₁ ≫ v₁) = (u₀ ≫ v₀) ≫ d := by
  rw [← Category.assoc, hu, Category.assoc, hv, Category.assoc]

-- The naturality square involves localization of the sheaf single-complex comparisons.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem single_pullback_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : Scheme.{u}} (k : A ⟶ B) {M N : B.Modules} (a : M ⟶ N) :
    (derivedPullback k).map ((DerivedCategory.singleFunctor _ 0).map a) ≫
        Scheme.Modules.canonicalSinglePullbackMap k N =
      Scheme.Modules.canonicalSinglePullbackMap k M ≫
        (DerivedCategory.singleFunctor _ 0).map ((Scheme.Modules.pullback k).map a) := by
  let C_A := SheafOfModules.{u} (moduleRings A.toRingedSpace)
  let C_B := SheafOfModules.{u} (moduleRings B.toRingedSpace)
  let T : C_B ⥤ C_A := Scheme.Modules.tensorPullback k
  have : T.Additive := Scheme.Modules.canonicalTensorPullbackAdditive k
  let L := derivedPullback.{u, w} k
  let Q := HomotopyCategory.quotient C_A (.up ℤ) ⋙ DerivedCategory.Qh.{w}
  let ε : DerivedCategory.Qh ⋙ L ⟶
      T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  let c := (HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).hom
  let t := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction k)
  have hε := ε.naturality ((HomotopyCategory.singleFunctor C_B 0).map a)
  have hc := mapped_square Q _ _ _ _ (c.naturality a)
  have ht := mapped_square (DerivedCategory.singleFunctor C_A 0) _ _ _ _ (t.hom.naturality a)
  have hh := compose_three_squares _ _ _ _ _ _ _ _ _ _ hε hc ht
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  with_unfolding_all
    simpa only [Scheme.Modules.canonicalSinglePullbackMap, cast_eq, Category.assoc] using! hh

-- The right-derived unit is compared with localized single-complex morphisms.
private theorem single_directImage_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : Scheme.{u}} (k : A ⟶ B) {M N : A.Modules} (a : M ⟶ N) :
    Scheme.Modules.canonicalSingleDirectImageMap k M ≫
        (schemeDerivedDirectImage k).map ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings A.toRingedSpace)) 0).map a) =
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings B.toRingedSpace)) 0).map
          ((Scheme.Modules.pushforward k).map a) ≫
        Scheme.Modules.canonicalSingleDirectImageMap k N := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let C_A := SheafOfModules.{u} (moduleRings A.toRingedSpace)
  let C_B := SheafOfModules.{u} (moduleRings B.toRingedSpace)
  let F : C_A ⥤ C_B := RingedSpace.moduleDirectImage k.toLRSHom.toShHom
  let Q := HomotopyCategory.quotient C_B (.up ℤ) ⋙ DerivedCategory.Qh.{w}
  let β : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ schemeDerivedDirectImage k := F.rightDerivedFunctorUnit
  let c := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv
  have hc := mapped_square Q _ _ _ _ (c.naturality a)
  have hβ := β.naturality ((HomotopyCategory.singleFunctor C_A 0).map a)
  have hh := compose_two_squares _ _ _ _ _ _ _ hc hβ
  with_unfolding_all
    simpa only [Scheme.Modules.canonicalSingleDirectImageMap, cast_eq,
      Category.assoc] using! hh.symm

-- Paste the comparison squares around the ordinary structure-map identity.
private theorem structure_map_pasting
    {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {A₀ A₁ A₂ A₃ A₄ A₅ : D} {M₀ M₁ M₂ M₃ M₄ : C}
    (a : A₀ ⟶ A₁) (u : A₁ ⟶ A₂) (e : A₂ ⟶ A₃)
    (v : A₃ ⟶ A₄) (b : A₄ ⟶ A₅)
    (c₀ : A₀ ⟶ Q.obj M₀) (c₁ : A₁ ⟶ Q.obj M₁)
    (d₀ : Q.obj M₂ ⟶ A₄) (d₁ : Q.obj M₄ ⟶ A₅)
    (a' : M₀ ⟶ M₁) (e' : M₁ ⟶ M₂) (b' : M₂ ⟶ M₄)
    (s : M₀ ⟶ M₃) (t : M₃ ⟶ M₄)
    (he : u ≫ e ≫ v = c₁ ≫ Q.map e' ≫ d₀)
    (hb : d₀ ≫ b = Q.map b' ≫ d₁)
    (ha : a ≫ c₁ = c₀ ≫ Q.map a')
    (h : a' ≫ e' ≫ b' = s ≫ t) :
    a ≫ u ≫ e ≫ v ≫ b = (c₀ ≫ Q.map s) ≫ (Q.map t ≫ d₁) := by
  calc
    _ = a ≫ (u ≫ e ≫ v) ≫ b := by simp only [Category.assoc]
    _ = a ≫ (c₁ ≫ Q.map e' ≫ d₀) ≫ b := by rw [he]
    _ = (a ≫ c₁) ≫ Q.map e' ≫ (d₀ ≫ b) := by simp only [Category.assoc]
    _ = (c₀ ≫ Q.map a') ≫ Q.map e' ≫ (Q.map b' ≫ d₁) := by rw [ha, hb]
    _ = c₀ ≫ Q.map (a' ≫ e' ≫ b') ≫ d₁ := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by rw [h]; simp only [Functor.map_comp, Category.assoc]

/-- The canonical structure maps commute with the pinned derived exchange map.
No cartesianness, flatness, vanishing or invertibility assumption is needed.
Source: Stacks Project, Tag 08HY, mate description, and Tag 0096, pullback of modules.
(blueprint: lem-sc-canonical-structure-map-base-change).

Proof: Represent each structure map as the single of the ordinary structure map
followed by the canonical right-derived unit. Apply derivedBaseChange_unit_compatibility
at the homotopy single of O_X. Naturality of the single-complex pullback and pushforward
comparisons moves these comparisons through the ordinary exchange. The last clause of
moduleBaseChangeMap_algebra is the ordinary identity:
tensorPullback g applied to f sharp, followed by ordinary exchange and pushforward
of tensorPullbackObjUnitToUnit p, equals tensorPullbackObjUnitToUnit g followed by
f' sharp. It follows by transposition from p f = f' g, using the adjunction triangles.
Localize the single of this identity. Naturality of the right-derived unit moves the
p-structure map to its target, and naturality of the left-derived counit moves f sharp
to its source. The comparisons from tensor to ordinary pullback are the unique maps
preserving the common pushforward adjunction;
therefore canonicalSingleAdjunctionTranspose identifies the remaining composites with
the displayed canonical single maps. Reassociate to obtain the equation. This proof
also applies to empty schemes, where the same functorial and triangle identities hold. -/
theorem canonical_structure_map_base_change
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) :
    (derivedPullback g).map
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          Scheme.Modules.canonicalSingleDirectImageMap f
            (SheafOfModules.unit X.ringCatSheaf)) ≫
      (schemeDerivedBaseChangeMap f f' g p h
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            (SheafOfModules.unit X.ringCatSheaf)) ≫
        (schemeDerivedDirectImage f').map
          (Scheme.Modules.canonicalSinglePullbackMap p
              (SheafOfModules.unit X.ringCatSheaf) ≫
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map
                (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom))) =
    (Scheme.Modules.canonicalSinglePullbackMap g (SheafOfModules.unit S.ringCatSheaf) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
            (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)) ≫
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom) ≫
        Scheme.Modules.canonicalSingleDirectImageMap f'
          (SheafOfModules.unit X'.ringCatSheaf)) := by
  let tg := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction g)
  let tp := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction p)
  let b := tg.inv.app ((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit X.ringCatSheaf)) ≫
    Scheme.Modules.moduleBaseChangeMap f f' g p h (SheafOfModules.unit X.ringCatSheaf) ≫
    (Scheme.Modules.pushforward f').map (tp.hom.app (SheafOfModules.unit X.ringCatSheaf))
  have hb : (Scheme.Modules.pullback g).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫ b ≫
      (Scheme.Modules.pushforward f').map
        (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom) =
      SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom ≫
        SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom := by
    apply (cancel_epi (tg.hom.app (SheafOfModules.unit S.ringCatSheaf))).mp
    dsimp only [b]
    simp only [Category.assoc]
    erw [← tg.hom.naturality_assoc]
    erw [Iso.hom_inv_id_app_assoc]
    erw [← Functor.map_comp, tensor_structure_transport p,
      reassoc_of% (tensor_structure_transport g)]
    obtain ⟨mu, mu', _, _, _, _, he⟩ :=
      Scheme.Modules.moduleBaseChangeMap_algebra f f' g p h
    simpa only [Category.assoc] using he
  have he := Scheme.Modules.canonicalSingleBaseChangeComparison
    f f' g p h (SheafOfModules.unit X.ringCatSheaf)
  have hd := single_directImage_naturality f'
    (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom)
  have hp := single_pullback_naturality g
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  have hh := structure_map_pasting
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0)
    _ _ _ _ _ _ _ _ _ _ b _ _ _ he hd hp hb
  simpa only [Functor.map_comp, Category.assoc] using hh

end AlgebraicGeometry
