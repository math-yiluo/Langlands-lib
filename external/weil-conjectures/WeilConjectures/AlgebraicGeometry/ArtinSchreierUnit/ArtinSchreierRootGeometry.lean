/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

/-! # Coordinates of roots of the universal Artin–Schreier cover

Source: latest blueprint, lem-wft-as-unit-trivialization.proof.md, the root charts
in Multiplicativity and Duality (blueprint: lem-wft-as-root-coordinate-calculus).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierUnit

attribute [local irreducible] AffineSpace.neg AffineSpace.homOfVector
  AffineSpace.artinSchreierMap Etale.artinSchreierScaling


variable (k : Type u) [Field k] [Fintype k]
variable (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The universal Artin–Schreier covering `t ↦ t ^ q - t` of the affine line over `k`,
as an object over the affine line. -/
abbrev universalCover : Over (AffineSpace PUnit (Spec (.of k))) :=
  Over.mk (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))

/-- A root is an actual morphism to the universal covering, over the function map. -/
abbrev Root (f : Γ(X, ⊤)) :=
  Over.mk (AffineSpace.homOfVector (X ↘ Spec (.of k))
    (fun _ : PUnit ↦ f)) ⟶ universalCover k

/-- The coordinate of a root, in the structure sheaf of the original scheme. -/
def rootCoordinate {f : Γ(X, ⊤)} (s : Root k X f) : Γ(X, ⊤) :=
  s.left.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)

/-- The covering equation evaluated at a root. This works also on the empty scheme. -/
theorem rootCoordinate_equation {f : Γ(X, ⊤)} (s : Root k X f) :
    rootCoordinate k X s ^ Fintype.card k - rootCoordinate k X s = f := by
  have h := congrArg
    (fun g ↦ g.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) (Over.w s)
  dsimp only [universalCover, Over.mk_hom] at h
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  erw [AffineSpace.artinSchreierMap_appTop_coord] at h
  simpa only [map_sub, map_pow, AffineSpace.homOfVector_appTop_coord, rootCoordinate]
    using h

private theorem root_over {f : Γ(X, ⊤)} (s : Root k X f) :
    s.left ≫ (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)) =
      (X ↘ Spec (.of k)) := by
  have h := congrArg (fun g ↦ g ≫
    (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))) (Over.w s)
  simpa only [universalCover, Over.mk_hom, Category.assoc,
    AffineSpace.artinSchreierMap_over, AffineSpace.homOfVector_over] using h

/-- Root morphisms are determined by their coordinate; no connectedness is needed. -/
theorem root_ext {f : Γ(X, ⊤)} (s t : Root k X f)
    (h : rootCoordinate k X s = rootCoordinate k X t) : s = t := by
  apply Over.OverMorphism.ext
  apply AffineSpace.hom_ext
  · exact (root_over k X s).trans (root_over k X t).symm
  · intro i
    cases i
    exact h

/-- Construct a root from a global section satisfying the covering equation. -/
def rootOfSection (f r : Γ(X, ⊤)) (hr : r ^ Fintype.card k - r = f) : Root k X f :=
  Over.homMk (AffineSpace.homOfVector (X ↘ Spec (.of k)) (fun _ : PUnit ↦ r)) (by
    apply AffineSpace.hom_ext
    · simp only [universalCover, Over.mk_hom, Category.assoc,
        AffineSpace.artinSchreierMap_over, AffineSpace.homOfVector_over]
    · intro i
      dsimp only [universalCover, Over.mk_hom]
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      erw [AffineSpace.artinSchreierMap_appTop_coord]
      rw [map_sub, map_pow]
      erw [AffineSpace.homOfVector_appTop_coord, AffineSpace.homOfVector_appTop_coord]
      exact hr)

/-- The construction has precisely the given coordinate. -/
@[simp] theorem rootOfSection_coordinate (f r : Γ(X, ⊤))
    (hr : r ^ Fintype.card k - r = f) :
    rootCoordinate k X (rootOfSection k X f r hr) = r :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- The zero root, constructed over every k-scheme. -/
def zeroRoot : Root k X 0 :=
  rootOfSection k X 0 0 (by rw [zero_pow Fintype.card_pos.ne', sub_zero])

@[simp] theorem zeroRoot_coordinate : rootCoordinate k X (zeroRoot k X) = 0 :=
  rootOfSection_coordinate k X _ _ _

/-- Any zero-coordinate root of zero is the distinguished zero root. -/
theorem eq_zeroRoot (s : Root k X 0) (h : rootCoordinate k X s = 0) :
    s = zeroRoot k X :=
  root_ext k X s (zeroRoot k X) (h.trans (zeroRoot_coordinate k X).symm)

/-- q-power Frobenius is additive on sections of every k-scheme. -/
theorem rootSection_pow_add (r t : Γ(X, ⊤)) :
    (r + t) ^ Fintype.card k = r ^ Fintype.card k + t ^ Fintype.card k := by
  let : Algebra k Γ(X, ⊤) :=
    ((X ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  exact (FiniteField.frobeniusAlgHom k Γ(X, ⊤)).map_add r t

/-- q-power Frobenius respects negation on all k-schemes. -/
theorem rootSection_pow_neg (r : Γ(X, ⊤)) :
    (-r) ^ Fintype.card k = -(r ^ Fintype.card k) := by
  let : Algebra k Γ(X, ⊤) :=
    ((X ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  exact map_neg (FiniteField.frobeniusAlgHom k Γ(X, ⊤)) r

/-- Adding two roots gives a root of the sum function, with its actual sum coordinate. -/
def addRoot {f g : Γ(X, ⊤)} (s : Root k X f) (t : Root k X g) : Root k X (f + g) :=
  rootOfSection k X (f + g) (rootCoordinate k X s + rootCoordinate k X t) (by
    rw [rootSection_pow_add]
    linear_combination rootCoordinate_equation k X s + rootCoordinate_equation k X t)

@[simp] theorem addRoot_coordinate {f g : Γ(X, ⊤)} (s : Root k X f) (t : Root k X g) :
    rootCoordinate k X (addRoot k X s t) = rootCoordinate k X s + rootCoordinate k X t :=
  rootOfSection_coordinate k X _ _ _

/-- Negating a root gives a root of the negative function, including in characteristic two. -/
def negRoot {f : Γ(X, ⊤)} (s : Root k X f) : Root k X (-f) :=
  rootOfSection k X (-f) (-rootCoordinate k X s) (by
    rw [rootSection_pow_neg]
    linear_combination -rootCoordinate_equation k X s)

@[simp] theorem negRoot_coordinate {f : Γ(X, ⊤)} (s : Root k X f) :
    rootCoordinate k X (negRoot k X s) = -rootCoordinate k X s :=
  rootOfSection_coordinate k X _ _ _

omit [Fintype k] in
private theorem affine_neg_of_coordinates
    (a b : X ⟶ AffineSpace PUnit (Spec (.of k)))
    (ha : a ≫ (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)) = X ↘ Spec (.of k))
    (hb : b ≫ (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)) = X ↘ Spec (.of k))
    (hc : b.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      -a.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) :
    b = a ≫ AffineSpace.neg PUnit (Spec (.of k)) := by
  apply AffineSpace.hom_ext
  · rw [hb, Category.assoc, AffineSpace.neg_over, ha]
  · intro i
    cases i
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    erw [AffineSpace.neg_appTop_coord]
    rw [map_neg]
    exact hc

omit [Fintype k] in
/-- The negative function map is composition with affine-line negation. -/
theorem functionMap_neg (f : Γ(X, ⊤)) :
    AffineSpace.homOfVector (X ↘ Spec (.of k)) (fun _ : PUnit ↦ -f) =
      AffineSpace.homOfVector (X ↘ Spec (.of k)) (fun _ : PUnit ↦ f) ≫
        AffineSpace.neg PUnit (Spec (.of k)) := by
  apply affine_neg_of_coordinates k X
  · exact AffineSpace.homOfVector_over _ _
  · exact AffineSpace.homOfVector_over _ _
  · rw [AffineSpace.homOfVector_appTop_coord, AffineSpace.homOfVector_appTop_coord]

/-- Transport the indexing function of a root along equality of functions. -/
def castRoot {f g : Γ(X, ⊤)} (h : f = g) (s : Root k X f) : Root k X g := h ▸ s

@[simp] theorem castRoot_coordinate {f g : Γ(X, ⊤)} (h : f = g) (s : Root k X f) :
    rootCoordinate k X (castRoot k X h s) = rootCoordinate k X s := by
  subst g
  rfl

/-- Involutivity of negation is equality of root morphisms, after the function transport. -/
theorem negRoot_negRoot {f : Γ(X, ⊤)} (s : Root k X f) :
    castRoot k X (neg_neg f) (negRoot k X (negRoot k X s)) = s := by
  apply root_ext
  simp only [castRoot_coordinate, negRoot_coordinate, neg_neg]

/-- The distinguished zero root is fixed by negation. -/
theorem negRoot_zeroRoot :
    castRoot k X (neg_zero : -(0 : Γ(X, ⊤)) = 0) (negRoot k X (zeroRoot k X)) =
      zeroRoot k X := by
  apply root_ext
  simp only [castRoot_coordinate, negRoot_coordinate, zeroRoot_coordinate, neg_zero]

/-- The two ways of adding three roots agree after associativity transport. -/
theorem addRoot_assoc {f g h : Γ(X, ⊤)} (r : Root k X f) (s : Root k X g)
    (t : Root k X h) :
    castRoot k X (add_assoc f g h) (addRoot k X (addRoot k X r s) t) =
      addRoot k X r (addRoot k X s t) := by
  apply root_ext
  simp only [castRoot_coordinate, addRoot_coordinate, add_assoc]

/-- Addition of the zero root gives the original root after the unit transport. -/
theorem addRoot_zero_left {f : Γ(X, ⊤)} (s : Root k X f) :
    castRoot k X (zero_add f) (addRoot k X (zeroRoot k X) s) = s := by
  apply root_ext
  simp only [castRoot_coordinate, addRoot_coordinate, zeroRoot_coordinate, zero_add]

/-- Pull a root back by pulling its coordinate back; the construction uses no choice. -/
def pullRoot (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of k))] {f : Γ(Y, ⊤)} (s : Root k Y f) :
    Root k X (g.appTop f) :=
  rootOfSection k X (g.appTop f) (g.appTop (rootCoordinate k Y s)) (by
    rw [← map_pow, ← map_sub, rootCoordinate_equation])

@[simp] theorem pullRoot_coordinate (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of k))] {f : Γ(Y, ⊤)} (s : Root k Y f) :
    rootCoordinate k X (pullRoot k X Y g s) = g.appTop (rootCoordinate k Y s) :=
  rootOfSection_coordinate k X _ _ _

/-- Coordinate-defined root pullback is actual composition of scheme morphisms. -/
theorem pullRoot_left (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of k))] {f : Γ(Y, ⊤)} (s : Root k Y f) :
    (pullRoot k X Y g s).left = g ≫ s.left := by
  apply AffineSpace.hom_ext
  · calc
      (pullRoot k X Y g s).left ≫ _ = (X ↘ Spec (.of k)) :=
        root_over k X (pullRoot k X Y g s)
      _ = g ≫ (Y ↘ Spec (.of k)) := (CategoryTheory.comp_over g _).symm
      _ = (g ≫ s.left) ≫ _ := by rw [Category.assoc, root_over k Y s]
  · intro i
    cases i
    change rootCoordinate k X (pullRoot k X Y g s) = _
    rw [pullRoot_coordinate, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rfl

/-- Root pullback preserves the distinguished zero root. -/
theorem pullRoot_zeroRoot (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of k))] :
    castRoot k X (map_zero g.appTop.hom) (pullRoot k X Y g (zeroRoot k Y)) =
      zeroRoot k X := by
  apply root_ext
  simp only [castRoot_coordinate, pullRoot_coordinate, zeroRoot_coordinate, map_zero]

/-- Root pullback commutes with adding roots and the canonical function transport. -/
theorem pullRoot_addRoot (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of k))] {f h : Γ(Y, ⊤)}
    (s : Root k Y f) (t : Root k Y h) :
    castRoot k X (map_add g.appTop.hom f h) (pullRoot k X Y g (addRoot k Y s t)) =
      addRoot k X (pullRoot k X Y g s) (pullRoot k X Y g t) := by
  apply root_ext
  simp only [castRoot_coordinate, pullRoot_coordinate, addRoot_coordinate, map_add]

/-- Root pullback commutes with negation and the canonical function transport. -/
theorem pullRoot_negRoot (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (g : X ⟶ Y) [g.IsOver (Spec (.of k))] {f : Γ(Y, ⊤)} (s : Root k Y f) :
    castRoot k X (map_neg g.appTop.hom f) (pullRoot k X Y g (negRoot k Y s)) =
      negRoot k X (pullRoot k X Y g s) := by
  apply root_ext
  simp only [castRoot_coordinate, pullRoot_coordinate, negRoot_coordinate, map_neg]

/-- A quasi-compact surjective pullback detects equality of condensed-module maps. -/
theorem condensedModule_hom_ext_of_surjective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y : Scheme.{u}} (g : Y ⟶ X) [QuasiCompact g]
    (hg : Function.Surjective g.base)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)} (a b : M ⟶ N)
    (h : (ProEtale.CondensedRing.upperStar Λ g).map a =
      (ProEtale.CondensedRing.upperStar Λ g).map b) : a = b := by
  apply Mod.hom_ext
  have hab : (ProEtale.upperStar Ab.{u + 1} g).map a.hom =
      (ProEtale.upperStar Ab.{u + 1} g).map b.hom := by
    apply (cancel_mono (ProEtale.CondensedRing.upperStarUnitHom Λ g N)).1
    rw [← ProEtale.CondensedRing.upperStarUnitHom_map_hom,
      ← ProEtale.CondensedRing.upperStarUnitHom_map_hom, h]
  apply sub_eq_zero.mp
  apply ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp
    (fun _ : PUnit.{u + 1} ↦ g) (fun x ↦ ⟨PUnit.unit, hg x⟩)
  intro i
  rw [Functor.map_sub, hab, sub_self]

/-- Every function has a finite, surjective chart on which it has a specified root.
The chart is the actual pullback of the universal covering, not an existence-based
choice of a root. -/
theorem exists_root_chart (f : Γ(X, ⊤)) :
    ∃ (Y : Scheme.{u}) (_ : Y.Over (Spec (.of k)))
      (g : Y ⟶ X) (_ : g.IsOver (Spec (.of k))),
      IsFinite g ∧ Function.Surjective g.base ∧ Nonempty (Root k Y (g.appTop f)) := by
  let a := AffineSpace.homOfVector (X ↘ Spec (.of k)) (fun _ : PUnit ↦ f)
  let b := (universalCover k).hom
  let Y := pullback b a
  let g : Y ⟶ X := pullback.snd b a
  let : Y.Over (Spec (.of k)) := ⟨g ≫ (X ↘ Spec (.of k))⟩
  let : g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsFinite b := inferInstanceAs (IsFinite
    (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)))
  have : Surjective b := ⟨AffineSpace.surjective_artinSchreierMap k⟩
  have : IsFinite g := inferInstanceAs (IsFinite (pullback.snd b a))
  have : Surjective g := inferInstanceAs (Surjective (pullback.snd b a))
  refine ⟨Y, inferInstance, g, inferInstance, inferInstance, this.surj, ?_⟩
  let r := (pullback.fst b a).appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)
  refine ⟨rootOfSection k Y (g.appTop f) r ?_⟩
  have he := congrArg (fun m ↦ m.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))
    (pullback.condition (f := b) (g := a))
  have hb : b.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      AffineSpace.coord (Spec (.of k)) PUnit.unit ^ Fintype.card k -
        AffineSpace.coord (Spec (.of k)) PUnit.unit :=
    AffineSpace.artinSchreierMap_appTop_coord _ _ _ _
  have ha : a.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) = f :=
    AffineSpace.homOfVector_appTop_coord _ _ _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hb, ha, map_sub, map_pow] at he
  exact he


/-- Condensed-module maps agree when they agree after every root chart of one function. -/
theorem condensedModule_hom_ext_on_roots
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f : Γ(X, ⊤))
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)} (a b : M ⟶ N)
    (h : ∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
      (g : Y ⟶ X) [g.IsOver (Spec (.of k))], Root k Y (g.appTop f) →
      (ProEtale.CondensedRing.upperStar Λ g).map a =
        (ProEtale.CondensedRing.upperStar Λ g).map b) : a = b := by
  obtain ⟨Y, hY, g, hg, hf, hs, ⟨s⟩⟩ := exists_root_chart k X f
  let := hY
  let := hg
  let := hf
  exact condensedModule_hom_ext_of_surjective X Λ g hs a b (h Y g s)

/-- Two functions admit roots on a common finite surjective chart. -/
theorem exists_pair_root_chart (f h : Γ(X, ⊤)) :
    ∃ (Y : Scheme.{u}) (_ : Y.Over (Spec (.of k)))
      (g : Y ⟶ X) (_ : g.IsOver (Spec (.of k))),
      IsFinite g ∧ Function.Surjective g.base ∧
        Nonempty (Root k Y (g.appTop f)) ∧ Nonempty (Root k Y (g.appTop h)) := by
  obtain ⟨Y, hY, g, hg, hfg, hsg, ⟨s⟩⟩ := exists_root_chart k X f
  let := hY
  let := hg
  let := hfg
  obtain ⟨Z, hZ, j, hj, hfj, hsj, ⟨t⟩⟩ := exists_root_chart k Y (g.appTop h)
  let := hZ
  let := hj
  let := hfj
  have hscomp : Function.Surjective (j ≫ g).base := hsg.comp hsj
  refine ⟨Z, hZ, j ≫ g, inferInstance, inferInstance, hscomp, ?_, ?_⟩
  · refine ⟨castRoot k Z ?_ (pullRoot k Z Y j s)⟩
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  · refine ⟨castRoot k Z ?_ t⟩
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- Identities of module maps can be checked on simultaneous root charts for two functions. -/
theorem condensedModule_hom_ext_on_pair_roots
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f h : Γ(X, ⊤))
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)} (a b : M ⟶ N)
    (H : ∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
      (g : Y ⟶ X) [g.IsOver (Spec (.of k))],
      Root k Y (g.appTop f) → Root k Y (g.appTop h) →
      (ProEtale.CondensedRing.upperStar Λ g).map a =
        (ProEtale.CondensedRing.upperStar Λ g).map b) : a = b := by
  obtain ⟨Y, hY, g, hg, hf, hs, ⟨s⟩, ⟨t⟩⟩ := exists_pair_root_chart k X f h
  let := hY
  let := hg
  let := hf
  exact condensedModule_hom_ext_of_surjective X Λ g hs a b (H Y g s t)

/-- Three functions admit roots on a common finite surjective chart. -/
theorem exists_triple_root_chart (f h l : Γ(X, ⊤)) :
    ∃ (Y : Scheme.{u}) (_ : Y.Over (Spec (.of k)))
      (g : Y ⟶ X) (_ : g.IsOver (Spec (.of k))),
      IsFinite g ∧ Function.Surjective g.base ∧
        Nonempty (Root k Y (g.appTop f)) ∧ Nonempty (Root k Y (g.appTop h)) ∧
          Nonempty (Root k Y (g.appTop l)) := by
  obtain ⟨Y, hY, g, hg, hfg, hsg, ⟨s⟩, ⟨t⟩⟩ := exists_pair_root_chart k X f h
  let := hY
  let := hg
  let := hfg
  obtain ⟨Z, hZ, j, hj, hfj, hsj, ⟨v⟩⟩ := exists_root_chart k Y (g.appTop l)
  let := hZ
  let := hj
  let := hfj
  have hscomp : Function.Surjective (j ≫ g).base := hsg.comp hsj
  refine ⟨Z, hZ, j ≫ g, inferInstance, inferInstance, hscomp, ?_, ?_, ?_⟩
  · refine ⟨castRoot k Z ?_ (pullRoot k Z Y j s)⟩
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  · refine ⟨castRoot k Z ?_ (pullRoot k Z Y j t)⟩
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  · refine ⟨castRoot k Z ?_ v⟩
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- Associativity diagrams can be checked after adjoining roots of three functions. -/
theorem condensedModule_hom_ext_on_triple_roots
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (f h l : Γ(X, ⊤))
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)} (a b : M ⟶ N)
    (H : ∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
      (g : Y ⟶ X) [g.IsOver (Spec (.of k))],
      Root k Y (g.appTop f) → Root k Y (g.appTop h) → Root k Y (g.appTop l) →
      (ProEtale.CondensedRing.upperStar Λ g).map a =
        (ProEtale.CondensedRing.upperStar Λ g).map b) : a = b := by
  obtain ⟨Y, hY, g, hg, hf, hs, ⟨s⟩, ⟨t⟩, ⟨v⟩⟩ := exists_triple_root_chart k X f h l
  let := hY
  let := hg
  let := hf
  exact condensedModule_hom_ext_of_surjective X Λ g hs a b (H Y g s t v)

end AlgebraicGeometry.ArtinSchreierUnit
