/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardFunctoriality
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardAffineSectionVanishing

/-! # Eventual vanishing of constant-module direct-image germs

Source: Stacks Project, Tag 09Z1, degree zero.
(blueprint: lem-weil-pbc-constant-module-pushforward-germ-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency.types false in
private theorem affine_point_refinement
    {X : Scheme.{u}} (s : X) (U : X.Etale)
    (v : (X.uliftPointSmallEtale s).fiber.obj U) :
    ∃ (W : X.Etale) (k : W ⟶ U) (w : (X.uliftPointSmallEtale s).fiber.obj W),
      IsAffine W.left ∧ (X.uliftPointSmallEtale s).fiber.map k w = v := by
  classical
  let v₀ := v.down
  change Over.mk (X.algClosurePoint s) ⟶ Over.mk U.hom at v₀
  obtain ⟨R, j, hj, hmem, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := v₀.left (default : Spec (.of (AlgebraicClosure (X.residueField s)))))
    (U := ⊤) (by simp)
  have := hj
  have : Subsingleton (Over.mk (X.algClosurePoint s)).left := by
    change Subsingleton (Spec (.of (AlgebraicClosure (X.residueField s))))
    infer_instance
  have hrange : Set.range v₀.left ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a
      (default : Spec (.of (AlgebraicClosure (X.residueField s))))]
  let l := IsOpenImmersion.lift j v₀.left hrange
  have hl : l ≫ j = v₀.left := IsOpenImmersion.lift_fac j v₀.left hrange
  let W : X.Etale := Scheme.Etale.mk (j ≫ U.hom)
  let k : W ⟶ U := MorphismProperty.Over.homMk j rfl
  let w₀ : (Scheme.pointSmallEtale (X.algClosurePoint s)).fiber.obj W :=
    Over.homMk l (by
      change l ≫ (j ≫ U.hom) = X.algClosurePoint s
      rw [← Category.assoc, hl]
      exact Over.w v₀)
  refine ⟨W, k, ULift.up w₀, inferInstanceAs (IsAffine (Spec R)), ?_⟩
  apply ULift.ext
  apply Over.OverMorphism.ext
  exact hl

/-- A germ of a constant-module direct image which vanishes at the limit already
vanishes after one transition of the inverse system.

Source: Stacks Project, Tag 09Z1, degree-zero injectivity in the proof; Tag 09YQ,
degree-zero continuity on affine etale test schemes.
(blueprint: lem-weil-pbc-constant-module-pushforward-germ-vanishing).

Proof: Represent the germ on an affine etale neighborhood U of the geometric point
of X. The hypothesis says that its restriction to U times_X Y is zero after shrinking
U; choose an affine etale refinement of that neighborhood. All U times_X D_i are
qcqs, their transition maps are affine, and their limit is U times_X Y. The canonical
pullback of a constant module sheaf is the same constant module sheaf. Degree-zero
continuity (Tag 09YQ, as used in Tag 09Z1) implies that a section which is zero on
U times_X Y is zero at a later stage. For a general cofiltered category, use the
final directed reindexing of Tag 0032; a common refinement supplies an arrow to the
original stage. The canonical transition is restriction of sections: the adjunction
unit, constant-sheaf comparison and direct-image composition in
constantModulePushforwardMap give exactly this restriction. Thus the section zero
equality gives the displayed equality of germs. Coefficients can be forgotten to
abelian groups, since constant sheaves, pullbacks, direct images and their canonical
maps commute with forgetting; zero and equality are reflected by that faithful
functor. This proves the assertion for any module, with no finiteness assumption.
The zero module is immediate; an empty limit still gives eventual zero by the same
qcqs continuity. A singleton system has an invertible transition to its limit. -/
theorem exists_constantModulePushforward_germ_eq_zero
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : ∀ i, D.obj i ⟶ X)
    (hp : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ p j = p i)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, QuasiCompact (p i)] [∀ i : I, QuasiSeparated (p i)]
    {Y : Scheme.{u}} (ν : Y ⟶ X)
    (π : (Functor.const I).obj Y ⟶ D) (hπ : ∀ i, π.app i ≫ p i = ν)
    [QuasiCompact ν] [QuasiSeparated ν]
    (hc : IsLimit (Cone.mk Y π))
    (s : X) (i : I)
    (x : ((X.uliftPointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj
        ((lowerStar (ModuleCat.{u + 1} Λ) (p i)).obj
          ((constantSheaf (D.obj i).smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).obj M)))
    (hx : ((X.uliftPointSmallEtale s).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map
        (constantModulePushforwardMap Λ M (p i) ν (π.app i) (hπ i)) x = 0) :
    ∃ (j : I) (g : j ⟶ i),
      ((X.uliftPointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map
          (constantModulePushforwardMap Λ M (p i) (p j) (D.map g) (hp g)) x = 0 := by
  classical
  let Φ := X.uliftPointSmallEtale s
  let F := (lowerStar (ModuleCat.{u + 1} Λ) (p i)).obj
    ((constantSheaf (D.obj i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  let G := (lowerStar (ModuleCat.{u + 1} Λ) ν).obj
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  let f : F ⟶ G := constantModulePushforwardMap Λ M (p i) ν (π.app i) (hπ i)
  obtain ⟨U, v, a, ha⟩ := Φ.toPresheafFiber_jointly_surjective (P := F.obj) x
  have hz : Φ.toPresheafFiber U v G.obj (f.hom.app (op U) a) =
      Φ.toPresheafFiber U v G.obj 0 := by
    rw [map_zero, ← Φ.toPresheafFiber_naturality_apply, ha]
    exact hx
  obtain ⟨V, k, w, hw, hzero⟩ := (Φ.toPresheafFiber_eq_iff' U v _ _).mp hz
  obtain ⟨W, l, t, hW, ht⟩ := affine_point_refinement s V w
  let := hW
  let b := F.obj.map l.op (F.obj.map k.op a)
  have hb : f.hom.app (op W) b = 0 := by
    dsimp [b]
    rw [f.hom.naturality_apply, f.hom.naturality_apply]
    rw [hzero, map_zero, map_zero]
  obtain ⟨j, g, hg⟩ := exists_constantModulePushforward_affine_section_eq_zero
    Λ M D p hp ν π hπ hc W i b hb
  refine ⟨j, g, ?_⟩
  have hrep : Φ.toPresheafFiber W t F.obj b = x := by
    dsimp [b]
    rw [Φ.toPresheafFiber_w_apply, ht, Φ.toPresheafFiber_w_apply, hw, ha]
  rw [← hrep]
  change Φ.presheafFiber.map
    (constantModulePushforwardMap Λ M (p i) (p j) (D.map g) (hp g)).hom
      (Φ.toPresheafFiber W t F.obj b) = 0
  rw [Φ.toPresheafFiber_naturality_apply, hg, map_zero]

end AlgebraicGeometry.Etale
