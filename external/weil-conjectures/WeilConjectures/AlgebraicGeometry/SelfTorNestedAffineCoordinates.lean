/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.RingTheory.SelfTorConormalComparison
public import Mathlib.AlgebraicGeometry.Modules.Tilde

import WeilConjectures.AlgebraicGeometry.SelfTorLocalWedgeCoordinates
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Affine normalized self-Tor coordinates

Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-e1-self-tor-nested-affine-coordinates). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

-- Work with abstract module maps here so the derived tensor construction stays folded.
set_option backward.isDefEq.respectTransparency false in
private theorem exterior_over_component_ext
    {X : Scheme.{u}} (M Q : X.Modules) (n : ℕ) (L₁ L₂ W : X.Opens)
    (a₁ : W ⟶ L₁) (a₂ : W ⟶ L₂)
    (f : (Scheme.Modules.exteriorPower M n).over L₁ ⟶ Q.over L₁)
    (g : (Scheme.Modules.exteriorPower M n).over L₂ ⟶ Q.over L₂)
    (hwedge : ∀ (V : X.Opens) (b : V ⟶ W)
      (v : Fin n → M.val.obj (op V)) (p : X) (_hp : p ∈ V),
      ∃ (V' : X.Opens) (hV' : V' ≤ V), p ∈ V' ∧
        Q.presheaf.map (homOfLE hV').op
            (f.val.app (op (Over.mk (b ≫ a₁)))
              (Scheme.Modules.wedge (M := M) (r := n) (U := V) v)) =
          Q.presheaf.map (homOfLE hV').op
            (g.val.app (op (Over.mk (b ≫ a₂)))
              (Scheme.Modules.wedge (M := M) (r := n) (U := V) v))) :
    f.val.app (op (Over.mk a₁)) = g.val.app (op (Over.mk a₂)) := by
  let E := Scheme.Modules.exteriorPower M n
  let η := (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 X.ringCatSheaf.obj)).unit.app ((_root_.PresheafOfModules.exteriorPower (R := _) M.val n))
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map η) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallySurjective
  apply ModuleCat.hom_ext
  ext x
  let R := Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map η) x
  have hR : R ∈ Opens.grothendieckTopology X W := Presheaf.imageSieve_mem _ _ _
  have hQ := (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf (Opens.grothendieckTopology X) _
      (forget _) Q.isSheaf)
  apply (hQ R hR).isSeparatedFor.ext
  intro V b hb
  obtain ⟨z, hz⟩ := hb
  change η.app (op V) z = E.val.map b.op x at hz
  have hf := PresheafOfModules.naturality_apply f.val
    (Over.homMk b : Over.mk (b ≫ a₁) ⟶ Over.mk a₁).op x
  have hg := PresheafOfModules.naturality_apply g.val
    (Over.homMk b : Over.mk (b ≫ a₂) ⟶ Over.mk a₂).op x
  change f.val.app (op (Over.mk (b ≫ a₁))) (E.val.map b.op x) =
    Q.presheaf.map b.op (f.val.app (op (Over.mk a₁)) x) at hf
  change g.val.app (op (Over.mk (b ≫ a₂))) (E.val.map b.op x) =
    Q.presheaf.map b.op (g.val.app (op (Over.mk a₂)) x) at hg
  change Q.presheaf.map b.op (f.val.app (op (Over.mk a₁)) x) =
    Q.presheaf.map b.op (g.val.app (op (Over.mk a₂)) x)
  rw [← hf, ← hg, ← hz]
  have hzspan : z ∈ Submodule.span (X.presheaf.obj (op V))
      (Set.range (exteriorPower.ιMulti (X.presheaf.obj (op V)) n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  clear hz
  induction hzspan using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    apply Q.isSheaf.section_ext
    intro p hp
    exact hwedge V b v p hp
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    rw [(η.app (op V)).hom.map_smul,
      (f.val.app (op (Over.mk (b ≫ a₁)))).hom.map_smul,
      (g.val.app (op (Over.mk (b ≫ a₂)))).hom.map_smul, hx]

private theorem exterior_over_component_ext_le
    {X : Scheme.{u}} (M Q : X.Modules) (n : ℕ) (L₁ L₂ : X.Opens) (h : L₂ ≤ L₁)
    (f : (Scheme.Modules.exteriorPower M n).over L₁ ⟶ Q.over L₁)
    (g : (Scheme.Modules.exteriorPower M n).over L₂ ⟶ Q.over L₂)
    (hwedge : ∀ (W : X.Opens) (hW : W ≤ L₂)
      (a : Fin n → M.val.obj (op W)) (p : X) (_hp : p ∈ W),
      ∃ (W' : X.Opens) (hW' : W' ≤ W), p ∈ W' ∧
        Q.presheaf.map (homOfLE hW').op
            (f.val.app (op (Over.mk (homOfLE (hW.trans h))))
              (Scheme.Modules.wedge (M := M) (r := n) (U := W) a)) =
          Q.presheaf.map (homOfLE hW').op
            (g.val.app (op (Over.mk (homOfLE hW)))
              (Scheme.Modules.wedge (M := M) (r := n) (U := W) a))) :
    f.val.app (op (Over.mk (homOfLE h))) = g.val.app (op (Over.mk (𝟙 L₂))) := by
  apply exterior_over_component_ext
  intro W b a p hp
  obtain ⟨W', hW', hpW', heq⟩ := hwedge W (leOfHom b) a p hp
  refine ⟨W', hW', hpW', ?_⟩
  have hb₁ : homOfLE ((leOfHom b).trans h) = b ≫ homOfLE h := Subsingleton.elim _ _
  have hb₂ : homOfLE (leOfHom b) = b ≫ 𝟙 L₂ := Subsingleton.elim _ _
  rw [hb₁, hb₂] at heq
  exact heq

set_option backward.isDefEq.respectTransparency false in
/-- Choose affine source and target coordinates using quotient resolutions and conormal
classes. The conjugated comparisons agree on the whole smaller affine chart's sections.
No assertion on an arbitrary subopen, an incomparable overlap or a global map is made.
Source: Stacks Project, Tags 09PQ, 01R3 and 06YH.
(blueprint: new-e1-self-tor-nested-affine-coordinates).

Proof: On U = Spec A use the quotient presentation defined by i.ker.ideal U and a
projective resolution P of A/I. Apply exists_affine_quotient_sheafified_resolution to its
augmentation. Its tensor with A/I computes the restriction of the fixed derived tensor:
termwise projectives sheafify to flat modules, the bounded-above cochain resolution is
K-flat, and comparison with a K-flat model gives the same homology. The quotient action
on this homology identifies its tensor pullback with the associated Tor module on the
closed affine chart. This gives t_U. The conormal sections theorem identifies i*ker(i)
with the associated I/I², preserving the class of each ideal section. Applying the
exterior universal property and sheafification gives s_U. Use these specific coordinates,
rather than arbitrary isomorphisms. For V affine inside U, cover V by principal opens
of U lying in V, then refine each by principal opens of V. Quotient resolutions and
the conormal unit localize. Flat localization commutes with resolution homology, and
sends the normalized algebraic comparison to the normalized comparison: apply its
Koszul normalization on tuples of ideal elements and extend by multilinearity to
localized tuples. Uniqueness of the normalized comparison identifies the two products.
The chosen resolution identifications commute with these comparison maps in the
derived category, independently of the resolutions. Thus the conjugated comparisons
have identical images of pure wedges on each refinement. Those wedges generate the
localized exterior modules; the target sheaf's separatedness then identifies their
values on all sections over i^-1 V. This is exactly the displayed nested top-component
equation. Degree zero uses the empty wedge and the quotient unit; the empty chart,
zero quotient, zero ideal and nonregular ideals require no exceptions.

Lean reduction: exists_local_wedge_selfTor_coordinates supplies the coordinates and
local agreement only on pure wedges. The proved exterior_over_component_ext helper
extends that agreement by span induction on sections of the exterior presheaf,
local surjectivity of the sheafification unit, and separatedness of the target.
Thus the general-section and top-component part of the argument is proved here. -/
theorem exists_nested_affine_selfTor_coordinates
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    let E := Scheme.Modules.exteriorPower
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n
    let T := fun U : Y.affineOpens ↦
      tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    let c := fun U : Y.affineOpens ↦
      selfTorConormalComparison (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    ∃ (s : ∀ U : Y.affineOpens,
        E.over (i ⁻¹ᵁ U.1) ≅ ((T U).obj _).over (i ⁻¹ᵁ U.1))
      (t : ∀ U : Y.affineOpens,
        ((T U).obj _).over (i ⁻¹ᵁ U.1) ≅ Q.over (i ⁻¹ᵁ U.1)),
      let φ := fun U ↦ (s U).hom ≫ ((T U).map (c U)).over (i ⁻¹ᵁ U.1) ≫ (t U).hom
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1),
        (φ U).val.app
            (op (Over.mk (homOfLE ((TopologicalSpace.Opens.map i.base).monotone h)))) =
          (φ V).val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1)))) := by
  classical
  obtain ⟨s, t, hwedge⟩ := exists_local_wedge_selfTor_coordinates i n
  refine ⟨s, t, ?_⟩
  intro φ V U h
  exact exterior_over_component_ext_le _ _ n _ _
    ((TopologicalSpace.Opens.map i.base).monotone h) (φ U) (φ V) (hwedge V U h)

end AlgebraicGeometry
