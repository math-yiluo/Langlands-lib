/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

import WeilConjectures.AlgebraicGeometry.KoszulSelfExtConormalCompatibleCover
import WeilConjectures.Topology.GlueSheavesOfModules
/-! # Alignment of local Koszul identifications

Source: Stacks Project, Tag 0BQY, comparison of regular generators. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry



set_option backward.isDefEq.respectTransparency false in
/-- Compatible local isomorphisms glue, by gluing their maps and inverses. -/
private theorem iso_of_compatible_cover
    (X : RingedSpace.{u}) (I : Type u) (U : I → TopologicalSpace.Opens X)
    (hcover : ⨆ i, U i = ⊤) (F G : SheafOfModules.{u} (moduleRings X))
    (e : ∀ i : I, F.over (U i) ≅ G.over (U i))
    (he : ∀ (i j : I) (W : TopologicalSpace.Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      (e i).hom.val.app (op (Over.mk (homOfLE hi))) =
        (e j).hom.val.app (op (Over.mk (homOfLE hj)))) : Nonempty (F ≅ G) := by
  have gl := glue_sheaves_of_modules.{u, u, u} X I U hcover
  obtain ⟨f, hf, _⟩ := gl.1 F G (fun i ↦ (e i).hom) he
  have hei : ∀ (i j : I) (W : TopologicalSpace.Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      (e i).inv.val.app (op (Over.mk (homOfLE hi))) =
        (e j).inv.val.app (op (Over.mk (homOfLE hj))) := by
    intro i j W hi hj
    let fi : F.val.obj (op W) ⟶ G.val.obj (op W) :=
      (e i).hom.val.app (op (Over.mk (homOfLE hi)))
    let fj : F.val.obj (op W) ⟶ G.val.obj (op W) :=
      (e j).hom.val.app (op (Over.mk (homOfLE hj)))
    let gi : G.val.obj (op W) ⟶ F.val.obj (op W) :=
      (e i).inv.val.app (op (Over.mk (homOfLE hi)))
    let gj : G.val.obj (op W) ⟶ F.val.obj (op W) :=
      (e j).inv.val.app (op (Over.mk (homOfLE hj)))
    have h : fi = fj := he i j W hi hj
    have h₁ : gi ≫ fi = 𝟙 _ := congrArg
      (fun k ↦ k.val.app (op (Over.mk (homOfLE hi)))) (e i).inv_hom_id
    have h₂ : fj ≫ gj = 𝟙 _ := congrArg
      (fun k ↦ k.val.app (op (Over.mk (homOfLE hj)))) (e j).hom_inv_id
    change gi = gj
    calc
      gi = gi ≫ (fj ≫ gj) := by rw [h₂, Category.comp_id]
      _ = gj := by rw [← Category.assoc, ← h, h₁, Category.id_comp]
  obtain ⟨g, hg, _⟩ := gl.1 G F (fun i ↦ (e i).inv) hei
  refine ⟨⟨f, g, ?_, ?_⟩⟩
  · apply gl.2.1 F F
    intro i
    change (SheafOfModules.overFunctor _ _).map (f ≫ g) =
      (SheafOfModules.overFunctor _ _).map (𝟙 F)
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
    change f.over (U i) ≫ g.over (U i) = 𝟙 _
    rw [hf, hg, (e i).hom_inv_id]
  · apply gl.2.1 G G
    intro i
    change (SheafOfModules.overFunctor _ _).map (g ≫ f) =
      (SheafOfModules.overFunctor _ _).map (𝟙 G)
    rw [Functor.map_comp, CategoryTheory.Functor.map_id]
    change g.over (U i) ≫ f.over (U i) = 𝟙 _
    rw [hg, hf, (e i).inv_hom_id]

set_option backward.isDefEq.respectTransparency false in
/-- Local isomorphisms can be adjusted by automorphisms of the source so that
all their components agree on overlaps.

Source: Stacks Project, Tag 0BQY, change of generators in the Koszul resolution.
(blueprint: new-w4-koszul-self-ext-local-alignment).

Proof: On each regular chart use the normalized Koszul Hom coordinate map.
On intersections refine by affine subopens around each point. The conormal
bases over its nonzero local ring have equal length; shrink so that a generator
substitution is invertible modulo the ideal. Empty intersections need no check.
A substitution between the two regular generator sets induces a chain map by
exterior powers in every degree.
The contraction identity checks the chain equation. Modulo the immersion ideal
its exterior powers are the conormal coordinate changes, whose duals are precisely
the Hom coordinate changes. Resolution comparison homotopies remove the choices
of substitutions, and localization preserves the formulas. Separatedness gives
agreement on every smaller open. Thus normalized comparisons glue, together with
their inverses, on each of the supplied neighborhoods. Comparing a supplied local
isomorphism e_z with the glued normalized one c_z gives the source automorphism
a_z = c_z followed by e_z.inv; its composite with e_z.hom is c_z.hom by the
inverse identity. This proves the asserted overlap
identities without assuming that arbitrary local isomorphisms already agree.
The empty scheme imposes no conditions, and degree zero uses the quotient unit. -/
theorem koszulRegularImmersion_self_ext_conormal_local_alignment
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ)
    (hregular : ∀ z : Z, z ∈ V → ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let F := (Scheme.Modules.restrictFunctor V.ι).obj
      (Scheme.Modules.dual (Scheme.Modules.exteriorPower
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n))
    ∀ (W : V.toScheme → V.toScheme.Opens)
      (e : ∀ z : V.toScheme, F.over (W z) ≅ T.over (W z)),
      (∀ z : V.toScheme, z ∈ W z) →
      ∃ a : ∀ z : V.toScheme, F.over (W z) ≅ F.over (W z),
        ∀ (x y : V.toScheme) (U : V.toScheme.Opens)
          (hx : U ≤ W x) (hy : U ≤ W y),
          ((a x).hom ≫ (e x).hom).val.app (op (Over.mk (homOfLE hx))) =
            ((a y).hom ≫ (e y).hom).val.app (op (Over.mk (homOfLE hy))) := by
  classical
  intro B S H G T F W e hW
  obtain ⟨W₀, hW₀, c₀, hc₀⟩ :=
    koszulRegularImmersion_self_ext_conormal_compatible_cover i V n hregular
  have hcover : ⨆ z, W₀ z = ⊤ := by
    apply top_unique
    intro z _
    exact (TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hW₀ z⟩)
  obtain ⟨c⟩ := iso_of_compatible_cover V.toScheme.toRingedSpace V.toScheme W₀ hcover F T c₀ hc₀
  let a : ∀ z : V.toScheme, F.over (W z) ≅ F.over (W z) :=
    fun z ↦ (SheafOfModules.overFunctor _ (W z)).mapIso c ≪≫ (e z).symm
  refine ⟨a, ?_⟩
  intro x y U hx hy
  have ha (z : V.toScheme) : (a z).hom ≫ (e z).hom = c.hom.over (W z) := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [ha x, ha y]
  rfl

end AlgebraicGeometry
