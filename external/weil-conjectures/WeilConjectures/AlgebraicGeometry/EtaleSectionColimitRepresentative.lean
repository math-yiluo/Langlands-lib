/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf

import WeilConjectures.AlgebraicGeometry.EtaleSectionColimitLocalLifts
import WeilConjectures.AlgebraicGeometry.EtaleSectionColimitEventualZero

/-! # Stage representatives in filtered etale sheaf colimits

Source: Stacks Project, Sites, Lemma Tag 0738, and Etale Cohomology, Tag 03Q4.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every section of a filtered colimit of module sheaves over a qcqs etale object
comes from a section at a diagram stage.
Source: Stacks Project, Sites, Lemma Tag 0738, proof of part (4), and Etale
Cohomology, Section Tag 03Q4 (blueprint: lem-weil-pbc-etale-section-colimit-representative).

Proof: Identify c.pt with the module sheafification of the sectionwise presheaf
colimit P, respecting the coprojections. A section t is locally represented in P.
Refine the local representing covering to a finite affine etale covering of U
with quasi-compact pairwise fibre products, using the qcqs finite-refinement lemma.
Choose a stage representative on each member. Filteredness puts the finitely many
representatives at one stage. On each pairwise fibre product their difference has
zero image in c.pt, as both images restrict from t. Apply the eventual-zero theorem
on that quasi-compact overlap. Choose a stage dominating the finitely many killing
arrows, equalizing the finitely many arrows from the common initial stage. The
transported representatives now agree on all overlaps. The sheaf condition at this
stage glues them to a section s over U. Its colimit image is t because this holds
on every covering member and c.pt is separated. Empty covers cause no exception:
the sheaf condition gives the unique zero section, and filteredness supplies an index. -/
theorem etale_section_colimit_representative
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    (U : X.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (c : Cocone G) (hc : IsColimit c) :
    ∀ t : c.pt.obj.obj (Opposite.op U),
      ∃ (i : I) (s : (G.obj i).obj.obj (Opposite.op U)),
        ((c.ι.app i).hom.app (Opposite.op U)).hom s = t := by
  classical
  intro t
  obtain ⟨B, hB, V, f, hcover, hcompact, i, s, hs⟩ :=
    etale_section_colimit_local_lifts X Λ U I G c hc t
  let : Finite B := hB
  have hnat (k : I) {Y Z : X.Etale} (a : Z ⟶ Y)
      (x : (G.obj k).obj.obj (Opposite.op Y)) :
      ((c.ι.app k).hom.app (Opposite.op Z)).hom
          (((G.obj k).obj.map a.op).hom x) =
        (c.pt.obj.map a.op).hom (((c.ι.app k).hom.app (Opposite.op Y)).hom x) := by
    exact (congrArg (fun z ↦ z.hom x) ((c.ι.app k).hom.naturality a.op))
  have hzero (b b' : B) :
      ((c.ι.app i).hom.app (Opposite.op (pullback (f b) (f b')))).hom
        (((G.obj i).obj.map (pullback.fst (f b) (f b')).op).hom (s b) -
          ((G.obj i).obj.map (pullback.snd (f b) (f b')).op).hom (s b')) = 0 := by
    rw [map_sub, hnat, hnat, hs, hs, sub_eq_zero]
    have h := congrArg (fun z ↦ (c.pt.obj.map z.op).hom t)
      (pullback.condition (f := f b) (g := f b'))
    simpa only [op_comp, Functor.map_comp, ModuleCat.comp_apply] using h
  have hkill (p : B × B) : ∃ (k : I) (a : i ⟶ k),
      ((G.map a).hom.app (Opposite.op (pullback (f p.1) (f p.2)))).hom
        (((G.obj i).obj.map (pullback.fst (f p.1) (f p.2)).op).hom (s p.1) -
          ((G.obj i).obj.map (pullback.snd (f p.1) (f p.2)).op).hom (s p.2)) = 0 := by
    let := hcompact p.1 p.2
    exact etale_section_colimit_eventual_zero X Λ _ I G c hc i _ (hzero p.1 p.2)
  choose k a ha using hkill
  obtain ⟨j, g, q, hq⟩ := IsFiltered.wideSpan a
  let sj (b : B) := ((G.map g).hom.app (Opposite.op (V b))).hom (s b)
  have htransition {k l : I} (a : k ⟶ l) {Y Z : X.Etale} (h : Z ⟶ Y)
      (x : (G.obj k).obj.obj (Opposite.op Y)) :
      ((G.obj l).obj.map h.op).hom (((G.map a).hom.app (Opposite.op Y)).hom x) =
        ((G.map a).hom.app (Opposite.op Z)).hom (((G.obj k).obj.map h.op).hom x) := by
    exact (congrArg (fun z ↦ z.hom x) ((G.map a).hom.naturality h.op)).symm
  have hpair (b b' : B) :
      ((G.obj j).obj.map (pullback.fst (f b) (f b')).op).hom (sj b) =
        ((G.obj j).obj.map (pullback.snd (f b) (f b')).op).hom (sj b') := by
    dsimp only [sj]
    rw [htransition, htransition, ← sub_eq_zero, ← map_sub]
    rw [← hq (b, b'), G.map_comp]
    change ((G.map (q (b, b'))).hom.app _).hom
      (((G.map (a (b, b'))).hom.app _).hom _) = 0
    rw [ha (b, b'), map_zero]
  let M : ModuleCat.{max v w} Λ := ModuleCat.of Λ (ULift.{w} Λ)
  let x (b : B) : M ⟶ (G.obj j).obj.obj (Opposite.op (V b)) :=
    ModuleCat.ofHom
      ((LinearMap.toSpanSingleton Λ _ (sj b)).comp ULift.moduleEquiv.toLinearMap)
  have hx : ∀ ⦃W : X.Etale⦄ ⦃b b' : B⦄ (r : W ⟶ V b) (r' : W ⟶ V b'),
      r ≫ f b = r' ≫ f b' →
        x b ≫ (G.obj j).obj.map r.op = x b' ≫ (G.obj j).obj.map r'.op := by
    intro W b b' r r' hr
    apply ModuleCat.hom_ext
    ext z
    change ((G.obj j).obj.map r.op).hom (z.down • sj b) =
      ((G.obj j).obj.map r'.op).hom (z.down • sj b')
    simp only [map_smul]
    congr 1
    let l := pullback.lift r r' hr
    have hh := congrArg (fun z ↦ ((G.obj j).obj.map l.op).hom z) (hpair b b')
    simpa only [← ModuleCat.comp_apply, ← Functor.map_comp, ← op_comp,
      pullback.lift_fst, pullback.lift_snd, l] using hh
  obtain ⟨y, hy, _⟩ :=
    (G.obj j).property.existsUnique_amalgamation_ofArrows f hcover x hx
  let z := y.hom (ULift.up 1)
  refine ⟨j, z, ?_⟩
  have hsj (b : B) : ((c.ι.app j).hom.app (Opposite.op (V b))).hom (sj b) =
      (c.pt.obj.map (f b).op).hom t := by
    dsimp only [sj]
    have h := congrArg (fun z ↦ (z.hom.app (Opposite.op (V b))).hom (s b))
      (c.w g)
    exact h.trans (hs b)
  let xt : M ⟶ c.pt.obj.obj (Opposite.op U) :=
    ModuleCat.ofHom ((LinearMap.toSpanSingleton Λ _ t).comp ULift.moduleEquiv.toLinearMap)
  have he : y ≫ (c.ι.app j).hom.app (Opposite.op U) = xt := by
    apply c.pt.property.hom_ext_ofArrows f hcover
    intro b
    have hn : (G.obj j).obj.map (f b).op ≫
        (c.ι.app j).hom.app (Opposite.op (V b)) =
        (c.ι.app j).hom.app (Opposite.op U) ≫ c.pt.obj.map (f b).op :=
      (c.ι.app j).hom.naturality (f b).op
    rw [Category.assoc, ← hn, ← Category.assoc, hy]
    apply ModuleCat.hom_ext
    ext z
    change ((c.ι.app j).hom.app (Opposite.op (V b))).hom (z.down • sj b) =
      (c.pt.obj.map (f b).op).hom (z.down • t)
    simpa only [map_smul] using congrArg (z.down • ·) (hsj b)
  have h := congrArg (fun q ↦ q.hom (ULift.up 1)) he
  change ((c.ι.app j).hom.app (Opposite.op U)).hom z = (1 : Λ) • t at h
  simpa only [one_smul] using h

end AlgebraicGeometry
