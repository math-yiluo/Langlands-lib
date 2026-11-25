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

import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.CategoryTheory.FilteredModuleSheafColimitLocalRepresentatives

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A colimit section has representatives at one stage on a finite covering with
quasi-compact overlaps. No compatibility of these representatives is asserted.
Source: Stacks Project, Sites, Tag 0738, proof of (4), and Etale Cohomology, Tag 03Q4
(blueprint: lem-weil-pbc-etale-section-colimit-local-lifts).

Proof: Form the sectionwise presheaf colimit and identify its module sheafification
with the given sheaf colimit, respecting the coprojections. Local representability
of sheafification supplies a covering on which the section comes from that presheaf.
Etale cancellation views this as a covering of the underlying scheme U. Refine it
by a finite affine etale covering with quasi-compact pairwise fibre products, using
quasi-compactness and quasi-separatedness of U. Regard its objects and overlaps in
X's small etale site by composition. Restrict the presheaf representatives to this
refinement. The filtered module-colimit representative criterion gives a diagram
index for each of the finitely many sections. Choose a common index using filteredness
and transport these representatives to it; cocone naturality preserves their images.
Index the finite family by a finite type in universe u. For an empty covering,
filteredness still supplies an index and the family of sections is empty. -/
theorem etale_section_colimit_local_lifts
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    (U : X.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (c : Cocone G) (hc : IsColimit c) (t : c.pt.obj.obj (op U)) :
    ∃ (B : Type u) (_ : Finite B) (V : B → X.Etale) (f : ∀ b, V b ⟶ U),
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U ∧
      (∀ b b', CompactSpace (pullback (f b) (f b')).left) ∧
      ∃ (i : I) (s : ∀ b, (G.obj i).obj.obj (op (V b))),
        ∀ b, ((c.ι.app i).hom.app (op (V b))).hom (s b) =
          (c.pt.obj.map (f b).op).hom t := by
  classical
  -- The local-image subsheaf argument supplies stage lifts without constructing
  -- a presheaf colimit or assuming sheafification in these independent universes.
  obtain ⟨S, hS, hrep⟩ :=
    filtered_module_sheaf_colimit_local_representatives X.smallEtaleTopology Λ I G c hc U t
  let A := S.arrows.category
  let T (a : A) : X.Etale := a.obj.left
  let g (a : A) : T a ⟶ U := a.obj.hom
  have hg : Sieve.ofArrows T g ∈ X.smallEtaleTopology U := by
    rw [show Sieve.ofArrows T g = S from Sieve.ofArrows_category S]
    exact hS
  have hg' := (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mp hg
  let C : U.left.Cover (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers A (fun a ↦ (T a).left) (fun a ↦ (g a).left)
      (fun x ↦ by
        have hx : x ∈ ⋃ a, Set.range (g a).left := by rw [hg']; trivial
        obtain ⟨a, y, hy⟩ := Set.mem_iUnion.mp hx
        exact ⟨a, y, hy⟩)
  let : QuasiCompactCover C.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun a ↦ (C.f a).isOpenMap)
  obtain ⟨D, k, hfin, _⟩ := QuasiCompactCover.exists_hom C
  let : Finite D.I₀ := hfin
  let : Fintype D.I₀ := Fintype.ofFinite D.I₀
  let B := ULift.{u} (Fin (Fintype.card D.I₀))
  let e : B ≃ D.I₀ := Equiv.ulift.trans (Fintype.equivFin D.I₀).symm
  let (b : B) : Etale (D.f (e b)) := D.map_prop (e b)
  let V (b : B) : X.Etale := Scheme.Etale.mk (D.f (e b) ≫ U.hom)
  let f (b : B) : V b ⟶ U := MorphismProperty.Over.homMk (D.f (e b))
  have hf : Sieve.ofArrows V f ∈ X.smallEtaleTopology U := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    change (⋃ b, Set.range (D.f (e b))) = Set.univ
    exact (e.surjective.iUnion_comp (fun j ↦ Set.range (D.f j))).trans D.cover.iUnion_range
  have hfS (b : B) : S (f b) := by
    let l : V b ⟶ T (k.s₀ (e b)) :=
      MorphismProperty.Over.homMk (k.h₀ (e b)) (by
        change k.h₀ (e b) ≫ (T (k.s₀ (e b))).hom = D.f (e b) ≫ U.hom
        rw [← MorphismProperty.Over.w (g (k.s₀ (e b))), ← Category.assoc]
        exact congrArg (fun q ↦ q ≫ U.hom) (k.w₀ (e b)))
    have hl : l ≫ g (k.s₀ (e b)) = f b := by
      apply MorphismProperty.Over.Hom.ext
      exact k.w₀ (e b)
    rw [← hl]
    exact S.downward_closed (k.s₀ (e b)).property l
  have hcompact (b b' : B) : CompactSpace (pullback (f b) (f b')).left := by
    let F := Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X
    let iso : (pullback (f b) (f b')).left ≅
        pullback (C := Scheme.{u}) (D.f (e b)) (D.f (e b')) :=
      PreservesPullback.iso F (f b) (f b')
    have : CompactSpace (pullback (C := Scheme.{u}) (D.f (e b)) (D.f (e b'))) :=
      inferInstance
    exact iso.inv.homeomorph.compactSpace
  choose j x hx using fun b ↦ hrep (V b) (f b) (hfS b)
  let : Fintype B := Fintype.ofFinite B
  obtain ⟨i, hi⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j)
  let a (b : B) : j b ⟶ i := (hi (Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩)).some
  refine ⟨B, inferInstance, V, f, hf, hcompact, i,
    (fun b ↦ ((G.map (a b)).hom.app (op (V b))).hom (x b)), ?_⟩
  intro b
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun q ↦ q.hom) (c.w (a b))) (op (V b))) (x b)
  change ((c.ι.app i).hom.app (op (V b))).hom
    (((G.map (a b)).hom.app (op (V b))).hom (x b)) = _ at h
  exact h.trans (hx b)

end AlgebraicGeometry
