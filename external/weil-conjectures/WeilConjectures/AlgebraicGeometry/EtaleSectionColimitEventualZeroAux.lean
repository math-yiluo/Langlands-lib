/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf

import WeilConjectures.AlgebraicGeometry.EtaleSectionColimitLocalZero
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finite-family reduction for eventual vanishing of a section.  The hypotheses
record the local vanishing data and the separatedness implication; the remaining
argument is the finite filtered-category equalisation from Sites, Tag 0738.
Source: Stacks Project, Sites, Lemma Tag 0738, proof of part (2).
The finite family is equalized using filteredness, and separatedness then gives
the global vanishing. (blueprint: lem-weil-pbc-etale-section-colimit-eventual-zero-finite-cover). -/
theorem etale_section_colimit_eventual_zero_of_finite_cover
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    (U : X.Etale) (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (i : I) (s : (G.obj i).obj.obj (Opposite.op U))
    (K : Type w) [Finite K] (V : K → X.Etale) (q : ∀ k, V k ⟶ U)
    (hlocal : ∀ k, ∃ (j : I) (f : i ⟶ j),
      ((G.map f).hom.app (Opposite.op (V k))).hom
        (((G.obj i).obj.map (q k).op).hom s) = 0)
    (hsep : ∀ (j : I) (t : (G.obj j).obj.obj (Opposite.op U)),
      (∀ k, ((G.obj j).obj.map (q k).op).hom t = 0) → t = 0) :
    ∃ (j : I) (f : i ⟶ j), ((G.map f).hom.app (Opposite.op U)).hom s = 0 := by
  classical
  choose j f hf using hlocal
  obtain ⟨l, g, a, ha⟩ := IsFiltered.wideSpan f
  refine ⟨l, g, hsep l _ ?_⟩
  intro k
  have hnat := congrArg (fun z ↦ z.hom s) ((G.map g).hom.naturality (q k).op)
  simp only [ModuleCat.comp_apply] at hnat
  rw [← hnat, ← ha k, G.map_comp]
  change ((G.map (a k)).hom.app (Opposite.op (V k))).hom
    (((G.map (f k)).hom.app (Opposite.op (V k))).hom
      (((G.obj i).obj.map (q k).op).hom s)) = 0
  rw [hf k, map_zero]

/-- Extraction of finite local data from a zero section in the sheaf colimit.
Source: Stacks Project, Sites, Lemma Tag 0738, proof of part (2), together
with the etale openness and quasi-compactness arguments.  Sheafification gives
local equality, etale maps have open images, and compactness extracts finitely
many members; these are recorded as local eventual vanishing and separatedness.
(blueprint: lem-weil-pbc-etale-section-colimit-finite-zero-cover). -/
theorem etale_section_colimit_finite_zero_cover
    (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    (U : X.Etale) [CompactSpace U.left]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{max v w} Λ))
    (c : Cocone G) (hc : IsColimit c) (i : I)
    (s : (G.obj i).obj.obj (Opposite.op U))
    (hs : ((c.ι.app i).hom.app (Opposite.op U)).hom s = 0) :
    ∃ (K : Type w) (_ : Finite K) (V : K → X.Etale) (q : ∀ k, V k ⟶ U),
      (∀ k, ∃ (j : I) (f : i ⟶ j),
        ((G.map f).hom.app (Opposite.op (V k))).hom
          (((G.obj i).obj.map (q k).op).hom s) = 0) ∧
      (∀ (j : I) (t : (G.obj j).obj.obj (Opposite.op U)),
        (∀ k, ((G.obj j).obj.map (q k).op).hom t = 0) → t = 0) := by
  classical
  obtain ⟨S, hS, hzero⟩ :=
    etale_section_colimit_local_zero_sieve X Λ U I G c hc i s hs
  obtain ⟨n, V, q, hq, _, hcover⟩ :=
    (AlgebraicGeometry.Etale.exists_affine_refinement _) hS
  let K := ULift.{w} (Fin n)
  let V' (k : K) := V k.down
  let q' (k : K) : V' k ⟶ U := q k.down
  have hcover' : Sieve.ofArrows V' q' ∈ X.smallEtaleTopology U := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff q').2
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨k, y, rfl⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨⟨k⟩, y, rfl⟩
  refine ⟨K, inferInstance, V', q', fun k ↦ hzero _ _ (hq k.down), ?_⟩
  intro j t ht
  let L := ModuleCat.of Λ (ULift.{w} Λ)
  let e : L ⟶ (G.obj j).obj.obj (Opposite.op U) := ModuleCat.ofHom
    { toFun := fun a ↦ a.down • t
      map_add' := by intro a b; exact add_smul _ _ _
      map_smul' := by intro a b; exact mul_smul _ _ _ }
  have he : e = 0 := by
    apply (G.obj j).property.hom_ext_ofArrows q' hcover'
    intro k
    ext a
    simp only [ModuleCat.comp_apply]
    change ((G.obj j).obj.map (q' k).op).hom (a.down • t) =
      ((G.obj j).obj.map (q' k).op).hom 0
    rw [map_smul, ht k, smul_zero, map_zero]
  have h := congrArg (fun f : L ⟶ (G.obj j).obj.obj (Opposite.op U) ↦
    f.hom ⟨1⟩) he
  simpa [e] using h

end AlgebraicGeometry
