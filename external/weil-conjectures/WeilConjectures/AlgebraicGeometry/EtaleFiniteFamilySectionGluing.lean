/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective

import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover

/-! # Gluing étale sections on a finite disjoint union

Source: Stacks Project, Tag 09ZF, fourth proof paragraph, disjoint union of representatives.
(blueprint: lem-weil-pbc-etale-finite-family-section-gluing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Assemble finitely many representing sections into one surjective étale object.
Source: Stacks Project, Tag 09ZF, fourth proof paragraph, the disjoint union of U_j.
(blueprint: lem-weil-pbc-etale-finite-family-section-gluing).

Proof: Form the finite scheme coproduct of the underlying schemes of U_j and let
q be the map induced by their structure maps. Its coprojections are open immersions
and cover the coproduct. Thus q is étale by locality on the source; hcover makes
it surjective. The coprojections are an étale cover. Different components have
empty fibre product, and the self-intersections are the components themselves,
so the given s_j are compatible and glue uniquely to s in F(U). Base change
preserves this cover. On each base-changed component, unit naturality identifies
i⁻¹s with i⁻¹s_j, which equals the restriction of t by heq. Separatedness of the
inverse-image sheaf proves the asserted global equation. The finite coproduct
is a scheme in universe u. For empty J, hcover forces X empty; the empty-cover
sheaf axiom gives the unique s and the unique equality after base change.
No closed-immersion, compactness, or Zariski-unit hypothesis is needed. -/
theorem etale_finite_family_section_gluing
    {X Z : Scheme.{u}} (i : Z ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X)))))
    {J : Type u} [Finite J] (U : J → X.Etale)
    (s : ∀ j, F.obj.obj (op (U j)))
    (hcover : (Set.univ : Set X) ⊆ ⋃ j, Set.range (U j).hom)
    (heq : ∀ j, etaleSetDescentUnit i F (U j) (s j) =
        ((Scheme.etaleSetPullback i).obj F).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ i).map
            (MorphismProperty.Over.homMk (U j).hom (Category.comp_id _) :
              U j ⟶ Scheme.Etale.mk (𝟙 X))).op t) :
    ∃ (U : Scheme.{u}) (q : U ⟶ X) (_ : Etale q) (_ : Surjective q)
      (s : F.obj.obj (op (Scheme.Etale.mk q))),
      etaleSetDescentUnit i F (Scheme.Etale.mk q) s =
        ((Scheme.etaleSetPullback i).obj F).obj.map
          ((MorphismProperty.Over.pullback @Etale ⊤ i).map
            (MorphismProperty.Over.homMk q (Category.comp_id q) :
              Scheme.Etale.mk q ⟶ Scheme.Etale.mk (𝟙 X))).op t := by
  classical
  let V : J → Scheme.{u} := fun j ↦ (U j).left
  let q : (∐ V) ⟶ X := Sigma.desc (fun j ↦ (U j).hom)
  have hq : Etale q := by
    apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Etale)
      (𝒰 := sigmaOpenCover V)).mpr
    intro j
    change Etale (Sigma.ι V j ≫ q)
    dsimp [q]
    rw [Sigma.ι_comp_desc]
    exact (U j).prop
  have hs : Surjective q := ⟨by
    intro x
    obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ x))
    refine ⟨Sigma.ι V j y, ?_⟩
    change (Sigma.ι V j ≫ q) y = x
    rw [show Sigma.ι V j ≫ q = (U j).hom from Sigma.ι_comp_desc _ _]
    exact hy⟩
  let π : ∀ j, U j ⟶ Scheme.Etale.mk q := fun j ↦
    MorphismProperty.Over.homMk (Sigma.ι V j) (by simp [q])
  have hm : ∀ j, Mono (π j) := by
    intro j
    apply (Scheme.Etale.forget X ⋙ Over.forget X).mono_of_mono_map
    change Mono (Sigma.ι V j)
    infer_instance
  have hc : Sieve.ofArrows U π ∈ X.smallEtaleTopology (Scheme.Etale.mk q) := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨⟨j, y⟩, hy⟩ := (sigmaMk V).surjective x
    exact ⟨j, y, (sigmaMk_mk V j y).symm.trans hy⟩
  have hd : ∀ j k, j ≠ k →
      Disjoint (Set.range (π j).left.base) (Set.range (π k).left.base) := by
    intro j k hjk
    exact Set.disjoint_left.mpr (fun x hxj hxk ↦
      (disjoint_iff.mp (disjoint_opensRange_sigmaι V j k hjk)).le ⟨hxj, hxk⟩)
  obtain ⟨a, ha, _⟩ := F.property.existsUnique_amalgamation_ofArrows π hc
    (fun j ↦ TypeCat.ofHom (fun _ : PUnit ↦ s j))
    (Scheme.Etale.comp_map_eq_of_disjoint F U π hd _)
  let sec : F.obj.obj (op (Scheme.Etale.mk q)) := a PUnit.unit
  have hsection : ∀ j, F.obj.map (π j).op sec = s j := by
    intro j
    exact ConcreteCategory.congr_hom (ha j) PUnit.unit
  refine ⟨∐ V, q, hq, hs, sec, ?_⟩
  let B := MorphismProperty.Over.pullback @Etale ⊤ i
  let H := (Scheme.etaleSetPullback i).obj F
  have hbc : Sieve.ofArrows (fun j ↦ B.obj (U j)) (fun j ↦ B.map (π j)) ∈
      Z.smallEtaleTopology (B.obj (Scheme.Etale.mk q)) := by
    simpa only [Scheme.Hom.Etale, Sieve.functorPushforward_ofArrows] using
      (Scheme.Hom.coverPreserving_etale i).cover_preserve hc
  have hhom :
      TypeCat.ofHom (fun _ : PUnit.{u + 2} ↦ etaleSetDescentUnit i F (Scheme.Etale.mk q) sec) =
      TypeCat.ofHom (fun _ : PUnit.{u + 2} ↦ H.obj.map
        (B.map (MorphismProperty.Over.homMk q (Category.comp_id q) :
          Scheme.Etale.mk q ⟶ Scheme.Etale.mk (𝟙 X))).op t) := by
    apply H.property.hom_ext_ofArrows (fun j ↦ B.map (π j)) hbc
    intro j
    ext x
    have hn := etaleSetInverseImageCompositionUnits.1 X Z i F
      (Scheme.Etale.mk q) (U j) (π j) sec
    change etaleSetDescentUnit i F (U j) (F.obj.map (π j).op sec) =
      H.obj.map (B.map (π j)).op (etaleSetDescentUnit i F (Scheme.Etale.mk q) sec) at hn
    change H.obj.map (B.map (π j)).op (etaleSetDescentUnit i F (Scheme.Etale.mk q) sec) =
      H.obj.map (B.map (π j)).op (H.obj.map
        (B.map (MorphismProperty.Over.homMk q (Category.comp_id q) :
          Scheme.Etale.mk q ⟶ Scheme.Etale.mk (𝟙 X))).op t)
    rw [← hn, hsection, heq]
    rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp]
    have hcomp : π j ≫ (MorphismProperty.Over.homMk q (Category.comp_id q) :
        Scheme.Etale.mk q ⟶ Scheme.Etale.mk (𝟙 X)) =
        (MorphismProperty.Over.homMk (U j).hom (Category.comp_id _) :
          U j ⟶ Scheme.Etale.mk (𝟙 X)) := by
      apply (Scheme.Etale.forget X ⋙ Over.forget X).map_injective
      change (π j).left ≫ q = (U j).hom
      exact MorphismProperty.Over.w (π j)
    rw [hcomp]
  exact ConcreteCategory.congr_hom hhom PUnit.unit

end AlgebraicGeometry
