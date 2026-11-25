/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.EtaleAffineChartDescent
import Mathlib.Data.Finset.Order

/-!
# Descent of étaleness to a stage of an inverse limit

Source: Stacks Project, Limits, Lemma 07RP in Situation 081D
(blueprint: lem-weil-pbc-descend-etale).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A locally finitely presented morphism over a quasi-compact quasi-separated stage,
whose source and target are quasi-compact quasi-separated, is étale at some later stage
if its base change to the inverse limit is étale.

Source: Stacks Project, Limits, Lemma 07RP in Situation 081D
(blueprint: lem-weil-pbc-descend-etale).

Proof:
1. Cover X₀ by finitely many affine opens U mapping into affine opens V of Y₀,
   themselves mapping into affine opens W of S₀. Local finite presentation makes the
   maps of their coordinate rings finitely presented
   (lem-weil-pbc-affine-open-spec-points, lem-weil-pbc-morphism-into-affine-scheme,
   lem-weil-pbc-lfp-affine-opens-finite-presentation, definition-ind-etale-pro-etale-weakly--3).
2. The inverse images Wᵢ are affine by pqf-def-affine-morphism. Their coordinate rings
   have colimit A, and the inverse image of W in the limit is Spec A, compatibly with
   projections (lem-weil-pbc-limit-affine-transition, lem-weil-pbc-spec-colimit-limit,
   def-weil-pbc-category-colimit, lem-weil-pbc-morphism-into-affine-scheme).
3. The corresponding pieces of the base changes of X₀ and Y₀ are spectra of tensor
   products. The restricted morphism is induced by the tensor product of the original
   ring map, as checked on both projections (def-pc-fibre-product,
   lem-weil-pbc-open-fibre-product, lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-colimit-etale-ring-map). The source pieces cover every stage.
4. Restrict the étale limit morphism to these opens and transport across the affine
   identifications (definition-torsion-sheaves--3).
5. Apply lem-weil-pbc-colimit-etale-ring-map to each affine triple. Étaleness persists
   at larger indices by tensor cancellation and étale base change
   (lem-weil-pbc-tensor-cancel-base-change, lem-weil-pbc-etale-ring-base-change,
   definition-torsion-sheaves--3).
6. Directedness gives a common upper bound of the finitely many indices and i₀.
   At this stage the restrictions are étale; their source opens cover, so the entire
   morphism is étale (lem-weil-pbc-etale-local-on-source,
   definition-torsion-sheaves--3). -/
theorem Etale.exists_stage_of_inverseLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFinitePresentation f₀.left]
    (hf : Etale (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (h : i₀ ≤ i),
      Etale (((Over.pullback (D.map (homOfLE h).op)).map f₀).left) := by
  classical
  have local_chart (x : X₀.left) :
      ∃ (U : X₀.left.Opens), x ∈ U ∧
        ∃ (i : I) (_ : i₀ ≤ i), ∀ (j : I) (_ : i ≤ j) (hj : i₀ ≤ j),
          Etale (((pullback.fst X₀.hom (D.map (homOfLE hj).op)) ⁻¹ᵁ U).ι ≫
            ((Over.pullback (D.map (homOfLE hj).op)).map f₀).left) := by
    obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := D.obj (op i₀)) (x := Y₀.hom (f₀.left x)) (U := ⊤) (by simp)
    obtain ⟨V, hV, hxV, eV⟩ := exists_isAffineOpen_mem_and_subset
      (X := Y₀.left) (x := f₀.left x) (U := Y₀.hom ⁻¹ᵁ W) hxW
    obtain ⟨U, hU, hxU, eU⟩ := exists_isAffineOpen_mem_and_subset
      (X := X₀.left) (x := x) (U := f₀.left ⁻¹ᵁ V) hxV
    refine ⟨U, hxU, Etale.exists_stage_on_affine_chart D c hc i₀ X₀ Y₀ f₀
      W hW V hV eV U hU eU ?_⟩
    have := hf
    infer_instance
  choose U hxU k hk hstage using local_chart
  have hcover : (Set.univ : Set X₀.left) ⊆ ⋃ x, (U x : Set X₀.left) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (U x : Set X₀.left)) (fun x ↦ (U x).isOpen) hcover
  have : Nonempty I := ⟨i₀⟩
  obtain ⟨i, hi⟩ := (insert i₀ (s.image k)).exists_le
  have hi₀ : i₀ ≤ i := hi i₀ (Finset.mem_insert_self _ _)
  refine ⟨i, hi₀, ?_⟩
  let q := D.map (homOfLE hi₀).op
  have hU : (⨆ x : s, U x) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale)
    (fun x : s ↦ (pullback.fst X₀.hom q) ⁻¹ᵁ U x)
    ((pullback.fst X₀.hom q).iSup_preimage_eq_top hU)
  intro x
  exact hstage x i (hi (k x) (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨x, x.property, rfl⟩))) hi₀

end AlgebraicGeometry
