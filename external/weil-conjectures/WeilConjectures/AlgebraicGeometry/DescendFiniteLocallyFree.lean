/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.DescendFinite
import all WeilConjectures.AlgebraicGeometry.DescendClosedImmersion
import all WeilConjectures.AlgebraicGeometry.DescendFiniteAffineOpen
import WeilConjectures.AlgebraicGeometry.DescendFlatFinitePresentation
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descent of finite locally free morphisms

Source: Stacks Project, Limits, Lemma Tag 06AC, in Situation Tag 081D
(blueprint: lem-weil-pbc-descend-finite-locally-free).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem over_pullback_comparison_square {S T R : Scheme.{u}}
    (X Y : Over S) (f : X ⟶ Y) (q : T ⟶ S) (r : R ⟶ S)
    (x : pullback X.hom r ⟶ pullback X.hom q)
    (y : pullback Y.hom r ⟶ pullback Y.hom q)
    (hx : x ≫ pullback.fst X.hom q = pullback.fst X.hom r)
    (hy : y ≫ pullback.fst Y.hom q = pullback.fst Y.hom r)
    (hcomm : x ≫ ((Over.pullback q).map f).left =
      ((Over.pullback r).map f).left ≫ y) :
    IsPullback x ((Over.pullback r).map f).left ((Over.pullback q).map f).left y := by
  apply IsPullback.of_right (t := over_pullback_square X Y f q) _ hcomm
  simpa only [hx, hy] using over_pullback_square X Y f r

/-- Finite locally freeness, and its degree, descend to a finite stage of an inverse limit
of schemes with affine transition morphisms.

Source: Stacks Project, Limits, Lemma Tag 06AC, in Situation Tag 081D
(blueprint: lem-weil-pbc-descend-finite-locally-free).

Proof:
1. Locally finite presentation implies locally finite type by the finite generators in an
   affine presentation (def-sbc-locally-finite-presentation, def-weil-finite-type-morphism).
   Finite local freeness gives finiteness and flatness (def-pc-finite-locally-free).
   Descend these separately (lem-weil-pbc-descend-finite,
   lem-weil-pbc-descend-flat-finite-presentation), then choose a common later stage.
   Cartesian-square pasting identifies the maps there as base changes; finiteness,
   flatness and locally finite presentation persist (lem-weil-pbc-cartesian-square-pasting,
   lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-flat-morphism-base-change,
   lem-weil-pbc-qcqs-morphism-permanence). Thus that stage is finite locally free.
2. If the limit map has degree d, take the clopen degree-d locus W in the stage target
   (lem-weil-pbc-finite-locally-free-degree-locally-constant). Rank base change and pasting
   show that the limit target maps into W (lem-weil-pbc-finite-flat-rank-iso,
   lem-weil-pbc-cartesian-square-pasting).
3. The limit target is the limit of the base-changed targets (lem-weil-pbc-scheme-over-limit).
   Their affine transitions and the qcqs initial target make them qcqs
   (lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-qcqs-morphism-permanence).
   The clopen W is retrocompact, hence constructible (def-weil-constructible-subset).
   A later target therefore maps into W (lem-weil-pbc-limit-contained-in-constructible).
4. At that later stage finite local freeness persists by the same base-change permanence
   and pasting as in Step 1. Rank base change identifies every fibre degree with the degree
   at its image in W, which is d (lem-weil-pbc-finite-flat-rank-iso).
   This is finite local freeness of degree d (def-pc-finite-locally-free).
-/
theorem descend_finite_locally_free
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    (hf : Scheme.Hom.IsFiniteLocallyFree (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    (∃ (i : I) (hi : i₀ ≤ i),
      Scheme.Hom.IsFiniteLocallyFree (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left)) ∧
    (∀ d : ℕ,
      Scheme.Hom.IsFiniteLocallyFreeOfDegree
          (((Over.pullback (c.π.app (op i₀))).map f₀).left) d →
        ∃ (i : I) (hi : i₀ ≤ i),
          Scheme.Hom.IsFiniteLocallyFreeOfDegree
            (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left) d) := by
  classical
  have : (((Over.pullback (c.π.app (op i₀))).map f₀).left).IsFiniteLocallyFree := hf
  obtain ⟨a, ha, hfa⟩ := exists_isFinite_baseChange_stage D c hc i₀ X₀ Y₀ f₀
    (inferInstance : IsFinite (((Over.pullback (c.π.app (op i₀))).map f₀).left))
  obtain ⟨b, hb, hfb⟩ := exists_flat_stage_of_limit D c hc i₀ X₀ Y₀ f₀
    (inferInstance : Flat (((Over.pullback (c.π.app (op i₀))).map f₀).left))
  obtain ⟨i, hai, hbi⟩ := exists_ge_ge a b
  have hcomp (j k : I) (hj : i₀ ≤ j) (hjk : j ≤ k) :
      D.map (homOfLE hjk).op ≫ D.map (homOfLE hj).op =
        D.map (homOfLE (hj.trans hjk)).op := by
    rw [← D.map_comp]
    congr 1
  have hfi : IsFinite (((Over.pullback (D.map (homOfLE (ha.trans hai)).op)).map f₀).left) := by
    rw [← hcomp a i ha hai]
    exact property_overPullback_comp (@IsFinite) _ _ f₀ hfa
  have hfli : Flat (((Over.pullback (D.map (homOfLE (ha.trans hai)).op)).map f₀).left) := by
    rw [show ha.trans hai = hb.trans hbi from Subsingleton.elim _ _]
    rw [← hcomp b i hb hbi]
    exact property_overPullback_comp (@Flat) _ _ f₀ hfb
  have hfpi : LocallyOfFinitePresentation
      (((Over.pullback (D.map (homOfLE (ha.trans hai)).op)).map f₀).left) :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) _ f₀ inferInstance
  have hfree : Scheme.Hom.IsFiniteLocallyFree
      (((Over.pullback (D.map (homOfLE (ha.trans hai)).op)).map f₀).left) := ⟨⟩
  refine ⟨⟨i, ha.trans hai, hfree⟩, ?_⟩
  intro d hd
  have : (((Over.pullback (c.π.app (op i₀))).map f₀).left).IsFiniteLocallyFreeOfDegree d := hd
  have : Nonempty I := ⟨i₀⟩
  let J := {j : I // i₀ ≤ j}
  let ji : J := ⟨i, ha.trans hai⟩
  have : Nonempty J := ⟨ji⟩
  have : IsDirected J (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨k, hka, hkb⟩ := exists_ge_ge a.val b.val
    exact ⟨⟨k, a.property.trans hka⟩, hka, hkb⟩⟩
  let F : Jᵒᵖ ⥤ Over (op i₀) :=
    { obj := fun j ↦ Over.mk (homOfLE j.unop.property).op
      map := fun f ↦ Over.homMk (homOfLE (leOfHom f.unop)).op (by subsingleton) }
  have : F.Faithful := ⟨fun _ ↦ Subsingleton.elim _ _⟩
  have : F.Full := ⟨fun {a b} f ↦
    ⟨(homOfLE (show b.unop ≤ a.unop from leOfHom f.left.unop)).op,
      by ext; apply Subsingleton.elim⟩⟩
  have : F.EssSurj := ⟨fun j ↦ by
    refine ⟨op (⟨j.left.unop, leOfHom j.hom.unop⟩ : J), ⟨?_⟩⟩
    exact Over.isoMk (Iso.refl _) (by subsingleton)⟩
  have : F.IsEquivalence := {}
  let B := F ⋙ baseChangeDiagram D Y₀.hom
  let A := F ⋙ baseChangeDiagram D X₀.hom
  let bc := (baseChangeCone D c Y₀.hom).whisker F
  let ac := (baseChangeCone D c X₀.hom).whisker F
  have hbc : IsLimit bc :=
    (Functor.Initial.isLimitWhiskerEquiv F _).symm (isLimitBaseChangeCone D c Y₀.hom hc)
  have : ∀ j : Jᵒᵖ, CompactSpace (B.obj j) := fun j ↦ by
    change CompactSpace ((baseChangeDiagram D Y₀.hom).obj (F.obj j))
    infer_instance
  have : ∀ j : Jᵒᵖ, QuasiSeparatedSpace (B.obj j) := fun j ↦ by
    change QuasiSeparatedSpace ((baseChangeDiagram D Y₀.hom).obj (F.obj j))
    infer_instance
  have : ∀ {j k : Jᵒᵖ} (f : j ⟶ k), IsAffineHom (B.map f) := fun f ↦ by
    change IsAffineHom ((baseChangeDiagram D Y₀.hom).map (F.map f))
    infer_instance
  let fstage (j : J) := ((Over.pullback (D.map (homOfLE j.property).op)).map f₀).left
  let flim := ((Over.pullback (c.π.app (op i₀))).map f₀).left
  have hflim : IsAffineHom flim := inferInstance
  have hfreei : (fstage ji).IsFiniteLocallyFree := hfree
  have hlimsq : IsPullback (ac.π.app (op ji)) flim (fstage ji) (bc.π.app (op ji)) := by
    apply over_pullback_comparison_square X₀ Y₀ f₀ _ _
    · exact baseChangeCone_π_app_fst D c X₀.hom (F.obj (op ji))
    · exact baseChangeCone_π_app_fst D c Y₀.hom (F.obj (op ji))
    · apply pullback.hom_ext <;>
        simp [ac, bc, F, baseChangeCone, Over.pullback_map_left]
  have hsquare (j : J) (hij : ji ≤ j) :
      IsPullback (A.map (homOfLE hij).op) (fstage j) (fstage ji)
        (B.map (homOfLE hij).op) := by
    apply over_pullback_comparison_square X₀ Y₀ f₀ _ _
    · exact baseChangeDiagram_map_fst D X₀.hom (F.map (homOfLE hij).op)
    · exact baseChangeDiagram_map_fst D Y₀.hom (F.map (homOfLE hij).op)
    · apply pullback.hom_ext <;>
        simp [A, B, F, baseChangeDiagram, Over.pullback_map_left]
  let E : Set (B.obj (op ji)) := (fstage ji).fiberDegree ⁻¹' {d}
  have hclopen : IsClopen E := by
    exact (finiteLocallyFree_fiberDimension_isLocallyConstant (fstage ji)).2.2.1 d
  have hE : Topology.IsConstructible E :=
    hclopen.1.isCompact.isConstructible hclopen.2
  have himage : Set.range (bc.π.app (op ji)) ⊆ E := by
    rintro _ ⟨y, rfl⟩
    change (fstage ji).fiberDegree ((bc.π.app (op ji)) y) = d
    exact (Scheme.Hom.fiberDegree_of_isPullback (fstage ji) hlimsq y).symm.trans
      (hd.fiberDegree_eq y)
  obtain ⟨j, hij, hstage⟩ := exists_eventually_range_subset_of_isConstructible
    B bc hbc ji E hE himage
  have hfinitej : IsFinite (fstage j) :=
    MorphismProperty.of_isPullback (P := @IsFinite) (hsquare j hij) inferInstance
  have hflatj : Flat (fstage j) :=
    MorphismProperty.of_isPullback (P := @Flat) (hsquare j hij) inferInstance
  have hfpj : LocallyOfFinitePresentation (fstage j) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (hsquare j hij)
      inferInstance
  have hfreej : (fstage j).IsFiniteLocallyFree := ⟨⟩
  refine ⟨j.val, j.property, ⟨?_⟩⟩
  intro y
  exact (Scheme.Hom.fiberDegree_of_isPullback (fstage ji) (hsquare j hij) y).trans
    (hstage j le_rfl ⟨y, rfl⟩)

end AlgebraicGeometry
