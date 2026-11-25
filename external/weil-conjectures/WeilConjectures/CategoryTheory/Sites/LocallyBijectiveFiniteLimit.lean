/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Finite limits of locally bijective abelian presheaf maps

Source: Stacks Project, Tags 00WJ and 03CN.
(blueprint: lem-sc-locally-bijective-finite-limit) -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Presheaf

private theorem common_cover
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {X : C} {ι : Type*} [Finite ι] (s : ι → Sieve X) (hs : ∀ i, s i ∈ J X) :
    ∃ S : Sieve X, S ∈ J X ∧ ∀ i, S ≤ s i := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have h : ∀ t : Finset ι, ∃ S : Sieve X, S ∈ J X ∧ ∀ i ∈ t, S ≤ s i := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨⊤, J.top_mem X, by simp⟩
    | @insert a t ha ih =>
      obtain ⟨S, hS, hle⟩ := ih
      refine ⟨s a ⊓ S, J.intersection_covering (hs a) hS, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact inf_le_left
      · exact inf_le_right.trans (hle i hi)
  obtain ⟨S, hS, hle⟩ := h Finset.univ
  exact ⟨S, hS, fun i ↦ hle i (Finset.mem_univ i)⟩

private theorem section_ext
    {C : Type u} [Category.{v} C] {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w})) (X : Cᵒᵖ)
    (x y : (limit F).obj X)
    (h : ∀ k, (limit.π F k).app X x = (limit.π F k).app X y) : x = y :=
  Concrete.isLimit_ext (F ⋙ (evaluation Cᵒᵖ AddCommGrpCat).obj X)
    (isLimitOfPreserves ((evaluation Cᵒᵖ AddCommGrpCat).obj X) (limit.isLimit F)) x y h

private theorem section_exists
    {C : Type u} [Category.{v} C] {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w})) (X : Cᵒᵖ)
    (s : ∀ k, (F.obj k).obj X)
    (h : ∀ (i j : K) (f : i ⟶ j), (F.map f).app X (s i) = s j) :
    ∃ t : (limit F).obj X, ∀ k, (limit.π F k).app X t = s k := by
  let E := (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj X ⋙ forget AddCommGrpCat.{w}
  let hl := isLimitOfPreserves E (limit.isLimit F)
  let s' : (F ⋙ E).sections := ⟨s, fun {i j} f ↦ h i j f⟩
  refine ⟨(Types.isLimitEquivSections hl).symm s', ?_⟩
  intro k
  simpa [E, s'] using Types.isLimitEquivSections_symm_apply hl s' k

/-- Finite limits of componentwise locally bijective morphisms of abelian
presheaves are locally bijective.

Source: Stacks Project, Tag 00WJ, finite-limit refinement argument, and Tag 03CN.
(blueprint: lem-sc-locally-bijective-finite-limit)

Proof: limits are computed sectionwise. For local injectivity, project two
sections to every component and intersect the finitely many covering equality
sieves supplied by local injectivity. The limit projections jointly detect
equality on this covering. For local surjectivity, intersect the image sieves
of all components of a target section. On any arrow of this covering choose
component lifts. For each diagram arrow, naturality and compatibility of the
target section show that the corresponding two source components have equal
images. Local injectivity gives a covering equality sieve for this equation.
Intersect these sieves for the finitely many diagram arrows. On this refinement
the lifts are compatible and hence give a section of the source limit. Its image
is the restricted target section by joint injectivity of limit projections.
Transitivity of coverings gives local surjectivity on the original object.
For an empty diagram both limits are terminal and the comparison is invertible. -/
theorem locallyBijective_limMap
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {K : Type} [SmallCategory K] [FinCategory K]
    {F G : K ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w})} (α : F ⟶ G)
    [∀ k, IsLocallyInjective J (α.app k)]
    [∀ k, IsLocallySurjective J (α.app k)] :
    IsLocallyInjective J (limMap α) ∧ IsLocallySurjective J (limMap α) := by
  classical
  constructor
  · constructor
    intro X x y hxy
    have hcomp (k : K) :
        (α.app k).app X ((limit.π F k).app X x) =
          (α.app k).app X ((limit.π F k).app X y) := by
      have e := congrArg (fun t ↦ (limit.π G k).app X t) hxy
      simpa only [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, limMap_π] using e
    obtain ⟨S, hS, hle⟩ := common_cover J
      (fun k ↦ equalizerSieve ((limit.π F k).app X x) ((limit.π F k).app X y))
      (fun k ↦ equalizerSieve_mem J (α.app k) _ _ (hcomp k))
    apply J.superset_covering _ hS
    intro Y f hf
    apply section_ext F (Opposite.op Y)
    intro k
    simpa only [equalizerSieve_apply, NatTrans.naturality_apply] using hle k f hf
  · constructor
    intro U s
    let y (k : K) := (limit.π G k).app (Opposite.op U) s
    obtain ⟨S, hS, hle⟩ := common_cover J
      (fun k ↦ imageSieve (α.app k) (y k))
      (fun k ↦ imageSieve_mem J (α.app k) (y k))
    apply J.transitive hS (imageSieve (limMap α) s)
    intro V f hf
    let t (k : K) := localPreimage (α.app k) (y k) f (hle k f hf)
    have ht (k : K) : (α.app k).app (Opposite.op V) (t k) =
        (G.obj k).map f.op (y k) := app_localPreimage _ _ _ _
    have hcompat (i j : K) (d : i ⟶ j) :
        (α.app j).app (Opposite.op V) ((F.map d).app (Opposite.op V) (t i)) =
          (α.app j).app (Opposite.op V) (t j) := by
      calc
        _ = (G.map d).app (Opposite.op V) ((α.app i).app (Opposite.op V) (t i)) := by
          simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using
            congrArg (fun e ↦ e.app (Opposite.op V) (t i)) (α.naturality d)
        _ = (G.map d).app (Opposite.op V) ((G.obj i).map f.op (y i)) := by rw [ht]
        _ = (G.obj j).map f.op ((G.map d).app (Opposite.op U) (y i)) :=
          NatTrans.naturality_apply (G.map d) f.op (y i)
        _ = (G.obj j).map f.op (y j) := by
          congr 1
          simpa only [y, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app] using
            congrArg (fun e ↦ e.app (Opposite.op U) s) (limit.w G d)
        _ = _ := (ht j).symm
    let eqs (a : Σ i : K, Σ j : K, i ⟶ j) :=
      equalizerSieve ((F.map a.2.2).app (Opposite.op V) (t a.1)) (t a.2.1)
    obtain ⟨T, hT, hTle⟩ := common_cover J eqs
      (fun a ↦ equalizerSieve_mem J (α.app a.2.1) _ _ (hcompat _ _ a.2.2))
    apply J.superset_covering _ hT
    intro W g hg
    let z (k : K) := (F.obj k).map g.op (t k)
    have hz (i j : K) (d : i ⟶ j) :
        (F.map d).app (Opposite.op W) (z i) = z j := by
      have heq := hTle ⟨i, j, d⟩ g hg
      change (F.obj j).map g.op ((F.map d).app (Opposite.op V) (t i)) =
        (F.obj j).map g.op (t j) at heq
      exact (NatTrans.naturality_apply (F.map d) g.op (t i)).trans heq
    obtain ⟨r, hr⟩ := section_exists F (Opposite.op W) z hz
    refine ⟨r, ?_⟩
    apply section_ext G (Opposite.op W)
    intro k
    have hm := congrArg (fun e ↦ e.app (Opposite.op W) r) (limMap_π α k)
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hm
    rw [hm, hr]
    dsimp [z]
    rw [NatTrans.naturality_apply, ht]
    simp only [y, NatTrans.naturality_apply, Functor.map_comp_apply]

end CategoryTheory.Presheaf
