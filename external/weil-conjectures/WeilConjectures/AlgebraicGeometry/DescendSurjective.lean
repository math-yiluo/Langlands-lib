/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Surjectivity descends to a finite stage of an inverse limit

Source: Stacks Project, Limits, Lemma 07RR in Situation 081D
(blueprint: lem-weil-pbc-descend-surjective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A locally finitely presented morphism between quasi-compact, quasi-separated schemes
at a stage of an inverse system with affine transitions is surjective at some later stage
if its base change to the limit is surjective.

Source: Stacks Project, Limits, Lemma 07RR in Situation 081D
(blueprint: lem-weil-pbc-descend-surjective).

Proof:
1. Quasi-compactness of X₀ and quasi-separatedness of Y₀ make f₀ quasi-compact
   (lem-weil-pbc-qcqs-morphism-permanence). Chevalley's theorem gives the constructible
   image E = f₀(X₀) (lem-weil-pbc-chevalley-constructible-image,
   def-weil-constructible-subset).
2. For each base T → S₀, `Scheme.Pullback.range_map` computes the image of the
   pullback of f₀ directly as the inverse image of E under Y₀ × T → Y₀
   (def-pc-fibre-product, lem-weil-pbc-base-change-image).
3. Surjectivity over S therefore implies that Y → Y₀ maps into E
   (def-weil-surjective-morphism).
4. Replace the upper tail i ≥ i₀ by its equivalent category `Over (op i₀)`. The
   whiskered base-change diagram has limit Y and affine transitions
   (lem-weil-pbc-scheme-over-limit, def-weil-pbc-category-colimit). They are quasi-compact
   and quasi-separated by affine permanence and composition with Y₀
   (lem-weil-pbc-affine-morphism-permanence, lem-weil-pbc-qcqs-morphism-permanence).
5. Transport E along the initial upper-tail projection and apply
   lem-weil-pbc-limit-contained-in-constructible to obtain a stage i ≥ i₀ whose
   projection Yᵢ → Y₀ maps into E.
6. The pullback image formula then says that fᵢ is surjective
   (def-weil-surjective-morphism). -/
theorem exists_surjective_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (_hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    (_hf : Surjective (((Over.pullback (c.π.app (op i₀))).map f₀).left)) :
    ∃ (i : I) (hi : i₀ ≤ i),
      Surjective (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left) := by
  have hbaseChange {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
      (p : Y ⟶ D.obj (op i₀)) (E : Set Y) (hE : Topology.IsConstructible E)
      (himage : Set.range (pullback.fst p (c.π.app (op i₀))) ⊆ E) :
      ∃ (i : I) (hi : i₀ ≤ i),
        Set.range (pullback.fst p (D.map (homOfLE hi).op)) ⊆ E := by
    classical
    let : Nonempty I := ⟨i₀⟩
    let J := {i : I // i₀ ≤ i}
    let j₀ : J := ⟨i₀, le_rfl⟩
    let : Nonempty J := ⟨j₀⟩
    let : IsDirected J (· ≤ ·) := ⟨fun a b ↦ by
      obtain ⟨k, ha, hb⟩ := exists_ge_ge a.val b.val
      exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
    let F : Jᵒᵖ ⥤ Over (op i₀) :=
      { obj := fun j ↦ Over.mk (homOfLE j.unop.property).op
        map := fun f ↦ Over.homMk (homOfLE (leOfHom f.unop)).op (by subsingleton) }
    let : F.Faithful := ⟨fun _ ↦ Subsingleton.elim _ _⟩
    let : F.Full := ⟨fun {a b} f ↦
      ⟨(homOfLE (show b.unop ≤ a.unop from leOfHom f.left.unop)).op,
        by ext; apply Subsingleton.elim⟩⟩
    let : F.EssSurj := ⟨fun j ↦ by
      refine ⟨op (⟨j.left.unop, leOfHom j.hom.unop⟩ : J), ⟨?_⟩⟩
      exact Over.isoMk (Iso.refl _) (by subsingleton)⟩
    let : F.IsEquivalence := {}
    let B := F ⋙ baseChangeDiagram D p
    let bc := (baseChangeCone D c p).whisker F
    have hbc : IsLimit bc :=
      (Functor.Initial.isLimitWhiskerEquiv F _).symm (isLimitBaseChangeCone D c p _hc)
    let : ∀ j : Jᵒᵖ, CompactSpace (B.obj j) := fun j ↦ by
      change CompactSpace ((baseChangeDiagram D p).obj (F.obj j))
      infer_instance
    let : ∀ j : Jᵒᵖ, QuasiSeparatedSpace (B.obj j) := fun j ↦ by
      change QuasiSeparatedSpace ((baseChangeDiagram D p).obj (F.obj j))
      infer_instance
    let : ∀ {j k : Jᵒᵖ} (f : j ⟶ k), IsAffineHom (B.map f) := fun f ↦ by
      change IsAffineHom ((baseChangeDiagram D p).map (F.map f))
      infer_instance
    have hE' : Topology.IsConstructible
        ((pullback.fst p (D.map (F.obj (op j₀)).hom)) ⁻¹' E) :=
      (pullback.fst p (D.map (F.obj (op j₀)).hom)).isConstructible_preimage hE
    have himage' : Set.range (bc.π.app (op j₀)) ⊆
        ((pullback.fst p (D.map (F.obj (op j₀)).hom)) ⁻¹' E) := by
      rintro _ ⟨x, rfl⟩
      change pullback.fst p (D.map (F.obj (op j₀)).hom)
        ((baseChangeCone D c p).π.app (F.obj (op j₀)) x) ∈ E
      have heq := congrArg (fun f : bc.pt ⟶ Y ↦ f x)
        (baseChangeCone_π_app_fst D c p (F.obj (op j₀)))
      rw [Scheme.Hom.comp_apply] at heq
      exact heq.symm ▸ himage ⟨x, rfl⟩
    obtain ⟨j, hj, hstage⟩ := exists_eventually_range_subset_of_isConstructible
      B bc hbc j₀ _ hE' himage'
    refine ⟨j.val, j.property, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hx := hstage j le_rfl ⟨x, rfl⟩
    change pullback.fst p (D.map (F.obj (op j₀)).hom)
      ((baseChangeDiagram D p).map (F.map (homOfLE (hj.trans le_rfl)).op) x) ∈ E at hx
    have heq := congrArg
      (fun f : (B.obj (op j)) ⟶ Y ↦ f x)
      (baseChangeDiagram_map_fst D p (F.map (homOfLE (hj.trans le_rfl)).op))
    rw [Scheme.Hom.comp_apply] at heq
    exact heq ▸ hx
  have hE : Topology.IsConstructible (Set.range f₀.left) := by
    simpa using f₀.left.isConstructible_image Topology.IsConstructible.univ
  have hrange {T : Scheme.{u}} (g : T ⟶ D.obj (op i₀)) :
      Set.range (((Over.pullback g).map f₀).left) =
        (pullback.fst Y₀.hom g) ⁻¹' Set.range f₀.left := by
    have heq : (((Over.pullback g).map f₀).left) =
        pullback.map X₀.hom g Y₀.hom g f₀.left (𝟙 T) (𝟙 _)
          (by simp [Over.w f₀]) (by simp) := by
      apply pullback.hom_ext <;> simp
    rw [heq]
    simpa using (Scheme.Pullback.range_map (f := X₀.hom) (g := g)
      Y₀.hom g f₀.left (𝟙 T) (𝟙 _) (by simp [Over.w f₀]) (by simp))
  have himage : Set.range (pullback.fst Y₀.hom (c.π.app (op i₀))) ⊆
      Set.range f₀.left := by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ Set.range (((Over.pullback (c.π.app (op i₀))).map f₀).left) :=
      _hf.surj.range_eq ▸ Set.mem_univ y
    rw [hrange] at hy
    exact hy
  obtain ⟨i, hi, hstage⟩ := hbaseChange
    Y₀.hom (Set.range f₀.left) hE himage
  refine ⟨i, hi, ⟨?_⟩⟩
  intro y
  have hy : y ∈ Set.range (((Over.pullback (D.map (homOfLE hi).op)).map f₀).left) := by
    rw [hrange]
    exact hstage ⟨y, rfl⟩
  exact hy

end AlgebraicGeometry
