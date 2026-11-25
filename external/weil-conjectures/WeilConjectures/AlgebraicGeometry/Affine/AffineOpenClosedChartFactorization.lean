/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QcqsOpenClosedTree.Path.QcqsOpenClosedTree
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import all WeilConjectures.SixFunctors.ConstructibleOpenClosedRefinement
import WeilConjectures.SixFunctors.SchemeRefinementTree
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Geometric factorization of stratified pro-etale charts

Source: Stacks Tags 09C3 and 09Y4, finite affine cover and base-change argument.
(blueprint: lem-sf-affine-open-closed-chart-factorization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open Topology AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/- The generic partition construction below is reused from AffineResidueLisseTree.
Keeping its geometric proof here avoids importing that arithmetic module and its
coefficient-model dependencies. -/
private theorem forgetRefinementTree {W T : Scheme.{u}} {t : T ⟶ W}
    {allowed : ∀ (Y : Scheme.{u}), (Y ⟶ W) → ∀ (A B : Scheme.{u}),
      (A ⟶ Y) → (B ⟶ Y) → Prop}
    {P : ∀ (Y : Scheme.{u}), (Y ⟶ W) → Prop}
    (tree : SchemeRefinementTree W allowed T t) (htree : tree.AllLeaves P) :
    ∃ q : QcqsOpenClosedTree T,
      ∀ (S : Scheme.{u}) (p : q.Path S), p.IsLeaf → P S (p.toRoot ≫ t) := by
  induction tree with
  | tip t hc hq hi =>
    let := hc
    let := hq
    refine ⟨.leaf _, ?_⟩
    intro S p hp
    cases p with
    | root => simpa only [SchemeRefinementTree.AllLeaves,
        QcqsOpenClosedTree.Path.toRoot, Category.id_comp] using htree
  | @node T A B t j i hc hq hi hj hi' hjqc hiqc hcov hdis ha a b iha ihb =>
    let := hc
    let := hq
    let := hj
    let := hi'
    let := hjqc
    let := hiqc
    obtain ⟨qa, hqa⟩ := iha htree.1
    obtain ⟨qb, hqb⟩ := ihb htree.2
    have hcomp : Set.range j.base = (Set.range i.base)ᶜ := by
      ext x
      constructor
      · intro hx hx'
        exact Set.disjoint_left.mp hdis hx hx'
      · intro hx
        have hx' : x ∈ Set.range j.base ∪ Set.range i.base := by rw [hcov]; trivial
        exact hx'.resolve_right hx
    refine ⟨.split j i hcomp qa qb, ?_⟩
    intro S p hp
    cases p with
    | root => exact hp.elim
    | openBranch _ _ _ _ _ p =>
      simpa only [QcqsOpenClosedTree.Path.toRoot, Category.assoc] using hqa S p hp
    | closedBranch _ _ _ _ _ p =>
      simpa only [QcqsOpenClosedTree.Path.toRoot, Category.assoc] using hqb S p hp

private theorem partitionTree
    {W : Scheme.{u}} [CompactSpace W] [QuasiSeparatedSpace W]
    (m : ℕ) (n : Fin m → ℕ)
    (S : ∀ a : Fin m, Fin (n a) → Scheme.{u})
    (s : ∀ (a : Fin m) (j : Fin (n a)), S a j ⟶ W)
    (hs : ∀ a j, IsImmersion (s a j))
    (hc : ∀ a j, Topology.IsConstructible (Set.range (s a j).base))
    (hcover : ∀ a : Fin m, (⋃ j, Set.range (s a j).base) = Set.univ) :
    ∃ tree : QcqsOpenClosedTree W,
      ∀ (T : Scheme.{u}) (p : tree.Path T), p.IsLeaf → Nonempty T →
        ∀ a : Fin m, ∃ j : Fin (n a), ∃ f : T ⟶ S a j,
          f ≫ s a j = p.toRoot := by
  classical
  choose O Q Z o c q z ho hclosed hq hz hco hoqc hqqc hqr hzr using
    fun (a : Fin m) (j : Fin (n a)) ↦
      exists_constructible_cut (W := W) (S := S a j) (s a j) (hc a j)
  let allowed := fun (T : Scheme.{u}) (_ : T ⟶ W) (L R : Scheme.{u})
      (_ : L ⟶ T) (_ : R ⟶ T) ↦ True
  let resolved := fun (k : (a : Fin m) × Fin (n a)) (T : Scheme.{u}) (t : T ⟶ W) ↦
    Disjoint (Set.range t.base) (Set.range (s k.1 k.2).base) ∨
      ∃ f : T ⟶ S k.1 k.2, f ≫ s k.1 k.2 = t
  have resolved_comp (k : (a : Fin m) × Fin (n a))
      {T R : Scheme.{u}} (t : T ⟶ W) (r : R ⟶ T)
      (ht : resolved k T t) : resolved k R (r ≫ t) := by
    rcases ht with ht | ⟨f, hf⟩
    · left
      apply Set.disjoint_left.mpr
      rintro x ⟨y, rfl⟩ hx
      exact Set.disjoint_left.mp ht ⟨r y, rfl⟩ hx
    · exact Or.inr ⟨r ≫ f, by rw [Category.assoc, hf]⟩
  have step (k : (a : Fin m) × Fin (n a)) (T : Scheme.{u}) (t : T ⟶ W)
      (hcompact : CompactSpace T) (hqs : QuasiSeparatedSpace T) (himm : IsImmersion t) :
      ∃ tree : SchemeRefinementTree W allowed T t,
        tree.AllLeaves (fun R r ↦
          (∃ p : R ⟶ T, p ≫ t = r) ∧ resolved k R r) := by
    let :=  hcompact
    let :=  hqs
    let :=  himm
    let a := k.1
    let j := k.2
    have :=  ho a j
    have :=  hclosed a j
    have :=  hq a j
    have :=  hz a j
    have :=  hoqc a j
    have :=  hqqc a j
    let A := pullback t (o a j)
    let D := pullback t (z a j)
    let p : A ⟶ T := pullback.fst t (o a j)
    let d : D ⟶ T := pullback.fst t (z a j)
    let f : A ⟶ O a j := pullback.snd t (o a j)
    let B := pullback f (q a j)
    let C := pullback f (c a j)
    let b : B ⟶ A := pullback.fst f (q a j)
    let c' : C ⟶ A := pullback.fst f (c a j)
    have : CompactSpace A := inferInstance
    have : CompactSpace D := inferInstance
    have : QuasiSeparatedSpace A := quasiSeparatedSpace_of_quasiSeparated p
    have : QuasiSeparatedSpace D := quasiSeparatedSpace_of_quasiSeparated d
    have : CompactSpace B := inferInstance
    have : CompactSpace C := inferInstance
    have : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated b
    have : QuasiSeparatedSpace C := quasiSeparatedSpace_of_quasiSeparated c'
    have hfc : f ≫ o a j = p ≫ t := (pullback.condition (f := t) (g := o a j)).symm
    have hqr' : Set.range (q a j).base = (Set.range (c a j).base)ᶜ := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩ ⟨v, hv⟩
        have hy : o a j (q a j y) ∈ Set.range (q a j ≫ o a j).base := ⟨y, rfl⟩
        rw [hqr a j] at hy
        apply hy.2
        refine ⟨v, ?_⟩
        rw [← hco a j]
        exact congrArg (o a j) hv
      · intro hx
        have hxW : o a j x ∈ Set.range (q a j ≫ o a j).base := by
          rw [hqr a j]
          refine ⟨⟨x, rfl⟩, ?_⟩
          rintro ⟨v, hv⟩
          apply hx
          refine ⟨v, (o a j).isEmbedding.injective ?_⟩
          simpa only [← hco a j, Scheme.Hom.comp_apply] using hv
        obtain ⟨y, hy⟩ := hxW
        exact ⟨y, (o a j).isEmbedding.injective hy⟩
    have houter : Set.range p.base ∪ Set.range d.base = Set.univ ∧
        Disjoint (Set.range p.base) (Set.range d.base) := by
      change Set.range (pullback.fst t (o a j)).base ∪
          Set.range (pullback.fst t (z a j)).base = Set.univ ∧
        Disjoint (Set.range (pullback.fst t (o a j)).base)
          (Set.range (pullback.fst t (z a j)).base)
      simp only [Scheme.Pullback.range_fst, hzr, Set.preimage_compl]
      exact ⟨Set.union_compl_self _, disjoint_compl_right⟩
    have hinner : Set.range b.base ∪ Set.range c'.base = Set.univ ∧
        Disjoint (Set.range b.base) (Set.range c'.base) := by
      change Set.range (pullback.fst f (q a j)).base ∪
          Set.range (pullback.fst f (c a j)).base = Set.univ ∧
        Disjoint (Set.range (pullback.fst f (q a j)).base)
          (Set.range (pullback.fst f (c a j)).base)
      simp only [Scheme.Pullback.range_fst, hqr', Set.preimage_compl]
      exact ⟨Set.compl_union_self _, disjoint_compl_left⟩
    refine ⟨.node t p d inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance houter.1 houter.2
      trivial
      (.node (p ≫ t) b c' inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance hinner.1 hinner.2
        trivial
        (.tip _ inferInstance inferInstance inferInstance)
        (.tip _ inferInstance inferInstance inferInstance))
      (.tip _ inferInstance inferInstance inferInstance), ?_⟩
    change ((_ ∧ resolved k B (b ≫ p ≫ t)) ∧
      (_ ∧ resolved k C (c' ≫ p ≫ t))) ∧ (_ ∧ resolved k D (d ≫ t))
    refine ⟨⟨⟨⟨b ≫ p, (Category.assoc ..)⟩, ?_⟩,
      ⟨⟨c' ≫ p, (Category.assoc ..)⟩, ?_⟩⟩, ⟨⟨d, rfl⟩, ?_⟩⟩
    · left
      have hb : b ≫ p ≫ t = pullback.snd f (q a j) ≫ q a j ≫ o a j := by
        change pullback.fst f (q a j) ≫ p ≫ t = _
        rw [← hfc, ← Category.assoc, pullback.condition, Category.assoc]
      apply Set.disjoint_left.mpr
      rintro x ⟨y, rfl⟩ hx
      have hy : (b ≫ p ≫ t) y ∈ Set.range (q a j ≫ o a j).base := by
        rw [hb]
        exact ⟨pullback.snd f (q a j) y, rfl⟩
      rw [hqr a j] at hy
      exact hy.2 hx
    · right
      refine ⟨pullback.snd f (c a j), ?_⟩
      change pullback.snd f (c a j) ≫ s a j = c' ≫ p ≫ t
      rw [← hco a j, ← Category.assoc, ← pullback.condition, Category.assoc, hfc]
    · left
      have hd : Set.range (d ≫ t).base =
          Set.range t.base ∩ (Set.range (o a j).base)ᶜ := by
        change Set.range (pullback.fst t (z a j) ≫ t).base = _
        rw [Scheme.Pullback.range_fst_comp, hzr a j]
      apply Set.disjoint_left.mpr
      intro x hx hxS
      have hxO := (hd ▸ hx).2
      obtain ⟨v, rfl⟩ := hxS
      apply hxO
      refine ⟨c a j v, ?_⟩
      exact congrArg (fun g : S a j ⟶ W ↦ g v) (hco a j)
  have build (K : Finset ((a : Fin m) × Fin (n a))) :
      ∃ tree : SchemeRefinementTree W allowed W (𝟙 W),
        tree.AllLeaves (fun T t ↦ ∀ k ∈ K, resolved k T t) := by
    induction K using Finset.induction_on with
    | empty =>
      exact ⟨.tip _ inferInstance inferInstance inferInstance, by simp [
        SchemeRefinementTree.AllLeaves]⟩
    | @insert k K hk ih =>
      obtain ⟨tree, htree⟩ := ih
      choose replacement hreplacement using step k
      refine ⟨tree.bind replacement, SchemeRefinementTree.allLeaves_bind replacement ?_ tree
        htree⟩
      intro T t hcompact hqs himm hprocessed
      apply SchemeRefinementTree.allLeaves_mono _ (replacement T t hcompact hqs himm)
        (hreplacement T t hcompact hqs himm)
      rintro R r ⟨⟨p, hp⟩, hnew⟩ i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hnew
      · rw [← hp]
        exact resolved_comp i t p (hprocessed i hi)
  obtain ⟨tree, htree⟩ := build Finset.univ
  have hleaf : tree.AllLeaves (fun T t ↦ Nonempty T →
      ∀ a : Fin m, ∃ j : Fin (n a), ∃ f : T ⟶ S a j, f ≫ s a j = t) := by
    apply SchemeRefinementTree.allLeaves_mono _ tree htree
    intro T t ht hT a
    obtain ⟨x⟩ := hT
    have hx : t x ∈ ⋃ j : Fin (n a), Set.range (s a j).base := by
      rw [hcover a]
      exact Set.mem_univ _
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    rcases ht ⟨a, j⟩ (Finset.mem_univ _) with havoid | hfactor
    · exact False.elim (Set.disjoint_left.mp havoid ⟨x, rfl⟩ hj)
    · exact ⟨j, hfactor⟩
  obtain ⟨qtree, hqtree⟩ := forgetRefinementTree tree hleaf
  refine ⟨qtree, ?_⟩
  intro T p hp hn a
  simpa only [Category.comp_id] using hqtree T p hp hn a

private def LeafIndex {X : Scheme.{u}} : QcqsOpenClosedTree X → Type
  | @QcqsOpenClosedTree.leaf _ _ _ => PUnit
  | @QcqsOpenClosedTree.split _ _ _ _ _ _ _ _ _ _ _ _ a b => LeafIndex a ⊕ LeafIndex b

private instance leafFintype {X : Scheme.{u}} (t : QcqsOpenClosedTree X) :
    Fintype (LeafIndex t) := by
  induction t with
  | leaf => exact inferInstanceAs (Fintype PUnit)
  | split _ _ _ _ _ iha ihb =>
    exact inferInstanceAs (Fintype (_ ⊕ _))

private def leafScheme {X : Scheme.{u}} (t : QcqsOpenClosedTree X) :
    LeafIndex t → Scheme.{u} :=
  match t with
  | @QcqsOpenClosedTree.leaf X _ _ => fun _ ↦ X
  | @QcqsOpenClosedTree.split _ _ _ _ _ _ _ _ _ _ _ _ a b => Sum.elim (leafScheme a) (leafScheme b)

private def leafPath {X : Scheme.{u}} (t : QcqsOpenClosedTree X) :
    (i : LeafIndex t) → t.Path (leafScheme t i) :=
  match t with
  | @QcqsOpenClosedTree.leaf X hc hqs => fun _ ↦
    .root (@QcqsOpenClosedTree.leaf X hc hqs)
  | @QcqsOpenClosedTree.split _ _ _ _ _ j i _ _ _ _ h a b => fun k ↦
    match k with
    | .inl k => .openBranch j i h a b (leafPath a k)
    | .inr k => .closedBranch j i h a b (leafPath b k)

private theorem leafPath_isLeaf {X : Scheme.{u}} (t : QcqsOpenClosedTree X)
    (i : LeafIndex t) : (leafPath t i).IsLeaf := by
  induction t with
  | leaf => trivial
  | split j z h a b iha ihb =>
    cases i with
    | inl k => exact iha k
    | inr k => exact ihb k

private theorem pathProperties {X S : Scheme.{u}} {t : QcqsOpenClosedTree X}
    (p : t.Path S) : CompactSpace S ∧ QuasiSeparatedSpace S ∧
      IsImmersion p.toRoot ∧ QuasiCompact p.toRoot := by
  induction p with
  | root t =>
    cases t <;> dsimp only [QcqsOpenClosedTree.Path.toRoot] <;>
      exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  | openBranch j i h a b p ih =>
    dsimp only [QcqsOpenClosedTree.Path.toRoot]
    have := ih.2.2.1
    have := ih.2.2.2
    exact ⟨ih.1, ih.2.1, inferInstance, inferInstance⟩
  | closedBranch j i h a b p ih =>
    dsimp only [QcqsOpenClosedTree.Path.toRoot]
    have := ih.2.2.1
    have := ih.2.2.2
    exact ⟨ih.1, ih.2.1, inferInstance, inferInstance⟩

private theorem leafRange_constructible {X : Scheme.{u}} (t : QcqsOpenClosedTree X)
    (k : LeafIndex t) : Topology.IsConstructible (Set.range (leafPath t k).toRoot.base) := by
  induction t with
  | leaf X =>
    change Topology.IsConstructible (Set.range (𝟙 X : X ⟶ X).base)
    simp only [Scheme.Hom.id_base, TopCat.coe_id, Set.range_id]
    exact (Topology.IsConstructible.univ : Topology.IsConstructible (Set.univ : Set X))
  | split j i h a b iha ihb =>
    cases k with
    | inl k =>
      change Topology.IsConstructible (Set.range ((leafPath a k).toRoot ≫ j).base)
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      exact (iha k).image_of_isOpenEmbedding j.isOpenEmbedding j.isRetrocompact_range
    | inr k =>
      change Topology.IsConstructible (Set.range ((leafPath b k).toRoot ≫ i).base)
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      exact (ihb k).image_of_isClosedEmbedding i.isClosedEmbedding
        (h ▸ j.isRetrocompact_range)

private theorem leafCover {X : Scheme.{u}} (t : QcqsOpenClosedTree X) (x : X) :
    ∃ k : LeafIndex t, x ∈ Set.range (leafPath t k).toRoot.base := by
  induction t with
  | leaf X => exact ⟨PUnit.unit, x, rfl⟩
  | split j i h a b iha ihb =>
    by_cases hx : x ∈ Set.range j.base
    · obtain ⟨y, rfl⟩ := hx
      obtain ⟨k, z, hz⟩ := iha y
      exact ⟨.inl k, z, congrArg j.base hz⟩
    · have hx' : x ∈ Set.range i.base := by
        rw [h] at hx
        exact Classical.not_not.mp hx
      obtain ⟨y, rfl⟩ := hx'
      obtain ⟨k, z, hz⟩ := ihb y
      exact ⟨.inr k, z, congrArg i.base hz⟩

private theorem finiteAffineOver {W Y : Scheme.{u}} [CompactSpace W] (f : W ⟶ Y) :
    ∃ (n : ℕ) (V : Fin n → Y.Opens) (A : Fin n → W.Opens)
      (g : ∀ i, (A i).toScheme ⟶ (V i).toScheme),
      (∀ i, IsAffine (V i).toScheme) ∧ (∀ i, IsAffine (A i).toScheme) ∧
      (∀ i, g i ≫ (V i).ι = (A i).ι ≫ f) ∧
      ∀ x : W, ∃ i, x ∈ A i := by
  classical
  have hv (x : W) : ∃ V : Y.Opens, IsAffineOpen V ∧ f x ∈ V := by
    obtain ⟨V, hV, hxV, _⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
        (U := ⊤) (x := f x) (by trivial)
    exact ⟨V, hV, hxV⟩
  choose V hV hxV using hv
  have ha (x : W) : ∃ A : W.Opens, IsAffineOpen A ∧ x ∈ A ∧ A ≤ f ⁻¹ᵁ V x :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens (hxV x)
  choose A hA hxA hAV using ha
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover (fun x : W ↦ (A x : Set W))
    (fun x ↦ (A x).isOpen.mem_nhds (hxA x))
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  refine ⟨_, fun k ↦ V (e k), fun k ↦ A (e k),
    fun k ↦ IsOpenImmersion.lift (V (e k)).ι ((A (e k)).ι ≫ f) ?_,
    fun k ↦ hV (e k), fun k ↦ hA (e k), ?_, ?_⟩
  · rename_i k
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hAV (e k) x.property
  · intro k
    exact IsOpenImmersion.lift_fac _ _ _
  · intro x
    have hx : x ∈ ⋃ y ∈ s, (A y : Set W) := by rw [hs]; trivial
    simp only [Set.mem_iUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨e.symm ⟨y, hy⟩, by simpa using hxy⟩

/-- Given source charts with any property, target charts factor through source charts.
No preservation of that property under pullback is assumed or asserted.

Source: Stacks proetale.tex, Tag 09C3, local-structure argument; Topology Tag 09Y4.
(blueprint: lem-sf-affine-open-closed-chart-factorization).

Proof: choose a finite affine cover of U subordinate to inverse images of affine
opens of Y. Enumerate all leaves of the supplied source trees. Their path maps
are quasi-compact immersions with constructible images covering each root, by
induction on the tree and the complementary-range equation at every split.
Pull them back along the chosen affine maps and compose with the affine open
inclusions into U. Their constructible images form a finite cover of U. The
constructible-immersion partition construction produces a finite qcqs open--closed
tree whose nonempty leaves factor through members of this family, and hence through
source leaves. Pull back the finite source pro-etale chart cover along this
factorization. These pullbacks are qcqs, since the source charts are quasi-compact
over quasi-separated source leaves. The pullback range equation proves coverage.
The two fibre-product equations give the desired map to the original source chart
and the equality over Y. The property C remains on that original source chart;
no transport of C is needed. Empty leaves impose no condition. -/
theorem affineOpenClosedChartFactorization
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hs : IsSeparated f) (_ht : LocallyOfFiniteType f) (_hq : QuasiCompact f)
    (C : ∀ (T : Scheme.{u}), (T ⟶ Y) → Prop)
    (hC : ∀ (V : Y.Opens), IsAffine V.toScheme →
      ∃ tree : QcqsOpenClosedTree V.toScheme,
        ∀ (S : Scheme.{u}) (p : tree.Path S), p.IsLeaf → Nonempty S →
          ∃ (c : ℕ) (A : Fin c → S.ProEt),
            (∀ i, CompactSpace (A i).left) ∧
            (∀ i, QuasiSeparatedSpace (A i).left) ∧
            (∀ x : S, ∃ i, x ∈ Set.range (A i).hom.base) ∧
            ∀ i, C (A i).left ((A i).hom ≫ p.toRoot ≫ V.ι))
    (U : X.Opens) [IsAffine U.toScheme] :
    ∃ tree : QcqsOpenClosedTree U.toScheme,
      ∀ (S : Scheme.{u}) (p : tree.Path S), p.IsLeaf → Nonempty S →
        ∃ (c : ℕ) (A : Fin c → S.ProEt),
          (∀ i, CompactSpace (A i).left) ∧
          (∀ i, QuasiSeparatedSpace (A i).left) ∧
          (∀ x : S, ∃ i, x ∈ Set.range (A i).hom.base) ∧
          ∀ i, ∃ (T : Scheme.{u}) (g : T ⟶ Y) (h : (A i).left ⟶ T),
            C T g ∧ ((A i).hom ≫ p.toRoot ≫ U.ι) ≫ f = h ≫ g := by
  classical
  obtain ⟨n, V, B, g, hV, hB, hg, hcover⟩ := finiteAffineOver (U.ι ≫ f)
  let (j : Fin n) : IsAffine (V j).toScheme := hV j
  let (j : Fin n) : IsAffine (B j).toScheme := hB j
  choose t ht using fun j : Fin n ↦ hC (V j) (hV j)
  let I := (j : Fin n) × LeafIndex (t j)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let D (k : I) := pullback (g k.1) (leafPath (t k.1) k.2).toRoot
  let d (k : I) : D k ⟶ U.toScheme :=
    pullback.fst (g k.1) (leafPath (t k.1) k.2).toRoot ≫ (B k.1).ι
  have hprops (k : I) := pathProperties (leafPath (t k.1) k.2)
  let (k : I) : IsImmersion (leafPath (t k.1) k.2).toRoot := (hprops k).2.2.1
  let (k : I) : QuasiCompact (leafPath (t k.1) k.2).toRoot := (hprops k).2.2.2
  have himm (k : I) : IsImmersion (d k) := by dsimp [d]; infer_instance
  have hc (k : I) : Topology.IsConstructible (Set.range (d k).base) := by
    change Topology.IsConstructible (Set.range
      (pullback.fst (g k.1) (leafPath (t k.1) k.2).toRoot ≫ (B k.1).ι).base)
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_fst]
    exact Topology.IsConstructible.image_of_isOpenEmbedding
      (B k.1).ι.isOpenEmbedding (B k.1).ι.isRetrocompact_range
      ((g k.1).isConstructible_preimage (leafRange_constructible (t k.1) k.2))
  have hdcover : (⋃ k : I, Set.range (d k).base) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨j, hx⟩ := hcover x
    let y : (B j).toScheme := ⟨x, hx⟩
    obtain ⟨k, hk⟩ := leafCover (t j) (g j y)
    have hy : y ∈ Set.range (pullback.fst (g j) (leafPath (t j) k).toRoot).base := by
      rw [Scheme.Pullback.range_fst]
      exact hk
    obtain ⟨z, hz⟩ := hy
    exact Set.mem_iUnion.mpr ⟨⟨j, k⟩, z, congrArg (B j).ι.base hz⟩
  obtain ⟨tree, htree⟩ := partitionTree
    1 (fun _ ↦ Fintype.card I) (fun _ k ↦ D (e k)) (fun _ k ↦ d (e k))
    (fun _ k ↦ himm (e k)) (fun _ k ↦ hc (e k)) (by
      intro a
      exact (e.surjective.iUnion_comp (fun k : I ↦ Set.range (d k).base)).trans hdcover)
  refine ⟨tree, ?_⟩
  intro S p hp hS
  let : CompactSpace S := (pathProperties p).1
  let : QuasiSeparatedSpace S := (pathProperties p).2.1
  obtain ⟨k, m, hm⟩ := htree S p hp hS 0
  let j := (e k).1
  let z := (e k).2
  let L := leafScheme (t j) z
  let lp : L ⟶ (V j).toScheme := (leafPath (t j) z).toRoot
  let r : S ⟶ L := m ≫ pullback.snd (g j) lp
  have hL : Nonempty L := hS.map r.base
  obtain ⟨c, A, hqc, hqs, hcov, hCA⟩ := ht j L (leafPath (t j) z)
    (leafPath_isLeaf (t j) z) hL
  let : CompactSpace L := (pathProperties (leafPath (t j) z)).1
  let : QuasiSeparatedSpace L := (pathProperties (leafPath (t j) z)).2.1
  let A' : Fin c → S.ProEt := fun i ↦ Scheme.ProEt.mk (pullback.fst r (A i).hom)
  have hqc' (i : Fin c) : CompactSpace (A' i).left := by
    let : QuasiCompact (A i).hom :=
      @quasiCompact_of_compactSpace (A i).left L (A i).hom (hqc i) inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst r (A i).hom)
  have hqs' (i : Fin c) : QuasiSeparatedSpace (A' i).left := by
    let : QuasiSeparated (A i).hom :=
      @QuasiSeparated.of_quasiSeparatedSpace (A i).left L (A i).hom (hqs i)
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst r (A i).hom)
  refine ⟨c, A', hqc', hqs', ?_, ?_⟩
  · intro x
    obtain ⟨i, hi⟩ := hcov (r x)
    refine ⟨i, ?_⟩
    change x ∈ Set.range (pullback.fst r (A i).hom).base
    rw [Scheme.Pullback.range_fst]
    exact hi
  · intro i
    refine ⟨(A i).left, (A i).hom ≫ lp ≫ (V j).ι,
      pullback.snd r (A i).hom, hCA i, ?_⟩
    have hr : r ≫ lp ≫ (V j).ι = p.toRoot ≫ U.ι ≫ f := by
      dsimp only [r]
      rw [Category.assoc, ← pullback.condition_assoc, hg j]
      simpa only [d, j, z, lp, Category.assoc] using
        congrArg (fun a ↦ a ≫ U.ι ≫ f) hm
    change (pullback.fst r (A i).hom ≫ p.toRoot ≫ U.ι) ≫ f = _
    calc
      _ = pullback.fst r (A i).hom ≫ r ≫ lp ≫ (V j).ι := by
        rw [Category.assoc, hr]
        simp only [Category.assoc]
      _ = pullback.snd r (A i).hom ≫ ((A i).hom ≫ lp ≫ (V j).ι) := by
        rw [pullback.condition_assoc]

end AlgebraicGeometry.ProEtale
