/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields

/-!
# Descent of point-indexed equalizer charts

Source: the current Weil conjectures blueprint, `thm-trf-frobenius-fixed-points.proof.md`,
Steps 0, 2 and 3 (blueprint: lem-trf-equalizer-point-chart-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem fixed_projection {X S : Scheme.{u}} (s : X ⟶ S) (h : X ⟶ X)
    (g : X ⟶ pullback s s) (hg₁ : g ≫ pullback.fst s s = 𝟙 X)
    (hg₂ : g ≫ pullback.snd s s = h) :
    pullback.fst g (pullback.diagonal s) = pullback.snd g (pullback.diagonal s) ∧
      pullback.fst g (pullback.diagonal s) ≫ h =
        pullback.fst g (pullback.diagonal s) := by
  have e₁ := congrArg (fun f ↦ f ≫ pullback.fst s s)
    (pullback.condition (f := g) (g := pullback.diagonal s))
  have e₂ := congrArg (fun f ↦ f ≫ pullback.snd s s)
    (pullback.condition (f := g) (g := pullback.diagonal s))
  simp only [Category.assoc, hg₁, hg₂, pullback.diagonal_fst,
    pullback.diagonal_snd, Category.comp_id] at e₁ e₂
  exact ⟨e₁, e₂.trans e₁.symm⟩

private theorem fixed_mono {X S : Scheme.{u}} (s : X ⟶ S) (h : X ⟶ X)
    (g : X ⟶ pullback s s) (hg₁ : g ≫ pullback.fst s s = 𝟙 X)
    (hg₂ : g ≫ pullback.snd s s = h) :
    Mono (pullback.fst g (pullback.diagonal s)) := by
  have e := (fixed_projection s h g hg₁ hg₂).1
  constructor
  intro T a b hab
  apply pullback.hom_ext hab
  simpa only [← e] using hab

private theorem fixed_lift_exists {X S T : Scheme.{u}} (s : X ⟶ S) (h : X ⟶ X)
    (g : X ⟶ pullback s s) (hg₁ : g ≫ pullback.fst s s = 𝟙 X)
    (hg₂ : g ≫ pullback.snd s s = h) (a : T ⟶ X) (ha : a ≫ h = a) :
    ∃ b : T ⟶ pullback g (pullback.diagonal s),
      b ≫ pullback.fst g (pullback.diagonal s) = a := by
  have w : a ≫ g = a ≫ pullback.diagonal s := by
    apply pullback.hom_ext <;> simp [Category.assoc, hg₁, hg₂, ha]
  exact ⟨pullback.lift a a w, pullback.lift_fst _ _ _⟩

set_option backward.isDefEq.respectTransparency false in
private theorem fixed_quotient_lift {B : Type u} [CommRing B] (φ : B →+* B)
    (I : Ideal B) (hI : I = Ideal.span (Set.range (fun b : B ↦ φ b - b)))
    {T : Scheme.{u}} (a : T ⟶ Spec (.of B))
    (ha : a ≫ Spec.map (CommRingCat.ofHom φ) = a) :
    ∃ b : T ⟶ Spec (.of (B ⧸ I)),
      b ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = a := by
  have hker : I ≤ RingHom.ker ((Scheme.ΓSpecIso (.of B)).inv ≫ a.appTop).hom := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    have e := congrArg (fun f ↦ (Scheme.ΓSpecIso (.of B)).inv ≫ f.appTop) ha
    rw [Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality] at e
    have eb := congrArg (fun f ↦ f.hom b) e
    change (((Scheme.ΓSpecIso (.of B)).inv ≫ a.appTop).hom) (φ b - b) = 0
    rw [map_sub, sub_eq_zero]
    exact eb
  exact ⟨a.liftQuotient I hker, a.liftQuotient_comp I hker⟩

private theorem fixed_quotient_equalizes {B : Type u} [CommRing B] (φ : B →+* B)
    (I : Ideal B) (hI : I = Ideal.span (Set.range (fun b : B ↦ φ b - b))) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
        Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  ext b
  change Ideal.Quotient.mk I (φ b) = Ideal.Quotient.mk I b
  apply Ideal.Quotient.eq.mpr
  rw [hI]
  exact Ideal.subset_span ⟨b, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem fixed_chart_exists {X S : Scheme.{u}} (s : X ⟶ S) (h : X ⟶ X)
    (g : X ⟶ pullback s s) (hg₁ : g ≫ pullback.fst s s = 𝟙 X)
    (hg₂ : g ≫ pullback.snd s s = h)
    {B : Type u} [CommRing B] (c : Spec (.of B) ⟶ X) [IsOpenImmersion c]
    (φ : B →+* B) (hφ : Spec.map (CommRingCat.ofHom φ) ≫ c = c ≫ h)
    (I : Ideal B) (hI : I = Ideal.span (Set.range (fun b : B ↦ φ b - b))) :
    ∃ e : Spec (.of (B ⧸ I)) ≅ pullback (pullback.fst g (pullback.diagonal s)) c,
      e.hom ≫ pullback.snd (pullback.fst g (pullback.diagonal s)) c =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  let i := pullback.fst g (pullback.diagonal s)
  let π := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : Mono i := fixed_mono s h g hg₁ hg₂
  obtain ⟨f, hf⟩ := fixed_lift_exists s h g hg₁ hg₂ (π ≫ c) (by
    rw [Category.assoc, ← hφ, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ c) (fixed_quotient_equalizes φ I hI))
  let u : Spec (.of (B ⧸ I)) ⟶ pullback i c := pullback.lift f π hf
  have heq : pullback.snd i c ≫ Spec.map (CommRingCat.ofHom φ) =
      pullback.snd i c := by
    apply (cancel_mono c).mp
    rw [Category.assoc, hφ, ← Category.assoc, ← pullback.condition, Category.assoc]
    exact congrArg (fun t ↦ pullback.fst i c ≫ t)
      (fixed_projection s h g hg₁ hg₂).2
  obtain ⟨v, hv⟩ := fixed_quotient_lift φ I hI (pullback.snd i c) heq
  have : IsClosedImmersion π := @IsClosedImmersion.spec_of_quotient_mk (.of B) I
  have : Mono π := inferInstance
  change v ≫ π = pullback.snd i c at hv
  have hu : u ≫ pullback.snd i c = π := pullback.lift_snd _ _ _
  refine ⟨⟨u, v, ?_, ?_⟩, hu⟩
  · apply (cancel_mono π).mp
    simpa only [Category.assoc, hv, Category.id_comp] using hu
  · apply (cancel_mono (pullback.snd i c)).mp
    simp only [Category.assoc, hu, hv, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem field_germ_iso (k : Type u) [Field k] (a : Spec (.of k)) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.Γgerm a) := by
  change IsIso (StructureSheaf.toStalk k a)
  apply (ConcreteCategory.isIso_iff_bijective _).2
  change Function.Bijective (algebraMap k ((Spec.structureSheaf k).presheaf.stalk a))
  apply Field.localization_map_bijective (M := a.asIdeal.primeCompl)
  exact fun h ↦ h (Ideal.zero_mem _)

set_option backward.isDefEq.respectTransparency false in
/-- Descent of evaluation-normalized affine equalizer charts to the canonical finite disjoint
union of fixed rational points, including its finite étale structure and length-one stalks.
Source: the current blueprint, `thm-trf-frobenius-fixed-points.proof.md`, Steps 0, 2 and 3
(blueprint: lem-trf-equalizer-point-chart-descent).

Proof plan:
1. Every label belongs to some `Pj j`, by the open cover and the universal property of an
   open immersion. Thus `P` is finite. The pullback of the graph and diagonal represents maps
   equalizing `h` and the identity, so its first projection is monic. Each fixed point lifts
   uniquely; the coproduct universal property gives the unique map `q`.
2. On chart `j`, the ideal generated by `φ j b - b` cuts out the equalizer. The quotient map
   equalizes the endomorphism. Conversely, a map from any test scheme to the affine chart
   equalizing the endomorphism kills the difference ideal on global sections. The
   spectrum-global-sections adjunction and `Scheme.Hom.liftQuotient` factor it through the
   quotient spectrum. The two universal properties give `e j`, normalized by its projection.
3. Compose `sigmaSpec`, the spectrum of `ε j`, and `e j`. The evaluation equation `hε`
   identifies its summand maps with the canonical point lifts. These are open immersions and
   jointly cover the equalizer, by the chart cover. Coproduct extensionality gives the
   displayed restriction equation.
4. The images of distinct point lifts are disjoint: choose a chart at any alleged common
   image. Both labels belong to that chart; its evaluation isomorphism and disjointness of
   coproduct summands force the labels to agree. Hence `isOpenImmersion_sigmaDesc` and
   surjectivity make `q` an isomorphism. Cancel the monic equalizer projection to prove
   compatibility for maps from arbitrary test schemes on overlaps. No affine-overlap or
   separatedness hypothesis is used.
5. The structure map of the finite coproduct is `sigmaSpec` followed by the spectrum of the
   diagonal algebra map into the finite product of copies of `k`. This algebra is a finite
   `k`-module, including the empty product. The spectrum criterion and composition with the
   isomorphism `q` prove finiteness of the equalizer structure map.
6. Apply `etale_sigmaDesc_spec_of_finite_separable` to the identity extensions `k/k` to obtain
   étaleness of the coproduct structure map, and transport along `q`.
7. Every point lies in a point-lift open immersion. Its stalk map is an isomorphism.
   Naturality of germs identifies the composite with the structural stalk map with the
   canonical map from `k` to a stalk of `Spec k`. This is an isomorphism, since localization
   of a field away from zero is an isomorphism. Cancel the open-immersion stalk map. The
   resulting field structure makes the stalk simple over itself, and `Module.length_eq_one`
   gives length one. For the empty equalizer this assertion is vacuous.
The coproduct facts are `lem-weil-pbc-scheme-coproduct-family` and
`lem-weil-pbc-finite-affine-coproduct-spectrum`; the étale input is
`lem-exc-etale-coproduct-etale`. -/
theorem equalizer_point_chart_descent
    (k : Type u) [Field k] (X : Scheme.{u}) (s : X ⟶ Spec (.of k))
    (h : X ⟶ X) (hs : h ≫ s = s)
    (g : X ⟶ pullback s s)
    (hg₁ : g ≫ pullback.fst s s = 𝟙 X)
    (hg₂ : g ≫ pullback.snd s s = h)
    (J : Type v) [Finite J] (B : J → Type u) [∀ j, CommRing (B j)]
    [∀ j, Algebra k (B j)] (c : ∀ j, Spec (.of (B j)) ⟶ X)
    [∀ j, IsOpenImmersion (c j)]
    (hc : ∀ z : X, ∃ j, z ∈ Set.range (c j))
    (hcs : ∀ j, c j ≫ s = Spec.map (CommRingCat.ofHom (algebraMap k (B j))))
    (φ : ∀ j, B j →ₐ[k] B j)
    (hφ : ∀ j, Spec.map (CommRingCat.ofHom (φ j).toRingHom) ≫ c j = c j ≫ h)
    (I : ∀ j, Ideal (B j))
    (hI : ∀ j, I j = Ideal.span (Set.range (fun b : B j ↦ φ j b - b)))
    (P : Type u) (x : P → (Spec (.of k) ⟶ X))
    (hxs : ∀ p, x p ≫ s = 𝟙 _)
    (hx : ∀ p, x p ≫ h = x p)
    (Pj : J → Set P)
    (hPj : ∀ j p, p ∈ Pj j ↔
      ∃ a : Spec (.of k) ⟶ Spec (.of (B j)), a ≫ c j = x p)
    [∀ j, Finite (Pj j)]
    (ε : ∀ j, (B j ⧸ I j) ≃ₐ[k] ((Pj j) → k))
    (hε : ∀ j (p : Pj j),
      Spec.map (CommRingCat.ofHom ((Pi.evalRingHom (fun _ : Pj j ↦ k) p).comp
        ((ε j).toRingHom.comp (Ideal.Quotient.mk (I j))))) ≫ c j = x p.val) :
    Finite P ∧
      ∃ q : (∐ fun _ : P ↦ Spec (.of k)) ⟶ pullback g (pullback.diagonal s),
        (∀ p, Sigma.ι (fun _ : P ↦ Spec (.of k)) p ≫ q ≫
          pullback.fst g (pullback.diagonal s) = x p) ∧
        (∀ q' : (∐ fun _ : P ↦ Spec (.of k)) ⟶ pullback g (pullback.diagonal s),
          (∀ p, Sigma.ι (fun _ : P ↦ Spec (.of k)) p ≫ q' ≫
            pullback.fst g (pullback.diagonal s) = x p) → q' = q) ∧
        IsIso q ∧
        (∃ e : ∀ j, Spec (.of (B j ⧸ I j)) ≅
            pullback (pullback.fst g (pullback.diagonal s)) (c j),
          (∀ j, (e j).hom ≫
            pullback.snd (pullback.fst g (pullback.diagonal s)) (c j) =
              Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I j)))) ∧
          (∀ j, Sigma.desc (fun p : Pj j ↦
              Sigma.ι (fun _ : P ↦ Spec (.of k)) p.val) ≫ q =
            sigmaSpec (fun _ : Pj j ↦ CommRingCat.of k) ≫
              Spec.map (CommRingCat.ofHom (ε j).toRingHom) ≫ (e j).hom ≫
                pullback.fst (pullback.fst g (pullback.diagonal s)) (c j)) ∧
          (∀ (T : Scheme.{u}) (j l : J)
              (a : T ⟶ Spec (.of (B j ⧸ I j)))
              (b : T ⟶ Spec (.of (B l ⧸ I l))),
            a ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I j))) ≫ c j =
              b ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I l))) ≫ c l →
            a ≫ (e j).hom ≫
                pullback.fst (pullback.fst g (pullback.diagonal s)) (c j) =
              b ≫ (e l).hom ≫
                pullback.fst (pullback.fst g (pullback.diagonal s)) (c l))) ∧
        IsFinite (pullback.fst g (pullback.diagonal s) ≫ s) ∧
        Etale (pullback.fst g (pullback.diagonal s) ≫ s) ∧
        (∀ z : (pullback g (pullback.diagonal s) : Scheme.{u}),
          IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
            (pullback.fst g (pullback.diagonal s) ≫ s).appTop ≫
              (pullback g (pullback.diagonal s)).presheaf.Γgerm z) ∧
          Module.length ((pullback g (pullback.diagonal s)).presheaf.stalk z)
            ((pullback g (pullback.diagonal s)).presheaf.stalk z) = 1) := by
  classical
  have _ := hs
  have _ := hcs
  -- The graph pullback represents the equalizer; its projection is a monomorphism.
  let E := pullback g (pullback.diagonal s)
  let i : E ⟶ X := pullback.fst g (pullback.diagonal s)
  have : Mono i := fixed_mono s h g hg₁ hg₂
  let t : Spec (.of k) := IsLocalRing.closedPoint k
  have point_chart (p : P) : ∃ j, p ∈ Pj j := by
    obtain ⟨j, hj⟩ := hc (x p t)
    refine ⟨j, (hPj j p).2 ?_⟩
    have hr : Set.range (x p) ⊆ Set.range (c j) := by
      rintro _ ⟨z, rfl⟩
      simpa only [Subsingleton.elim z t] using hj
    exact ⟨IsOpenImmersion.lift (c j) (x p) hr, IsOpenImmersion.lift_fac _ _ _⟩
  have fin : Finite P := by
    apply Finite.of_surjective (fun p : Σ j, Pj j ↦ p.2.val)
    intro p
    obtain ⟨j, hj⟩ := point_chart p
    exact ⟨⟨j, p, hj⟩, rfl⟩
  refine ⟨fin, ?_⟩
  choose y hy using fun p ↦ fixed_lift_exists s h g hg₁ hg₂ (x p) (hx p)
  change ∀ p, y p ≫ i = x p at hy
  let q : (∐ fun _ : P ↦ Spec (.of k)) ⟶ E := Sigma.desc y
  have hq (p : P) : Sigma.ι (fun _ : P ↦ Spec (.of k)) p ≫ q ≫ i = x p := by
    simp [q, hy]
  -- Quotient charts are obtained by the universal property, even for nonaffine tests.
  choose e he using fun j ↦ fixed_chart_exists s h g hg₁ hg₂
    (c j) (φ j).toRingHom (hφ j) (I j) (hI j)
  let vj (j : J) : (∐ fun _ : Pj j ↦ Spec (.of k)) ⟶ pullback i (c j) :=
    sigmaSpec (fun _ : Pj j ↦ CommRingCat.of k) ≫
      Spec.map (CommRingCat.ofHom (ε j).toRingHom) ≫ (e j).hom
  have vj_iso (j : J) : IsIso (vj j) := by
    have : IsIso (CommRingCat.ofHom (ε j).toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (ε j).bijective
    change IsIso (sigmaSpec (fun _ : Pj j ↦ CommRingCat.of k) ≫
      Spec.map (CommRingCat.ofHom (ε j).toRingHom) ≫ (e j).hom)
    infer_instance
  have vj_point (j : J) (p : Pj j) :
      Sigma.ι (fun _ : Pj j ↦ Spec (.of k)) p ≫ vj j ≫ pullback.fst i (c j) = y p.val := by
    apply (cancel_mono i).mp
    rw [Category.assoc, Category.assoc, pullback.condition]
    change Sigma.ι (fun _ : Pj j ↦ Spec (.of k)) p ≫
      (sigmaSpec (fun _ : Pj j ↦ CommRingCat.of k) ≫
        Spec.map (CommRingCat.ofHom (ε j).toRingHom) ≫ (e j).hom) ≫
          pullback.snd i (c j) ≫ c j = y p.val ≫ i
    simp only [Category.assoc, ι_sigmaSpec_assoc]
    rw [← Category.assoc (e j).hom, he j]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    simpa only [CommRingCat.ofHom_comp, Category.assoc] using
      (hε j p).trans (hy p.val).symm
  have hy_open (p : P) : IsOpenImmersion (y p) := by
    obtain ⟨j, hp⟩ := point_chart p
    rw [← vj_point j ⟨p, hp⟩]
    have := vj_iso j
    infer_instance
  have hy_surj : ∀ z : E, ∃ p a, y p a = z := by
    intro z
    obtain ⟨j, a, ha⟩ := hc (i z)
    have hz : z ∈ Set.range (pullback.fst i (c j)) := by
      rw [IsOpenImmersion.range_pullbackFst]
      exact ⟨a, ha⟩
    obtain ⟨w, rfl⟩ := hz
    have := vj_iso j
    obtain ⟨d, rfl⟩ := (vj j).homeomorph.surjective w
    obtain ⟨p, a, hd⟩ := (sigmaOpenCover (fun _ : Pj j ↦ Spec (.of k))).exists_eq d
    refine ⟨p.val, a, ?_⟩
    rw [← hd]
    exact (congrArg (fun f ↦ f a) (vj_point j p)).symm
  -- Labels are distinct on every chart, hence globally; no separatedness is needed.
  have hy_disj : Pairwise (Function.onFun Disjoint (fun p ↦ Set.range (y p))) := by
    intro p r hpr
    apply Set.disjoint_left.mpr
    rintro z ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨j, c₀, hc₀⟩ := hc (i z)
    have memj (p' : P) (a' : Spec (.of k)) (h' : y p' a' = z) : p' ∈ Pj j := by
      apply (hPj j p').2
      have hr : Set.range (x p') ⊆ Set.range (c j) := by
        rintro _ ⟨d, rfl⟩
        have heq : x p' d = i z := by
          rw [← hy p', Scheme.Hom.comp_apply, Subsingleton.elim d a', h']
        rw [heq]
        exact ⟨c₀, hc₀⟩
      exact ⟨IsOpenImmersion.lift (c j) (x p') hr, IsOpenImmersion.lift_fac _ _ _⟩
    let p' : Pj j := ⟨p, memj p a ha⟩
    let r' : Pj j := ⟨r, memj r b hb⟩
    have heq : (Sigma.ι (fun _ : Pj j ↦ Spec (.of k)) p' ≫ vj j ≫
        pullback.fst i (c j)) a = (Sigma.ι (fun _ : Pj j ↦ Spec (.of k)) r' ≫
        vj j ≫ pullback.fst i (c j)) b := by
      rw [vj_point, vj_point]
      exact ha.trans hb.symm
    have := vj_iso j
    simp only [Scheme.Hom.comp_apply] at heq
    have hlabels := (sigmaι_eq_iff _ _ _ _ _).mp
      ((vj j).isOpenEmbedding.injective ((pullback.fst i (c j)).isOpenEmbedding.injective heq))
    exact hpr (congrArg (fun p : Σ _ : Pj j, Spec (.of k) ↦ p.1.val) hlabels)
  have : IsOpenImmersion q := isOpenImmersion_sigmaDesc _ _ hy_disj
  have : Surjective q := by
    constructor
    intro z
    obtain ⟨p, a, ha⟩ := hy_surj z
    refine ⟨Sigma.ι (fun _ : P ↦ Spec (.of k)) p a, ?_⟩
    simpa only [← Scheme.Hom.comp_apply, q, Sigma.ι_comp_desc] using ha
  have : IsIso q := (isIso_iff_isOpenImmersion_and_surjective q).2 ⟨‹_›, ‹_›⟩
  refine ⟨q, hq, ?_, ‹IsIso q›, ?_, ?_, ?_, ?_⟩
  · intro q' hq'
    apply (cancel_mono i).mp
    apply Sigma.hom_ext
    intro p
    exact (hq' p).trans (hq p).symm
  · refine ⟨e, he, ?_, ?_⟩
    · intro j
      apply Sigma.hom_ext
      intro p
      simpa only [Sigma.ι_comp_desc_assoc, q, Sigma.ι_comp_desc, vj, Category.assoc]
        using (vj_point j p).symm
    · intro T j l a b hab
      apply (cancel_mono i).mp
      change a ≫ (e j).hom ≫ pullback.fst i (c j) ≫ i =
        b ≫ (e l).hom ≫ pullback.fst i (c l) ≫ i
      rw [pullback.condition, pullback.condition, ← Category.assoc (e j).hom, he j,
        ← Category.assoc (e l).hom, he l]
      exact hab
  · have str : q ≫ (i ≫ s) = sigmaSpec (fun _ : P ↦ CommRingCat.of k) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (P → k))) := by
      apply Sigma.hom_ext
      intro p
      rw [ι_sigmaSpec_assoc]
      change Sigma.ι (fun _ : P ↦ Spec (.of k)) p ≫ Sigma.desc y ≫ i ≫ s = _
      rw [Sigma.ι_comp_desc_assoc, ← Category.assoc, hy, hxs, ← Spec.map_comp]
      symm
      convert Spec.map_id (.of k) using 2
      ext a
      rfl
    have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (P → k)))) := by
      rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr inferInstance
    have : IsFinite (q ≫ (i ≫ s)) := by rw [str]; infer_instance
    have : IsFinite (inv q ≫ (q ≫ (i ≫ s))) := inferInstance
    simpa only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] using this
  · have str : q ≫ (i ≫ s) = Sigma.desc (fun _ : P ↦
        Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
      apply Sigma.hom_ext
      intro p
      change Sigma.ι (fun _ : P ↦ Spec (.of k)) p ≫ Sigma.desc y ≫ i ≫ s = _
      rw [Sigma.ι_comp_desc_assoc, ← Category.assoc, hy, hxs, Sigma.ι_comp_desc]
      exact (Spec.map_id (.of k)).symm
    have : Etale (q ≫ (i ≫ s)) := by
      rw [str]
      exact etale_sigmaDesc_spec_of_finite_separable k P (fun _ ↦ k)
    have : Etale (inv q ≫ (q ≫ (i ≫ s))) := inferInstance
    simpa only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] using this
  · intro z
    -- On each open summand the structural stalk map is the field localization map.
    obtain ⟨p, a, rfl⟩ := hy_surj z
    let f : E ⟶ Spec (.of k) := i ≫ s
    let α := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ E.presheaf.Γgerm (y p a)
    have fac : α ≫ (y p).stalkMap a =
        (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.Γgerm a := by
      dsimp [α]
      change (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        E.presheaf.germ ⊤ (y p a) (by trivial) ≫ (y p).stalkMap a = _
      rw [Scheme.Hom.germ_stalkMap]
      simp only [Scheme.Hom.preimage_top]
      have hys : y p ≫ f = 𝟙 _ := by dsimp [f]; rw [← Category.assoc, hy, hxs]
      simpa only [Scheme.Hom.appTop, Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop,
        Category.id_comp, Category.assoc, TopCat.Presheaf.Γgerm] using
          congrArg (fun t ↦ (Scheme.ΓSpecIso (.of k)).inv ≫
          t.appTop ≫ (Spec (.of k)).presheaf.Γgerm a) hys
    have : IsIso (α ≫ (y p).stalkMap a) := by rw [fac]; exact field_germ_iso k a
    have : IsIso α := IsIso.of_isIso_comp_right α ((y p).stalkMap a)
    refine ⟨this, ?_⟩
    have hf : IsField (E.presheaf.stalk (y p a)) :=
      (asIso α).commRingCatIsoToRingEquiv.symm.toMulEquiv.isField (Field.toIsField k)
    let := hf.toField
    exact Module.length_eq_one _ _

end AlgebraicGeometry
