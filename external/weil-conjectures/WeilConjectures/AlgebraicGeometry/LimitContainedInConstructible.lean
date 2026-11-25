/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Topology.Constructible
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Images of inverse limits in constructible subsets

Source: Stacks Project, Limits of Schemes, Lemma 05F4 in Situation 086P,
restricted to constructible subsets
(blueprint: lem-weil-pbc-limit-contained-in-constructible).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Empty pullbacks descend to a stage (Stacks, Limits, Tag 05F3).
Base change preserves the given limit; if every stage pullback were nonempty, Tag 01Z2
would make its limit nonempty. The pullback image formula gives disjointness. -/
private theorem exists_range_disjoint_of_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {j k : Iᵒᵖ} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {W : Scheme.{u}} [CompactSpace W] (g : W ⟶ D.obj (op i))
    (h : Disjoint (Set.range g) (Set.range (c.π.app (op i)))) :
    ∃ (j : I) (hj : i ≤ j),
      Disjoint (Set.range g) (Set.range (D.map (homOfLE hj).op)) := by
  classical
  have hempty : IsEmpty ↥(pullback g (c.π.app (op i)) : Scheme.{u}) := ⟨fun x ↦ by
    have heq := congrArg (fun f : pullback g (c.π.app (op i)) ⟶ D.obj (op i) ↦ f x)
      (pullback.condition (f := g) (g := c.π.app (op i)))
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at heq
    exact Set.disjoint_left.mp h ⟨pullback.fst g (c.π.app (op i)) x, rfl⟩
      (heq.symm ▸ (show c.π.app (op i) (pullback.snd g (c.π.app (op i)) x) ∈
        Set.range (c.π.app (op i)) from ⟨_, rfl⟩))⟩
  have hex : ∃ j : Over (op i), IsEmpty ((baseChangeDiagram D g).obj j) := by
    by_contra! hn
    have (j : Over (op i)) : Nonempty ((baseChangeDiagram D g).obj j) :=
      hn j
    have hne := Scheme.nonempty_of_isLimit (baseChangeDiagram D g)
      (baseChangeCone D c g) (isLimitBaseChangeCone D c g hc)
    exact hempty.false hne.some
  obtain ⟨j, hj⟩ := hex
  refine ⟨j.left.unop, leOfHom j.hom.unop, ?_⟩
  have hhom : (homOfLE (leOfHom j.hom.unop)).op = j.hom := Subsingleton.elim _ _
  rw [hhom]
  apply Set.disjoint_left.mpr
  rintro _ ⟨w, rfl⟩ hw
  have hw' : w ∈ Set.range (pullback.fst g (D.map j.hom)) := by
    rw [Scheme.Pullback.range_fst]
    exact hw
  obtain ⟨x, _⟩ := hw'
  exact hj.false x

/-- Transport Stacks, Algebra, Tag 00F8 along the affine scheme's canonical
isomorphism with the spectrum of its global sections. -/
private theorem exists_affine_range_eq_constructible
    {X : Scheme.{u}} [IsAffine X] (E : Set X) (hE : Topology.IsConstructible E) :
    ∃ (W : Scheme.{u}) (g : W ⟶ X), IsAffine W ∧ Set.range g = E := by
  let e := X.isoSpec.hom.homeomorph
  have hE' : Topology.IsConstructible (e '' E) :=
    hE.image_of_isOpenEmbedding e.isOpenEmbedding (by
      rw [e.surjective.range_eq]
      exact IsRetrocompact.univ)
  obtain ⟨R, hR, f, hf⟩ := PrimeSpectrum.exists_range_eq_of_isConstructible hE'
  let g : Spec (CommRingCat.of R) ⟶ X := Spec.map (CommRingCat.ofHom f) ≫ X.isoSpec.inv
  refine ⟨Spec (CommRingCat.of R), g, inferInstance, ?_⟩
  change Set.range (X.isoSpec.inv ∘ PrimeSpectrum.comap f) = E
  rw [Set.range_comp, hf, ← Set.image_comp]
  have he : X.isoSpec.inv ∘ e = id := by
    funext x
    simp [e, ← Scheme.Hom.comp_apply]
  rw [he, Set.image_id]

/-- A constructible subset containing the image of the limit of a directed inverse system
of quasi-compact quasi-separated schemes with affine transition maps contains the images
of every sufficiently large stage.

Source: Stacks Project, Limits of Schemes, Lemma 05F4 in Situation 086P
(blueprint: lem-weil-pbc-limit-contained-in-constructible).

Proof plan:
1. If the target stage is affine, express the constructible complement of `E` as the
   image of an affine scheme `W` (def-weil-constructible-subset and
   lem-weil-pbc-constructible-is-image).
2. The fibre product of `W` with the limit is empty: its two projections would map
   any point both into `E` and into its complement (def-pc-fibre-product).
3. Over the tail of the index set, the fibre products of `W` with the stages form
   an inverse system whose limit is this empty fibre product
   (lem-weil-pbc-scheme-over-limit and lem-weil-pbc-limit-affine-transition).
   They are affine, hence quasi-compact (lem-weil-pbc-affine-morphism-permanence).
4. Some such fibre product is empty by lem-weil-pbc-limit-nonempty, and every
   later fibre product maps to it and is therefore empty as well.
5. A point outside `E` at a later stage would lift to the fibre product: the tensor
   product of the two residue fields over their common residue field is nonzero
   and has a prime (lem-weil-pbc-fibre-product-points). This proves the affine case.
6. Cover the target stage by finitely many affine opens. The preimage opens form
   inverse systems with the corresponding open in the limit as their limit
   (lem-weil-pbc-limit-cone-affine-projections-opens). Their stages are affine,
   and `E` restricts to a constructible subset of each affine open
   (lem-weil-pbc-constructible-open-restriction). Apply the affine case to each.
7. Directedness supplies a common upper bound of the finitely many resulting
   indices, also above the original index. The images of all stages above it
   are contained in `E`, because the preimage opens cover each stage. -/
theorem exists_eventually_range_subset_of_isConstructible
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ j : Iᵒᵖ, CompactSpace (D.obj j)]
    [∀ j : Iᵒᵖ, QuasiSeparatedSpace (D.obj j)]
    [∀ {j k : Iᵒᵖ} (f : j ⟶ k), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (E : Set (D.obj (op i))) (hE : Topology.IsConstructible E)
    (himage : Set.range (c.π.app (op i)) ⊆ E) :
    ∃ i₁ : I, ∃ hi₁ : i ≤ i₁, ∀ (j : I) (hj : i₁ ≤ j),
      Set.range (D.map (homOfLE (hi₁.trans hj)).op) ⊆ E := by
  classical
  let 𝒰 := (D.obj (op i)).affineCover.finiteSubcover
  have (a : 𝒰.I₀) : IsAffine (𝒰.X a) := inferInstance
  have hex (a : 𝒰.I₀) :
      ∃ (W : Scheme.{u}) (g : W ⟶ 𝒰.X a),
        IsAffine W ∧ Set.range g = (𝒰.f a) ⁻¹' Eᶜ :=
    exists_affine_range_eq_constructible _
      (hE.compl.preimage_of_isOpenEmbedding (𝒰.f a).isOpenEmbedding)
  choose W g ha hr using hex
  let v (a : 𝒰.I₀) : W a ⟶ D.obj (op i) := g a ≫ 𝒰.f a
  have (a : 𝒰.I₀) : IsAffine (W a) := ha a
  have hdis (a : 𝒰.I₀) :
      Disjoint (Set.range (v a)) (Set.range (c.π.app (op i))) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨w, rfl⟩ hx
    have hw : g a w ∈ Set.range (g a) := ⟨w, rfl⟩
    rw [hr a] at hw
    exact hw (himage hx)
  choose j hj hd using fun a ↦ exists_range_disjoint_of_limit D c hc i (v a) (hdis a)
  obtain ⟨k, hk⟩ := (insert i (Finset.univ.image j)).exists_le
  have hik : i ≤ k := hk i (Finset.mem_insert_self _ _)
  have hjk (a : 𝒰.I₀) : j a ≤ k :=
    hk (j a) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩))
  refine ⟨k, hik, ?_⟩
  intro l hkl
  rintro _ ⟨x, rfl⟩
  by_contra hx
  obtain ⟨a, y, hy⟩ := 𝒰.exists_eq (D.map (homOfLE (hik.trans hkl)).op x)
  have hy' : y ∈ Set.range (g a) := by
    rw [hr a]
    change 𝒰.f a y ∉ E
    rwa [hy]
  obtain ⟨w, hw⟩ := hy'
  have hmem : D.map (homOfLE (hik.trans hkl)).op x ∈ Set.range (v a) := by
    refine ⟨w, ?_⟩
    change 𝒰.f a (g a w) = _
    rw [hw, hy]
  have hfactor : D.map (homOfLE (hik.trans hkl)).op =
      D.map (homOfLE ((hjk a).trans hkl)).op ≫ D.map (homOfLE (hj a)).op := by
    rw [← D.map_comp]
    congr 1
  have hmem' : D.map (homOfLE (hik.trans hkl)).op x ∈
      Set.range (D.map (homOfLE (hj a)).op) := by
    rw [hfactor, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  exact Set.disjoint_left.mp (hd a) hmem hmem'

end AlgebraicGeometry
