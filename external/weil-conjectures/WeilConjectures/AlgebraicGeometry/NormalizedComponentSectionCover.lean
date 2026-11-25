/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import WeilConjectures.AlgebraicGeometry.GlueComponentReducedCoverSections
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
import Mathlib.Topology.DiscreteSubset

/-! # A normalized frame cover for prescribed component sections

Source: Stacks Project, Varieties Lemma 09NE (lemma-glue-invertible-sheaves).
(blueprint: lem-sc-normalized-component-section-cover) -/

@[expose] public section

universe u v
open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

private theorem freeGenerator_empty {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (hU : U = ⊥) (e : Γ(M, U)) : IsFreeGenerator e := by
  subst U
  exact isFreeGenerator_of_mem e (S := ⊥) (fun _ hx ↦ hx.elim) fun _ _ h ↦ h.elim

/-- Source: Stacks Project, Varieties Lemma 09NE, first three paragraphs of the direct
proof and final paragraph (normalizing the frames by the prescribed sections).

Proof: Let T be the finite union of pairwise intersections. The reduced-cover lemma
makes T closed and identifies the component opens off T scheme-theoretically, with a
product bijection on structure sections on every open disjoint from T. T is discrete:
a finite union of closed discrete subsets is discrete. Choose one open U_t for each
point t of T, meeting T only at t. Remove every component not containing t. On each
incident component s is nonzero in the residue-field fibre. A section of an invertible
module with nonzero fibre is a local free generator: choose a trivialization, whose
section coefficient has a germ outside the maximal ideal, and restrict to its basic
open. Shrink U_t simultaneously along these finitely many component neighborhoods.
For each incident component use the restricted s as frame m, and use f_t=1 on U_t.
For nonincident components the preimage is empty and its unique section is a frame.
Off T cover each component by its free-generator neighborhoods, regarded as opens of Y
by the reduced-cover lemma. Use that component's frames and the unique empty sections
on all other components. The structure-section bijection transfers the coefficient
of s in its frame to a function f on Y. Index the union of the point neighborhoods
and component neighborhoods by a type in universe max(u,v). Every distinct pair of
members overlaps outside T: point neighborhoods have distinct distinguished points,
and all other members avoid T. Thus for every open W contained in a distinct overlap,
the reduced-cover section bijection applies. This proves all the asserted clauses.
If T is empty take only component neighborhoods; if Y is empty take the empty cover.
No transition unit, cocycle, glued module, or global section is constructed here.
(blueprint: lem-sc-normalized-component-section-cover) -/
theorem exists_normalized_component_section_cover
    {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a : ι, Z a ⟶ Y) [∀ a : ι, IsClosedImmersion (i a)]
    (hcover : (⋃ a : ι, Set.range (i a)) = Set.univ)
    (hdiscrete : ∀ a b : ι, a ≠ b →
      DiscreteTopology ↥(Set.range (i a) ∩ Set.range (i b)))
    (M : ∀ a : ι, (Z a).Modules) [∀ a : ι, (M a).IsInvertible]
    (s : ∀ a : ι, Γ(M a, ⊤))
    (hs : ∀ a b : ι, a ≠ b → Set.range (i a) ∩ Set.range (i b) ⊆
      i a '' nonvanishingLocus (M a) (s a)) :
    ∃ (κ : Type (max u v)) (U : κ → Y.Opens) (f : ∀ b, Γ(Y, U b))
      (m : ∀ a b, Γ(M a, (i a) ⁻¹ᵁ U b)),
      (⨆ b, U b) = ⊤ ∧
      (∀ a b, IsFreeGenerator (m a b)) ∧
      (∀ a b, (M a).presheaf.map (homOfLE le_top).op (s a) =
        ((i a).app (U b)).hom (f b) • m a b) ∧
      ∀ b c, b ≠ c → ∀ (W : Y.Opens), W ≤ U b → W ≤ U c →
        Function.Bijective
          (fun r : Γ(Y, W) ↦ fun a ↦ ((i a).app W).hom r) := by
  classical
  let T : Set Y := ⋃ a : ι, ⋃ b : ι, ⋃ (_ : b ≠ a),
    Set.range (i a) ∩ Set.range (i b)
  obtain ⟨-, hcomponentOpen, hcomponentDisjoint, -, hsections⟩ :=
    glue_component_reduced_cover_sections Z i hcover
  change ∀ a, IsOpen (Tᶜ ∩ Set.range (i a)) at hcomponentOpen
  change Pairwise (fun a b ↦ Disjoint (Tᶜ ∩ Set.range (i a))
    (Tᶜ ∩ Set.range (i b))) at hcomponentDisjoint
  change ∀ V : Y.Opens, (V : Set Y) ⊆ Tᶜ → Function.Bijective
    (fun r : Γ(Y, V) ↦ fun a ↦ ((i a).app V).hom r) at hsections
  have hclosed (a : ι) : IsClosed (Set.range (i a)) :=
    (i a).isClosedEmbedding.isClosed_range
  have hTd : _root_.IsDiscrete T := by
    apply _root_.IsDiscrete.iUnion
    · intro a
      apply _root_.IsDiscrete.iUnion
      · intro b
        apply _root_.IsDiscrete.iUnion
        · intro hba
          exact ⟨hdiscrete a b hba.symm⟩
        · intro _
          exact (hclosed a).inter (hclosed b)
      · intro b
        exact isClosed_iUnion_of_finite fun _ ↦ (hclosed a).inter (hclosed b)
    · intro a
      exact isClosed_iUnion_of_finite fun b ↦
        isClosed_iUnion_of_finite fun _ ↦ (hclosed a).inter (hclosed b)
  have hnormalize (t : T) (a : ι) {z : Z a} (hz : i a z = t) :
      z ∈ generatingLocus (s a) := by
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp t.property
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hb
    obtain ⟨hcb, hbc⟩ := Set.mem_iUnion.mp hc
    have ht : (t : Y) ∈ i a '' nonvanishingLocus (M a) (s a) := by
      by_cases hab : a = b
      · subst b
        exact hs a c hcb.symm hbc
      · exact hs a b hab ⟨⟨z, hz⟩, hbc.1⟩
    obtain ⟨z', hz', heq⟩ := ht
    have heq' : z' = z := (i a).isClosedEmbedding.injective (heq.trans hz.symm)
    subst z'
    exact (mem_nonvanishingLocus_iff_generatesAt (M a) (s a) z).mp hz'
  have hpoint (t : T) : ∃ U : Y.Opens, (t : Y) ∈ U ∧
      (∀ x ∈ U, x ∈ T → x = t) ∧
      ∀ a, IsFreeGenerator ((M a).presheaf.map
        (homOfLE (le_top : (i a) ⁻¹ᵁ U ≤ ⊤)).op (s a)) := by
    obtain ⟨V, hVopen, hVT⟩ :=
      isDiscrete_iff_forall_mem_exists_isOpen.mp hTd t t.property
    let B (a : ι) : Set Y := i a '' (generatingLocus (s a) : Set (Z a))ᶜ
    have hB (a : ι) : IsClosed (B a) :=
      (i a).isClosedEmbedding.isClosedMap _ (generatingLocus (s a)).isOpen.isClosed_compl
    let U : Y.Opens := ⟨V ∩ (⋃ a, B a)ᶜ,
      hVopen.inter (isClosed_iUnion_of_finite hB).isOpen_compl⟩
    have htV : (t : Y) ∈ V := by
      have : (t : Y) ∈ V ∩ T := by rw [hVT]; exact Set.mem_singleton _
      exact this.1
    have htU : (t : Y) ∈ U := by
      refine ⟨htV, ?_⟩
      intro h
      obtain ⟨a, z, hz, heq⟩ := Set.mem_iUnion.mp h
      exact hz (hnormalize t a heq)
    refine ⟨U, htU, ?_, ?_⟩
    · intro x hx hxT
      have : x ∈ V ∩ T := ⟨hx.1, hxT⟩
      rwa [hVT, Set.mem_singleton_iff] at this
    · intro a
      have hpre : (i a) ⁻¹ᵁ U ≤ generatingLocus (s a) := by
        intro z hz
        by_contra hzg
        exact hz.2 (Set.mem_iUnion.mpr ⟨a, z, hzg, rfl⟩)
      have hg := (isFreeGenerator_generatingLocus (s a)).map hpre
      simpa only [presheaf_map_homOfLE_map_homOfLE] using hg
  have hoff (x : Y) (hx : x ∈ Tᶜ) : ∃ U : Y.Opens, x ∈ U ∧
      (U : Set Y) ⊆ Tᶜ ∧ ∃ m : ∀ a, Γ(M a, (i a) ⁻¹ᵁ U),
        (∀ a, IsFreeGenerator (m a)) := by
    have hc : x ∈ ⋃ a, Set.range (i a) := by rw [hcover]; trivial
    obtain ⟨a, z, hz⟩ := Set.mem_iUnion.mp hc
    let D : Y.Opens := ⟨Tᶜ ∩ Set.range (i a), hcomponentOpen a⟩
    have hzD : z ∈ (i a) ⁻¹ᵁ D := by
      change i a z ∈ Tᶜ ∩ Set.range (i a)
      exact ⟨hz ▸ hx, ⟨z, rfl⟩⟩
    have : SheafOfModules.IsInvertible.{u, u, u} (M a) :=
      IsInvertible.sheafOfModules_isInvertible (M a)
    obtain ⟨W, hzW, hWD, e, he⟩ := exists_isFreeGenerator (M a) hzD
    let B : Set Y := i a '' (W.1 : Set (Z a))ᶜ
    have hB : IsClosed B := (i a).isClosedEmbedding.isClosedMap _ W.1.isOpen.isClosed_compl
    let U : Y.Opens := ⟨(D : Set Y) ∩ Bᶜ, D.isOpen.inter hB.isOpen_compl⟩
    have hxU : x ∈ U := by
      refine ⟨hz ▸ hzD, ?_⟩
      rintro ⟨z', hz', heq⟩
      have heq' : z' = z := (i a).isClosedEmbedding.injective (heq.trans hz.symm)
      subst z'
      exact hz' hzW
    have hUT : (U : Set Y) ⊆ Tᶜ := fun _ h ↦ h.1.1
    have hUW : (i a) ⁻¹ᵁ U ≤ W.1 := by
      intro z' hz'
      by_contra hn
      exact hz'.2 ⟨z', hn, rfl⟩
    have hempty (b : ι) (hba : b ≠ a) : (i b) ⁻¹ᵁ U = ⊥ := by
      ext z'
      constructor
      · intro hz'
        have hd := hcomponentDisjoint hba
        exact (Set.disjoint_left.mp hd
          ⟨hUT hz', ⟨z', rfl⟩⟩ hz'.1).elim
      · intro hz'
        exact hz'.elim
    let m (b : ι) : Γ(M b, (i b) ⁻¹ᵁ U) := by
      by_cases hba : b = a
      · subst b
        exact (M a).presheaf.map (homOfLE hUW).op e
      · exact 0
    refine ⟨U, hxU, hUT, m, ?_⟩
    intro b
    by_cases hba : b = a
    · subst b
      simpa only [m, dite_eq_left rfl] using he.map hUW
    · exact freeGenerator_empty (M b) (hempty b hba) (m b)
  have hoffCoefficient (x : ↥(Tᶜ)) : ∃ U : Y.Opens, (x : Y) ∈ U ∧
      (U : Set Y) ⊆ Tᶜ ∧ ∃ (f : Γ(Y, U)) (m : ∀ a, Γ(M a, (i a) ⁻¹ᵁ U)),
        (∀ a, IsFreeGenerator (m a)) ∧
        ∀ a, (M a).presheaf.map (homOfLE le_top).op (s a) =
          ((i a).app U).hom f • m a := by
    obtain ⟨U, hxU, hUT, m, hm⟩ := hoff x x.property
    let r (a : ι) := (hm a).coeff
      ((M a).presheaf.map (homOfLE le_top).op (s a))
    obtain ⟨f, hf⟩ := (hsections U hUT).2 r
    refine ⟨U, hxU, hUT, f, m, hm, ?_⟩
    intro a
    rw [show ((i a).app U).hom f = r a from congrFun hf a]
    exact ((hm a).coeff_smul _).symm
  choose Up hUp hUpT hUpm using hpoint
  choose Uo hUo hUoT fo mo hmo hso using hoffCoefficient
  let κ : Type (max u v) := ULift.{v} T ⊕ ULift.{v} ↥(Tᶜ)
  let U : κ → Y.Opens := Sum.elim (fun t ↦ Up t.down) (fun x ↦ Uo x.down)
  let f : ∀ b, Γ(Y, U b) := fun b ↦ match b with
    | .inl _ => 1
    | .inr x => fo x.down
  let m : ∀ a b, Γ(M a, (i a) ⁻¹ᵁ U b) := fun a b ↦ match b with
    | .inl t => (M a).presheaf.map (homOfLE le_top).op (s a)
    | .inr x => mo x.down a
  refine ⟨κ, U, f, m, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm le_top
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hx : x ∈ T
    · exact ⟨Sum.inl ⟨⟨x, hx⟩⟩, hUp ⟨x, hx⟩⟩
    · exact ⟨Sum.inr ⟨⟨x, hx⟩⟩, hUo ⟨x, hx⟩⟩
  · intro a b
    cases b with
    | inl t => exact hUpm t.down a
    | inr x => exact hmo x.down a
  · intro a b
    cases b with
    | inl t =>
      simp only [f, map_one, one_smul, m]
    | inr x => exact hso x.down a
  · intro b c hbc W hWb hWc
    apply hsections W
    intro x hxW hxT
    cases b with
    | inl t =>
      cases c with
      | inl t' =>
        have ht := hUpT t.down x (hWb hxW) hxT
        have ht' := hUpT t'.down x (hWc hxW) hxT
        have heq : t = t' := ULift.ext (Subtype.ext (ht.symm.trans ht'))
        exact hbc (congrArg Sum.inl heq)
      | inr y => exact hUoT y.down (hWc hxW) hxT
    | inr y => exact hUoT y.down (hWb hxW) hxT

end AlgebraicGeometry.Scheme.Modules
