/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Structure sections on a reduced scheme away from component intersections

Source: Stacks Project, Varieties Lemma 09NE, proof, first paragraph after setting T
(blueprint: lem-sc-glue-component-reduced-cover-sections).
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- Let `X` be a reduced scheme and `i a : Z a ⟶ X` finitely many closed immersions whose
images cover `X`. With `T` the union of the pairwise intersections `Z a ∩ Z b`, `a ≠ b`, the
sets `Z a \ T` are open in `X`, pairwise disjoint and cover `X \ T`, and for every open
`V ⊆ X \ T` the restriction maps `Γ(X, V) → Γ(Z a, (i a)⁻¹ V)` together give a bijection
onto the product over `a` (empty factors are the zero ring), so `X \ T` is the
scheme-theoretic union of the open subschemes `Z a \ T`.
Source: Stacks Project, Varieties Lemma 09NE, proof, first paragraph after setting T
(blueprint: lem-sc-glue-component-reduced-cover-sections).

Proof: The finite union `T` is closed. The complement of `T` together with all component
images other than `a` is exactly `Z a \ T`, so that set is open. Disjointness and coverage
follow from the definition of `T` and the covering hypothesis. For `V` disjoint from `T`,
put `U a = V ∩ (Z a \ T)`. The closed immersion restricted to `U a` is surjective onto a
reduced open subscheme, hence is an isomorphism by
`isIso_of_isClosedImmersion_of_surjective`. Its map on sections is an isomorphism, and
`(i a)⁻¹ U a = (i a)⁻¹ V`, giving a bijection `e a` from sections on `U a` to the required
component sections. Naturality factors the original section map as restriction to `U a`
followed by `e a`. Injectivity follows from sheaf separatedness. For surjectivity, pull
back the given component sections through the bijections `e a`; these sections agree on
all overlaps, since distinct opens have empty intersection. The sheaf gluing theorem
produces the desired section on `V`. The same proof covers an empty index type and empty
opens, using the unique structure-sheaf section on the empty open.
-/
theorem glue_component_reduced_cover_sections
    {X : Scheme.{u}} [IsReduced X] {ι : Type v} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a : ι, Z a ⟶ X) [∀ a : ι, IsClosedImmersion (i a)]
    (hcover : (⋃ a : ι, Set.range (i a)) = Set.univ) :
    let T : Set X := ⋃ a : ι, ⋃ b : ι, ⋃ (_ : b ≠ a), Set.range (i a) ∩ Set.range (i b)
    IsClosed T ∧
      (∀ a : ι, IsOpen (Tᶜ ∩ Set.range (i a))) ∧
      Pairwise (fun a b : ι => Disjoint (Tᶜ ∩ Set.range (i a)) (Tᶜ ∩ Set.range (i b))) ∧
      (⋃ a : ι, Tᶜ ∩ Set.range (i a)) = Tᶜ ∧
      ∀ V : X.Opens, (V : Set X) ⊆ Tᶜ →
        Function.Bijective
          (fun s : Γ(X, V) => fun a : ι => ((i a).app V).hom s :
            Γ(X, V) → ∀ a : ι, Γ(Z a, (i a) ⁻¹ᵁ V)) := by
  classical
  dsimp only
  let T : Set X := ⋃ a : ι, ⋃ b : ι, ⋃ (_ : b ≠ a), Set.range (i a) ∩ Set.range (i b)
  have hclosed (a : ι) : IsClosed (Set.range (i a)) :=
    (i a).isClosedEmbedding.isClosed_range
  have hT : IsClosed T :=
    isClosed_iUnion_of_finite fun a ↦ isClosed_iUnion_of_finite fun b ↦
      isClosed_iUnion_of_finite fun _ ↦ (hclosed a).inter (hclosed b)
  have hmem (a b : ι) (hab : b ≠ a) {x : X}
      (ha : x ∈ Set.range (i a)) (hb : x ∈ Set.range (i b)) : x ∈ T :=
    Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hab, ha, hb⟩⟩⟩
  have hopen (a : ι) : IsOpen (Tᶜ ∩ Set.range (i a)) := by
    have heq : Tᶜ ∩ Set.range (i a) =
        (T ∪ ⋃ b : ι, ⋃ (_ : b ≠ a), Set.range (i b))ᶜ := by
      ext x
      constructor
      · rintro ⟨hx, ha⟩ (h | h)
        · exact hx h
        · obtain ⟨b, hb⟩ := Set.mem_iUnion.mp h
          obtain ⟨hab, hb⟩ := Set.mem_iUnion.mp hb
          exact hx (hmem a b hab ha hb)
      · intro hx
        refine ⟨fun h ↦ hx (Or.inl h), ?_⟩
        have hc : x ∈ ⋃ b : ι, Set.range (i b) := by rw [hcover]; trivial
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hc
        by_cases hab : b = a
        · subst b
          exact hb
        · exact False.elim (hx (Or.inr
            (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hab, hb⟩⟩)))
    rw [heq]
    exact (hT.union (isClosed_iUnion_of_finite fun b ↦
      isClosed_iUnion_of_finite fun _ ↦ hclosed b)).isOpen_compl
  have hdisj : Pairwise (fun a b : ι ↦
      Disjoint (Tᶜ ∩ Set.range (i a)) (Tᶜ ∩ Set.range (i b))) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro x ha hb
    exact ha.1 (hmem a b (Ne.symm hab) ha.2 hb.2)
  have hcov : (⋃ a : ι, Tᶜ ∩ Set.range (i a)) = Tᶜ := by
    rw [← Set.inter_iUnion, hcover, Set.inter_univ]
  refine ⟨hT, hopen, hdisj, hcov, ?_⟩
  intro V hV
  let U : ι → X.Opens := fun a ↦
    ⟨(V : Set X) ∩ (Tᶜ ∩ Set.range (i a)), V.isOpen.inter (hopen a)⟩
  have hUV (a : ι) : U a ≤ V := fun _ hx ↦ hx.1
  have hUc : V ≤ ⨆ a, U a := by
    intro x hx
    change x ∈ ((⨆ a, U a : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iSup]
    have hc : x ∈ ⋃ a, Tᶜ ∩ Set.range (i a) := by rw [hcov]; exact hV hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hc
    exact Set.mem_iUnion.mpr ⟨a, hx, ha⟩
  have hpre (a : ι) : (i a) ⁻¹ᵁ U a = (i a) ⁻¹ᵁ V := by
    ext x
    exact ⟨fun hx ↦ hx.1, fun hx ↦ ⟨hx, hV hx, ⟨x, rfl⟩⟩⟩
  have hiso (a : ι) : IsIso ((i a).app (U a)) := by
    have : Surjective (i a ∣_ U a) := ⟨by
      intro x
      obtain ⟨y, hy⟩ := x.2.2.2
      refine ⟨⟨y, ?_⟩, ?_⟩
      · change i a y ∈ U a
        rw [hy]
        exact x.2
      · apply Subtype.ext
        exact (morphismRestrict_base_coe _ _ _).trans hy⟩
    have : IsIso (i a ∣_ U a) := isIso_of_isClosedImmersion_of_surjective _
    have : IsIso (((i a).resLE (U a) ((i a) ⁻¹ᵁ U a) le_rfl).appTop) := by
      simpa [Scheme.Hom.resLE] using
        (inferInstance : IsIso ((i a ∣_ U a).appTop))
    simpa only [Scheme.Hom.appLE_eq_app] using
      (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms CommRingCat)
        (arrowResLEAppIso (i a) (U a) ((i a) ⁻¹ᵁ U a) le_rfl)).mp this
  have he (a : ι) : (i a) ⁻¹ᵁ V ≤ (i a) ⁻¹ᵁ U a := (hpre a).ge
  let e (a : ι) := (i a).appLE (U a) ((i a) ⁻¹ᵁ V) (he a)
  have hebij (a : ι) : Function.Bijective (e a).hom := by
    have : IsIso (e a) := by
      dsimp [e, Scheme.Hom.appLE]
      have : IsIso ((Z a).presheaf.map (homOfLE (he a)).op) := by
        have : IsIso (homOfLE (he a)) := by
          have heq : homOfLE (he a) = eqToHom (hpre a).symm := Subsingleton.elim _ _
          rw [heq]
          infer_instance
        infer_instance
      infer_instance
    exact ConcreteCategory.bijective_of_isIso (e a)
  have hfactor (a : ι) : X.presheaf.map (homOfLE (hUV a)).op ≫ e a = (i a).app V := by
    simp only [e, Scheme.Hom.map_appLE, Scheme.Hom.appLE_eq_app]
  constructor
  · intro s t hst
    apply X.sheaf.eq_of_locally_eq' U V (fun a ↦ homOfLE (hUV a)) hUc s t
    intro a
    apply (hebij a).1
    change (e a).hom ((X.presheaf.map (homOfLE (hUV a)).op).hom s) =
      (e a).hom ((X.presheaf.map (homOfLE (hUV a)).op).hom t)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, hfactor]
    exact congrFun hst a
  · intro t
    choose sf hsf using fun a ↦ (hebij a).2 (t a)
    have hcompatible : TopCat.Presheaf.IsCompatible X.presheaf U sf := by
      intro a b
      by_cases hab : a = b
      · subst b
        congr 1
      · have hbot : U a ⊓ U b = ⊥ := by
          ext x
          exact ⟨fun hx ↦ (Set.disjoint_left.mp (hdisj hab) hx.1.2 hx.2.2).elim,
            fun hx ↦ hx.elim⟩
        have : Subsingleton Γ(X, U a ⊓ U b) := by rw [hbot]; infer_instance
        exact Subsingleton.elim _ _
    obtain ⟨s, hs, _⟩ := X.sheaf.existsUnique_gluing' U V
      (fun a ↦ homOfLE (hUV a)) hUc sf hcompatible
    refine ⟨s, funext fun a ↦ ?_⟩
    change ((i a).app V).hom s = t a
    rw [← hfactor a, CommRingCat.comp_apply]
    change (e a).hom ((X.sheaf.obj.map (homOfLE (hUV a)).op) s) = t a
    rw [hs a]
    exact hsf a

end AlgebraicGeometry
