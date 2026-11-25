/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends
import WeilConjectures.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

private theorem finite_components_homeomorph {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (h : A ≃ₜ B)
    (hf : (irreducibleComponents B).Finite) : (irreducibleComponents A).Finite := by
  have hsub : (fun C : Set A ↦ h '' C) '' irreducibleComponents A ⊆
      irreducibleComponents B := by
    rintro _ ⟨C, hC, rfl⟩
    have hc := preimage_mem_irreducibleComponents hC h.symm.isOpenEmbedding
      (by rw [h.symm.surjective.range_eq, Set.inter_univ]; exact hC.1.1)
    simpa only [h.preimage_symm] using hc
  exact (hf.subset hsub).of_finite_image
    ((Set.image_injective.mpr h.injective).injOn)

private theorem component_finite_stabilizer {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hf : (irreducibleComponents
      ↥(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap k (SeparableClosure k)))))).Finite)
    (C : Set ↥(pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap k (SeparableClosure k))))))
    (hC : C ∈ irreducibleComponents _) :
    ∃ L : IntermediateField k (SeparableClosure k), Module.Finite k L ∧
      ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
        (∀ x : L, σ (x : SeparableClosure k) = x) →
        (baseChangeMap f (specAlgEquivOver σ)) '' C = C := by
  let Y := pullback f (Spec.map (CommRingCat.ofHom
    (algebraMap k (SeparableClosure k))))
  let U : Set Y := (⋃₀ (irreducibleComponents Y \ {C}))ᶜ
  have hU : IsOpen U := by
    simpa only [U, Set.sUnion_eq_biUnion] using (hf.sdiff.isClosed_biUnion fun D hD ↦
      isClosed_of_mem_irreducibleComponents D hD.1).isOpen_compl
  have hcl : closure U = C := closure_sUnion_irreducibleComponents_sdiff_singleton hf C hC
  have hUne : U.Nonempty := by
    rw [← hcl] at hC
    exact hC.1.1.of_closure
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx hU
  have hUC : U ⊆ C := hcl ▸ subset_closure
  have hVC : (V : Set Y) ⊆ C := hVU.trans hUC
  have hVCcl : closure (V : Set Y) = C := by
    apply subset_antisymm
    · exact closure_minimal hVC (isClosed_of_mem_irreducibleComponents C hC)
    · have h := subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 V.isOpen
        (show (C ∩ (V : Set Y)).Nonempty from ⟨x, hVC hxV, hxV⟩)
      simpa only [Set.inter_eq_right.mpr hVC] using h
  obtain ⟨hiso, -, L, hL, -, -, -, -, -, hfix⟩ :=
    galois_baseChange_qc_open_descends k (SeparableClosure k) X f V hV.isCompact
  refine ⟨L, hL, ?_⟩
  intro σ hσ
  have := hiso σ
  let e := (baseChangeMap f (specAlgEquivOver σ)).homeomorph
  calc
    (baseChangeMap f (specAlgEquivOver σ)) '' C = e '' closure (V : Set Y) := by
      rw [hVCcl]; rfl
    _ = closure (e '' (V : Set Y)) := e.image_closure _
    _ = C := by
      change closure ((baseChangeMap f (specAlgEquivOver σ)) '' V.carrier) = C
      rw [hfix σ hσ]
      exact hVCcl

private theorem components_finite_stabilizer {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hf : (irreducibleComponents
      ↥(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap k (SeparableClosure k)))))).Finite) :
    ∃ L : IntermediateField k (SeparableClosure k), Module.Finite k L ∧
      ∀ C ∈ irreducibleComponents
        ↥(pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap k (SeparableClosure k))))),
        ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
          (∀ x : L, σ (x : SeparableClosure k) = x) →
          (baseChangeMap f (specAlgEquivOver σ)) '' C = C := by
  let Y := pullback f (Spec.map (CommRingCat.ofHom
    (algebraMap k (SeparableClosure k))))
  have aux (S : Set (Set Y)) (hS : S.Finite) : S ⊆ irreducibleComponents Y →
      ∃ L : IntermediateField k (SeparableClosure k), Module.Finite k L ∧
        ∀ C ∈ S, ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
          (∀ x : L, σ (x : SeparableClosure k) = x) →
          (baseChangeMap f (specAlgEquivOver σ)) '' C = C := by
    induction S, hS using Set.Finite.induction_on with
    | empty =>
      intro _
      exact ⟨⊥, inferInstance, by simp⟩
    | @insert C S hS hCS ih =>
      intro hs
      obtain ⟨L₁, h₁, hc⟩ := component_finite_stabilizer f hf C (hs (by simp))
      obtain ⟨L₂, h₂, hcs⟩ := ih (Set.Subset.trans (Set.subset_insert _ _) hs)
      have := h₁
      have := h₂
      refine ⟨L₁ ⊔ L₂, inferInstance, ?_⟩
      intro D hD σ hσ
      rcases Set.mem_insert_iff.mp hD with rfl | hD
      · apply hc σ
        intro x
        exact hσ ⟨x, (show L₁ ≤ L₁ ⊔ L₂ from le_sup_left) x.property⟩
      · apply hcs D hD σ
        intro x
        exact hσ ⟨x, (show L₂ ≤ L₁ ⊔ L₂ from le_sup_right) x.property⟩
  exact aux _ hf Set.Subset.rfl

/-- All components over a separable closure simultaneously descend to closed subsets over
one finite intermediate field.

Source: Stacks Project, Tag 04KZ (1),(2), and Tag 054R, proof.
Proof: for each geometric component choose an affine open U of X meeting it after base
change. The coordinate ring of U is finite type over k, so its base change is noetherian.
The minimal prime defining the component on this chart has finitely many generators.
Write each generator as a finite sum of tensors and adjoin their ksep coefficients for
all components. There are finitely many coefficients, and algebraicity makes their
intermediate field L finite over k. Every automorphism fixing L preserves each chosen
chart and fixes the ideal generators, hence fixes the component on that chart. Its
closure is the entire component, which is therefore fixed. Since ksep/L is algebraic,
normal and separable, it is Galois, even if L/k is not normal.
Descent of invariant closed subsets (Stacks Tag 038B, applied over L) supplies closed
subsets of X_L whose full preimages are those components. The projection is surjective
by faithful flatness of field extension. The pullback tower isomorphism identifies the
iterated base change with X_ksep and transports the given finiteness of components.
For empty X take the bottom field and use the vacuous component assertion.
(blueprint: new-lem-sbc-finite-field-closed-component-descent) -/
theorem exists_finite_intermediateField_closed_component_descent {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hfinite : (irreducibleComponents
      ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))))).Finite) :
    ∃ L : IntermediateField k (SeparableClosure k),
      Module.Finite k L ∧
      let Z := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      let Y := pullback
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
        (Spec.map (CommRingCat.ofHom L.subtype))
      let p : Y ⟶ Z := pullback.fst
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
        (Spec.map (CommRingCat.ofHom L.subtype))
      Function.Surjective p ∧ (irreducibleComponents ↥Y).Finite ∧
        ∀ C ∈ irreducibleComponents ↥Y,
          ∃ A : Set Z, IsClosed A ∧ p ⁻¹' A = C := by
  -- Compact-open descent fixes a dense affine open in each component; taking closures
  -- avoids the finite-type minimal-prime construction in the original proof plan.
  obtain ⟨L, hL, hfix⟩ := components_finite_stabilizer f hfinite
  refine ⟨L, hL, ?_⟩
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let g' : Spec (.of (SeparableClosure k)) ⟶ Spec (.of L) :=
    Spec.map (CommRingCat.ofHom (algebraMap L (SeparableClosure k)))
  let gΩ := Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))
  let Z := pullback f g
  let fL := pullback.snd f g
  let Y := pullback fL g'
  let p := pullback.fst fL g'
  have hg : g' ≫ g = gΩ := by
    simp only [g', g, gΩ, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  let e : Y ≅ pullback f gΩ :=
    pullbackLeftPullbackSndIso f g g' ≪≫ pullback.congrHom rfl hg
  have hefst : e.hom ≫ pullback.fst f gΩ = p ≫ pullback.fst f g := by
    simp [e, p, fL]
  have hesnd : e.hom ≫ pullback.snd f gΩ = pullback.snd fL g' := by
    simp [e, fL]
  have haction (σ : SeparableClosure k ≃ₐ[L] SeparableClosure k) :
      baseChangeMap fL (specAlgEquivOver σ) ≫ e.hom =
        e.hom ≫ baseChangeMap f (specAlgEquivOver (σ.restrictScalars k)) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hefst]
      simp only [baseChangeMap, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.comp_id, g', gΩ, g, fL, p, Over.mk_hom]
      simpa only [g', gΩ, g, fL, p] using hefst.symm
    · simp only [Category.assoc, hesnd]
      simp only [baseChangeMap, pullback.map, pullback.lift_snd,
        g', gΩ, g, fL, Over.mk_hom]
      rw [← Category.assoc, hesnd]
      rfl
  have : Surjective g' := ⟨fun x ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  refine ⟨p.surjective, finite_components_homeomorph e.hom.homeomorph hfinite, ?_⟩
  intro C hC
  let : Z.Over (Spec (.of L)) := ⟨fL⟩
  apply exists_closed_subset_of_galois_invariant L (SeparableClosure k) Z C
    (isClosed_of_mem_irreducibleComponents C hC)
  intro σ
  have hD : e.hom '' C ∈ irreducibleComponents ↥(pullback f gΩ) := by
    have hc := preimage_mem_irreducibleComponents hC e.hom.homeomorph.symm.isOpenEmbedding
      (by rw [e.hom.homeomorph.symm.surjective.range_eq, Set.inter_univ]; exact hC.1.1)
    simpa only [e.hom.homeomorph.preimage_symm, Scheme.Hom.homeomorph_apply] using hc
  have hinv := hfix _ hD (σ.restrictScalars k) (fun x ↦ σ.commutes x)
  apply Set.image_injective.mpr e.hom.homeomorph.injective
  change e.hom '' ((baseChangeMap fL (specAlgEquivOver σ)) '' C) = e.hom '' C
  rw [Set.image_image]
  have hcomp : (fun x ↦ e.hom (baseChangeMap fL (specAlgEquivOver σ) x)) =
      (fun x ↦ baseChangeMap f (specAlgEquivOver (σ.restrictScalars k)) (e.hom x)) := by
    funext x
    exact congrArg (fun t ↦ t x) (haction σ)
  change (fun x ↦ e.hom (baseChangeMap fL (specAlgEquivOver σ) x)) '' C = e.hom '' C
  rw [hcomp]
  simpa only [gΩ, Over.mk_hom, Set.image_image, Function.comp_def] using hinv

end AlgebraicGeometry
