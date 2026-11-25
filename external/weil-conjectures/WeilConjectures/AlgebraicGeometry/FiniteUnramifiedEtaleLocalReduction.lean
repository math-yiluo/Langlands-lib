/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Finite-fibre enumeration and application of the unramified-local decomposition
produce the input required by `finite_coproduct_of_unramified_decomposition`.
(blueprint: lem-weil-pbc-finite-unramified-etale-local-input). -/
theorem finite_decomposition_input
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [LocallyOfFiniteType f]
    [IsOpenImmersion (pullback.diagonal f)] (x : X) :
    ∃ (n : ℕ) (pts : Fin n → Y), (∀ i, f.base (pts i) = x) ∧
      (∃ (U : Scheme.{u}) (g : U ⟶ X) (u : U),
        Etale g ∧ g.base u = x ∧
        ∃ (m : Fin n → ℕ) (W : (pullback f g).Opens)
          (V : (Σ i : Fin n, Fin (m i)) → (pullback f g).Opens),
          IsClosed (W : Set ↥(pullback f g)) ∧
          (∀ a, IsClosed (V a : Set ↥(pullback f g))) ∧
          Pairwise (fun a b ↦ Disjoint (V a) (V b)) ∧
          (∀ a, Disjoint W (V a)) ∧ W ⊔ iSup V = ⊤ ∧
          (∀ a, IsClosedImmersion ((V a).ι ≫ pullback.snd f g) ∧
            u ∈ Set.range (((V a).ι ≫ pullback.snd f g).base)) ∧
          (∀ p : ↥(pullback f g), p ∈ W →
            (pullback.snd f g).base p = u →
            ∀ i, (pullback.fst f g).base p ≠ pts i)) := by
  classical
  let F := ↥(f ⁻¹' {x})
  have hF : Finite F := by
    have hf := f.finite_preimage_singleton x
    exact hf.to_subtype
  let : Fintype F := Fintype.ofFinite F
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  let pts : Fin (Fintype.card F) → Y := fun i ↦ (e i).val
  have hpts : ∀ i, f.base (pts i) = x := fun i ↦ (e i).property
  refine ⟨Fintype.card F, pts, hpts, ?_⟩
  have hunramified : ∀ i, ∃ O : Y.Opens, pts i ∈ O ∧
      LocallyOfFiniteType (O.ι ≫ f) ∧ IsOpenImmersion (pullback.diagonal (O.ι ≫ f)) := by
    intro i
    have : FormallyUnramified f := inferInstance
    have : FormallyUnramified ((⊤ : Y.Opens).ι ≫ f) :=
      MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
    refine ⟨⊤, trivial, inferInstance, ?_⟩
    exact FormallyUnramified.isOpenImmersion_diagonal _
  obtain ⟨U, g, u, hg, hu, m, W, V, hW, hV, hd, hWd, hcover, hclosed, hrest, _⟩ :=
    exists_etale_closed_immersion_decomposition_of_unramified_at_points
      f x (Fintype.card F) pts hpts hunramified
  exact ⟨U, g, u, hg, hu, m, W, V, hW, hV, hd, hWd, hcover, hclosed, hrest⟩


/-- Shrinking and reindexing a finite clopen decomposition removes its
remainder and yields the finite coproduct presentation used in Lemma 04HJ.
This packages the open shrinking, base change, and coproduct bookkeeping.
(blueprint: lem-weil-pbc-finite-unramified-etale-local-reduction). -/
theorem finite_coproduct_of_unramified_decomposition
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [LocallyOfFiniteType f]
    [IsOpenImmersion (pullback.diagonal f)] (x : X) (n : ℕ) (pts : Fin n → Y)
    (hpts : ∀ i, f.base (pts i) = x)
    (h : ∃ (U : Scheme.{u}) (g : U ⟶ X) (u : U),
      Etale g ∧ g.base u = x ∧
      ∃ (m : Fin n → ℕ) (W : (pullback f g).Opens)
        (V : (Σ i : Fin n, Fin (m i)) → (pullback f g).Opens),
        IsClosed (W : Set ↥(pullback f g)) ∧
        (∀ a, IsClosed (V a : Set ↥(pullback f g))) ∧
        Pairwise (fun a b ↦ Disjoint (V a) (V b)) ∧
        (∀ a, Disjoint W (V a)) ∧ W ⊔ iSup V = ⊤ ∧
        (∀ a, IsClosedImmersion ((V a).ι ≫ pullback.snd f g) ∧
          u ∈ Set.range (((V a).ι ≫ pullback.snd f g).base)) ∧
        (∀ p : ↥(pullback f g), p ∈ W → (pullback.snd f g).base p = u →
          ∀ i, (pullback.fst f g).base p ≠ pts i) ) :
    ∃ (U : Scheme.{u}) (g : U ⟶ X) (u : U),
      Etale g ∧ g.base u = x ∧
      ∃ (J : Type u) (V : J → Scheme.{u}) (ι : ∀ j, V j ⟶ pullback f g),
        Finite J ∧
        Nonempty (IsColimit (Cofan.mk (pullback f g) ι)) ∧
        (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j)) ∧
        (∀ j, IsClosedImmersion (ι j ≫ pullback.snd f g)) := by
  -- The supplied list need not exhaust the fibre. Enumerate the whole fibre instead.
  have _ := hpts
  have _ := h
  classical
  let F := ↥(f ⁻¹' {x})
  have hF : Finite F := by
    have hf := f.finite_preimage_singleton x
    exact hf.to_subtype
  let : Fintype F := Fintype.ofFinite F
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  let pts : Fin (Fintype.card F) → Y := fun i ↦ (e i).val
  have hpts : ∀ i, f.base (pts i) = x := fun i ↦ (e i).property
  have hunramified : ∀ i, ∃ O : Y.Opens, pts i ∈ O ∧
      LocallyOfFiniteType (O.ι ≫ f) ∧ IsOpenImmersion (pullback.diagonal (O.ι ≫ f)) := by
    intro i
    have : FormallyUnramified f := inferInstance
    have : FormallyUnramified ((⊤ : Y.Opens).ι ≫ f) :=
      MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
    refine ⟨⊤, trivial, inferInstance, ?_⟩
    exact FormallyUnramified.isOpenImmersion_diagonal _
  obtain ⟨U, g, u, hg, hu, m, W, V, hW, hV, hd, hWd, hcover, hclosed, hrest, hexhaust⟩ :=
    exists_etale_closed_immersion_decomposition_of_unramified_at_points
      f x (Fintype.card F) pts hpts hunramified
  have hfull : ∀ y : Y, f.base y = x ↔ ∃ i, y = pts i := by
    intro y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := e.surjective ⟨y, hy⟩
      exact ⟨i, (congrArg Subtype.val hi).symm⟩
    · rintro ⟨i, rfl⟩
      exact hpts i
  have hnone := hexhaust hfull
  let p := pullback.snd f g
  let Z : Set U := p.base '' (W : Set ↥(pullback f g))
  have hZ : IsClosed Z := p.isClosedMap _ hW
  let O : U.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have huO : u ∈ O := by
    rintro ⟨z, hzW, hzu⟩
    exact hnone z hzW hzu
  let g' := O.ι ≫ g
  let q := pullback.snd f g'
  let k : pullback f g' ⟶ pullback f g :=
    pullback.map f g' f g (𝟙 Y) O.ι (𝟙 X) (by simp) (by simp [g'])
  have hkfst : k ≫ pullback.fst f g = pullback.fst f g' := by simp [k]
  have hkp : k ≫ p = q ≫ O.ι := by simp [k, p, q]
  have H : IsPullback k q p O.ι := by
    apply IsPullback.of_right _ hkp (IsPullback.of_hasPullback f g)
    simpa only [hkfst] using (IsPullback.of_hasPullback f g')
  let P : (Σ i : Fin (Fintype.card F), Fin (m i)) → (pullback f g').Opens :=
    fun a ↦ k ⁻¹ᵁ V a
  have hWempty : k ⁻¹ᵁ W = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    have heq : p.base (k.base z) = O.ι.base (q.base z) :=
      congrArg (fun t ↦ t.base z) hkp
    have hzZ : p.base (k.base z) ∈ Z := ⟨k.base z, hz, rfl⟩
    rw [heq] at hzZ
    exact (q.base z).property hzZ
  have hPcover : iSup P = ⊤ := by
    have hc := congrArg (fun T ↦ k ⁻¹ᵁ T) hcover
    simpa only [Scheme.Hom.preimage_sup, Scheme.Hom.preimage_iSup,
      Scheme.Hom.preimage_top, hWempty, bot_sup_eq] using hc
  have hPdisj : Pairwise (fun a b ↦ Disjoint (P a) (P b)) := by
    intro a b hab
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, (hd hab).eq_bot,
      Scheme.Hom.preimage_bot]
  have hPclosed (a) : IsClosed (P a : Set ↥(pullback f g')) :=
    (hV a).preimage k.continuous
  have hPimm (a) : IsClosedImmersion ((P a).ι) := by
    apply IsClosedImmersion.of_isPreimmersion
    simpa only [Scheme.Opens.range_ι] using hPclosed a
  have hPbase (a) : IsClosedImmersion ((P a).ι ≫ q) := by
    let r := k.resLE (V a) (P a) le_rfl
    have Hr : IsPullback r (P a).ι (V a).ι k := by
      apply IsOpenImmersion.isPullback
      · simp [r]
      · simp [P]
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (Hr.paste_vert H) (hclosed a).1
  have : Etale g := hg
  refine ⟨O.toScheme, g', ⟨u, huO⟩, inferInstance, ?_,
    ULift.{u} (Σ i : Fin (Fintype.card F), Fin (m i)),
    (fun a ↦ (P a.down).toScheme), (fun a ↦ (P a.down).ι), inferInstance, ?_, ?_, ?_⟩
  · exact hu
  · apply nonempty_isColimit_cofanMk_of
    · simpa using hPcover
    · intro a b hab
      simpa using hPdisj (show a.down ≠ b.down from fun he ↦ hab (congrArg ULift.up he))
  · intro a
    exact ⟨inferInstance, hPimm a.down⟩
  · intro a
    exact hPbase a.down


end AlgebraicGeometry
