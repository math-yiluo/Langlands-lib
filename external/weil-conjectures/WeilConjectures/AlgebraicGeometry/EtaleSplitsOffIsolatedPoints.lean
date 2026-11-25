/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteMultiplePointsElementary
import all WeilConjectures.AlgebraicGeometry.FinitePiecePersistence
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Splitting off isolated fibre points in an elementary étale neighbourhood

Source: Stacks Project, More on Morphisms, Lemma 37.41.4, Tag 02LN
(blueprint: lem-weil-pbc-etale-splits-off-isolated-points-technical).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Shrink the base by deleting the closed images of the pairwise intersections.
Finite open pieces in a separated scheme are closed; their finite maps are closed.
Uniqueness of the marked fibre points shows that these images miss the base point.
The persistence lemma retains the finite pieces and their residue-field maps (Stacks 02LN). -/
private theorem disjoint_finite_pieces_after_shrinking
    {X S U : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (φ : U ⟶ S) (t : U)
    (n : ℕ) (x : Fin n → X) (hx : Function.Injective x)
    (hxt : ∀ i, f (x i) = φ t)
    (V : Fin n → (pullback f φ).Opens) (v : (i : Fin n) → (V i).toScheme)
    (hV : ∀ i, IsFinite ((V i).ι ≫ pullback.snd f φ) ∧
      ((V i).ι ≫ pullback.snd f φ) (v i) = t ∧
      (∀ w : (V i).toScheme, ((V i).ι ≫ pullback.snd f φ) w = t → w = v i) ∧
      ((V i).ι ≫ pullback.fst f φ) (v i) = x i ∧
      IsIso (((V i).ι ≫ pullback.fst f φ).residueFieldMap (v i))) :
    ∃ (B : U.Opens) (htB : t ∈ B)
      (V' : Fin n → (pullback f (B.ι ≫ φ)).Opens)
      (v' : (i : Fin n) → (V' i).toScheme),
      (∀ i, IsClosed (V' i : Set ↥(pullback f (B.ι ≫ φ)))) ∧
      (∀ i j, i ≠ j → Disjoint (V' i) (V' j)) ∧
      (∀ i, IsFinite ((V' i).ι ≫ pullback.snd f (B.ι ≫ φ)) ∧
        ((V' i).ι ≫ pullback.snd f (B.ι ≫ φ)) (v' i) = (⟨t, htB⟩ : B.toScheme) ∧
        (∀ w : (V' i).toScheme,
          ((V' i).ι ≫ pullback.snd f (B.ι ≫ φ)) w = (⟨t, htB⟩ : B.toScheme) →
            w = v' i) ∧
        ((V' i).ι ≫ pullback.fst f (B.ι ≫ φ)) (v' i) = x i ∧
        IsIso (((V' i).ι ≫ pullback.fst f (B.ι ≫ φ)).residueFieldMap (v' i))) := by
  classical
  let q := pullback.snd f φ
  let π := fun i ↦ (V i).ι ≫ q
  have hclosed (i : Fin n) : IsClosed (V i : Set ↥(pullback f φ)) := by
    have : IsFinite (π i) := (hV i).1
    have : IsProper (V i).ι := IsProper.of_comp (V i).ι q
    simpa only [Scheme.Opens.range_ι] using (V i).ι.isClosedMap.isClosed_range
  let Z : Fin n → Fin n → Set U := fun i j ↦ q '' ((V i : Set _) ∩ (V j : Set _))
  have hZclosed (i j : Fin n) : IsClosed (Z i j) := by
    have : IsFinite (π i) := (hV i).1
    have heq : Z i j = π i '' ((V i).ι ⁻¹' (V j : Set _)) := by
      change q '' ((V i : Set _) ∩ (V j : Set _)) =
        (q ∘ (V i).ι) '' ((V i).ι ⁻¹' (V j : Set _))
      rw [Set.image_comp, Set.image_preimage_eq_range_inter, Scheme.Opens.range_ι]
    rw [heq]
    exact (π i).isClosedMap _ ((hclosed j).preimage (V i).ι.continuous)
  have htZ (i j : Fin n) (hij : i ≠ j) : t ∉ Z i j := by
    rintro ⟨p, ⟨hpi, hpj⟩, hpt⟩
    have hi : (⟨p, hpi⟩ : (V i).toScheme) = v i := (hV i).2.2.1 _ hpt
    have hj : (⟨p, hpj⟩ : (V j).toScheme) = v j := (hV j).2.2.1 _ hpt
    apply hij
    apply hx
    have hxi : pullback.fst f φ p = x i :=
      (congrArg (fun w ↦ ((V i).ι ≫ pullback.fst f φ) w) hi).trans
        (hV i).2.2.2.1
    have hxj : pullback.fst f φ p = x j :=
      (congrArg (fun w ↦ ((V j).ι ≫ pullback.fst f φ) w) hj).trans
        (hV j).2.2.2.1
    exact hxi.symm.trans hxj
  let D : Fin n → Fin n → U.Opens := fun i j ↦
    if i = j then ⊤ else ⟨(Z i j)ᶜ, (hZclosed i j).isOpen_compl⟩
  let B : U.Opens := ⨅ i, ⨅ j, D i j
  have htB : t ∈ B := by
    change t ∈ (↑B : Set U)
    simp only [B, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro i j
    by_cases hij : i = j
    · simp [D, hij]
    · simpa [D, hij] using htZ i j hij
  let φ' := B.ι ≫ φ
  let k : pullback f φ' ⟶ pullback f φ :=
    pullback.map f φ' f φ (𝟙 X) B.ι (𝟙 S) (by simp) (by simp [φ'])
  have hkp : k ≫ pullback.fst f φ = pullback.fst f φ' := by simp [k]
  have hkq : k ≫ q = pullback.snd f φ' ≫ B.ι := by simp [k, q]
  have hpersist (i : Fin n) := finitePiece_persistence_of_isIso_residueFieldMap
    f φ t (x i) (hxt i) (V i) (v i) (hV i).1 (hV i).2.1 (hV i).2.2.1
    (hV i).2.2.2.1 (hV i).2.2.2.2 B.ι (⟨t, htB⟩ : B.toScheme) rfl
    (inferInstance) k hkp hkq
  choose v' hv' using fun i ↦ (hpersist i).2
  refine ⟨B, htB, fun i ↦ k ⁻¹ᵁ V i, v', ?_, ?_, ?_⟩
  · intro i
    exact (hclosed i).preimage k.continuous
  · intro i j hij
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro p hp
    have hpZ : q (k p) ∈ Z i j := ⟨k p, hp, rfl⟩
    have hpoint : q (k p) = B.ι (pullback.snd f φ' p) :=
      congrArg (fun h ↦ h p) hkq
    have hpD : B.ι (pullback.snd f φ' p) ∈ D i j :=
      ((iInf_le _ i).trans (iInf_le _ j) : B ≤ D i j)
        (pullback.snd f φ' p).property
    rw [hpoint] at hpZ
    exact (show B.ι (pullback.snd f φ' p) ∉ Z i j from
      by simpa [D, hij] using hpD) hpZ
  · intro i
    exact ⟨(hpersist i).1, (hv' i).1, (hv' i).2.1,
      (hv' i).2.2.1, (hv' i).2.2.2.1⟩

/-- Source: Stacks Project, More on Morphisms, Tag 02LN
(blueprint: lem-weil-pbc-etale-splits-off-isolated-points-technical).
A separated locally finite type morphism splits off finite disjoint open pieces through any
finite family of distinct isolated fibre points after an elementary étale base change.

Proof: Apply `lem-weil-pbc-etale-local-finite-multiple-points-elementary` (Tag 02LL)
to obtain the elementary neighbourhood and finite open pieces with their unique fibre points
and residue-field isomorphisms. By `lem-weil-pbc-separated-base-change` the base-changed
morphism is separated. Each finite piece is proper by
`lem-weil-pbc-finite-morphism-permanence`; its inclusion is proper by
`lem-weil-pbc-proper-over-separated`; its range is closed because proper maps are closed.
Pairwise intersections are closed in the finite pieces; their images in the base are closed
and avoid the distinguished point, since the original points are distinct. Remove these
finitely many images from the base. The retained properties follow from
`lem-weil-pbc-elementary-etale-finite-piece-persistence`, and étaleness from
`definition-torsion-sheaves--3`. The pieces are now disjoint; their complement
is the open and closed `W`. For `n = 0` the union is empty and `W` is the whole
pullback. Finally `lem-weil-pbc-fibre-product-points` identifies points above
`(x i, t)` with primes of the residue-field tensor product. Since the neighbourhood has
trivial residue extension, this tensor product is a field with a unique prime. Thus a point
in `W` above this pair would equal the selected point of `V i`, contradicting disjointness. -/
theorem exists_etale_splits_off_isolated_points
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsSeparated f]
    (s : S) (n : ℕ) (x : Fin n → X) (h_distinct : Function.Injective x)
    (h_over : ∀ i : Fin n, f (x i) = s)
    (h_isolated : ∀ i : Fin n, IsOpen ({f.asFiber (x i)} : Set (f.fiber (f (x i))))) :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S) (t : U),
      Etale φ ∧ φ t = s ∧ IsIso (φ.residueFieldMap t) ∧
      ∃ (W : (pullback φ f).Opens) (V : Fin n → (pullback φ f).Opens),
        (∀ i : Fin n, Disjoint W (V i)) ∧
        (∀ i j : Fin n, i ≠ j → Disjoint (V i) (V j)) ∧
        W ⊔ (⨆ i : Fin n, V i) = ⊤ ∧
        (∀ i : Fin n, IsFinite ((V i).ι ≫ pullback.fst φ f)) ∧
        (∀ i : Fin n, ∃ v : (V i).toScheme,
          ((V i).ι ≫ pullback.fst φ f) v = t ∧
          (∀ v' : (V i).toScheme, ((V i).ι ≫ pullback.fst φ f) v' = t → v' = v) ∧
          ((V i).ι ≫ pullback.snd φ f) v = x i ∧
          IsIso (((V i).ι ≫ pullback.snd φ f).residueFieldMap v)) ∧
        (∀ w : W.toScheme, (W.ι ≫ pullback.fst φ f) w = t →
          ∀ i : Fin n, (W.ι ≫ pullback.snd φ f) w ≠ x i) := by
  classical
  obtain ⟨U, φ, t, hφ, ht, hres, V, v, hV⟩ :=
    exists_etale_local_finite_multiple_points_elementary f s n x h_over h_isolated
  obtain ⟨B, htB, V', v', hclosed, hdisj, hpieces⟩ :=
    disjoint_finite_pieces_after_shrinking f φ t n x h_distinct
      (fun i ↦ (h_over i).trans ht.symm) V v hV
  have : Etale φ := hφ
  have : IsIso (φ.residueFieldMap t) := hres
  let φ' := B.ι ≫ φ
  let t' : B.toScheme := ⟨t, htB⟩
  have ht' : φ' t' = s := ht
  have hres' : IsIso (φ'.residueFieldMap t') := by
    rw [Scheme.residueFieldMap_comp]
    change IsIso (φ.residueFieldMap t ≫ B.ι.residueFieldMap t')
    infer_instance
  let W : (pullback f φ').Opens :=
    ⟨(⋃ i, (V' i : Set ↥(pullback f φ')))ᶜ,
      (isClosed_iUnion_of_finite hclosed).isOpen_compl⟩
  have hWV (i : Fin n) : Disjoint W (V' i) := by
    apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro p hp
    exact hp.1 (Set.mem_iUnion.mpr ⟨i, hp.2⟩)
  have hcover : W ⊔ (⨆ i, V' i) = ⊤ := by
    ext p
    change (p ∉ ⋃ i, (V' i : Set ↥(pullback f φ')) ∨ p ∈ ⨆ i, V' i) ↔ True
    simp only [Set.mem_iUnion, TopologicalSpace.Opens.mem_iSup]
    tauto
  have havoid (w : W.toScheme)
      (hw : (W.ι ≫ pullback.snd f φ') w = t') (i : Fin n) :
      (W.ι ≫ pullback.fst f φ') w ≠ x i := by
    intro hwx
    have heq : W.ι w = (V' i).ι (v' i) := by
      apply pullback_point_unique f φ'
      · exact hwx.trans (hpieces i).2.2.2.1.symm
      · exact hw.trans (hpieces i).2.1.symm
      · have hpt : pullback.snd f φ' ((V' i).ι (v' i)) = t' :=
          (hpieces i).2.1
        rw [hpt]
        exact hres'
    have hm : W.ι w ∈ V' i := heq ▸ (v' i).property
    exact w.property (Set.mem_iUnion.mpr ⟨i, hm⟩)
  -- Reverse the two pullback factors to match the public statement.
  let e := pullbackSymmetry φ' f
  let W'' := e.hom ⁻¹ᵁ W
  let V'' := fun i ↦ e.hom ⁻¹ᵁ V' i
  let d := fun i ↦ e.hom.preimageIso (V' i)
  have hq (i : Fin n) :
      (V'' i).ι ≫ pullback.fst φ' f = (d i).hom ≫ (V' i).ι ≫ pullback.snd f φ' := by
    simp [V'', d, e]
  have hp (i : Fin n) :
      (V'' i).ι ≫ pullback.snd φ' f = (d i).hom ≫ (V' i).ι ≫ pullback.fst f φ' := by
    simp [V'', d, e]
  refine ⟨B.toScheme, φ', t', inferInstance, ht', hres', W'', V'', ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro i
    have hi := disjoint_iff.mp (hWV i)
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, hi]
    rfl
  · intro i j hij
    have hi := disjoint_iff.mp (hdisj i j hij)
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, hi]
    rfl
  · rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_sup, hcover]
    rfl
  · intro i
    have : IsFinite ((V' i).ι ≫ pullback.snd f φ') := (hpieces i).1
    rw [hq]
    infer_instance
  · intro i
    let z := (d i).inv (v' i)
    have hz : (d i).hom z = v' i := by simp [z, ← Scheme.Hom.comp_apply]
    refine ⟨z, ?_, ?_, ?_, ?_⟩
    · rw [hq, Scheme.Hom.comp_apply, hz]
      exact (hpieces i).2.1
    · intro z' hz'
      apply (d i).hom.homeomorph.injective
      change (d i).hom z' = (d i).hom z
      rw [hz]
      apply (hpieces i).2.2.1
      simpa [hq, Scheme.Hom.comp_apply] using hz'
    · rw [hp, Scheme.Hom.comp_apply, hz]
      exact (hpieces i).2.2.2.1
    · rw [hp, Scheme.residueFieldMap_comp]
      have : IsIso (((V' i).ι ≫ pullback.fst f φ').residueFieldMap ((d i).hom z)) :=
        hz.symm ▸ (hpieces i).2.2.2.2
      infer_instance
  · intro w hw i
    let w' : W.toScheme := ⟨e.hom (W''.ι w), w.property⟩
    have hw' : (W.ι ≫ pullback.snd f φ') w' = t' := by
      simpa [w', e, ← Scheme.Hom.comp_apply] using hw
    have ha := havoid w' hw' i
    simpa [w', e, ← Scheme.Hom.comp_apply] using ha

end AlgebraicGeometry
