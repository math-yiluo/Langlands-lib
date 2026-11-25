/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpaceClosedChart

/-!
# Morphisms locally embedding into affine spaces of bounded dimension

A morphism `q : T ⟶ S` *locally embeds into `𝔸ᵐ_S`*
(`AlgebraicGeometry.Scheme.Hom.LocallyEmbedsInAffineSpace q m`) if every point of `T` has an open
neighbourhood `V` with an immersion `V ⟶ 𝔸ⁿ_S` over `S` into an affine space of dimension
`n ≤ m`. This is the dimension measure of the induction in Gabber's Künneth formula for nearby
cycles (blueprint `proposition-external-kunneth-formula-nearby-cycles`, "Finite support"): slicing
along one coordinate of such a chart lowers the dimension of the chart by one.

## Main statements

* `AlgebraicGeometry.Scheme.Hom.LocallyEmbedsInAffineSpace.restrict`: restriction to an open;
* `AlgebraicGeometry.Scheme.Hom.LocallyEmbedsInAffineSpace.of_isPullback`: stability under base
  change;
* `AlgebraicGeometry.Scheme.Hom.exists_locallyEmbedsInAffineSpace`: a quasi-compact morphism
  locally of finite type to an affine scheme locally embeds into some `𝔸ᵐ_S`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {T S : Scheme.{u}}

/-- A morphism `q : T ⟶ S` *locally embeds into `𝔸ᵐ_S`* if every point of `T` has an open
neighbourhood `V` with an immersion `V ⟶ 𝔸(ι; S)` over `S`, for a finite type `ι` with at most
`m` elements. -/
def LocallyEmbedsInAffineSpace (q : T ⟶ S) (m : ℕ) : Prop :=
  ∀ x : T, ∃ (V : T.Opens) (_ : x ∈ V) (ι : Type u) (_ : Finite ι) (c : V.toScheme ⟶ 𝔸(ι; S)),
    Nat.card ι ≤ m ∧ IsImmersion c ∧ c ≫ 𝔸(ι; S) ↘ S = V.ι ≫ q

namespace LocallyEmbedsInAffineSpace

variable {q : T ⟶ S} {m : ℕ}

lemma mono (h : q.LocallyEmbedsInAffineSpace m) {m' : ℕ} (hm : m ≤ m') :
    q.LocallyEmbedsInAffineSpace m' := fun x ↦ by
  obtain ⟨V, hx, ι, hι, c, hc, hi, hq⟩ := h x
  exact ⟨V, hx, ι, hι, c, hc.trans hm, hi, hq⟩

/-- An immersion into `𝔸(ι; S)` over `S` is a global chart. -/
lemma of_isImmersion {ι : Type u} [Finite ι] (c : T ⟶ 𝔸(ι; S)) [IsImmersion c]
    (hc : c ≫ 𝔸(ι; S) ↘ S = q) : q.LocallyEmbedsInAffineSpace (Nat.card ι) := fun _ ↦
  ⟨⊤, trivial, ι, inferInstance, (⊤ : T.Opens).ι ≫ c, le_rfl, inferInstance, by simp [hc]⟩

/-- Restriction to an open. -/
lemma restrict (h : q.LocallyEmbedsInAffineSpace m) (U : T.Opens) :
    (U.ι ≫ q).LocallyEmbedsInAffineSpace m := fun x ↦ by
  obtain ⟨V, hx, ι, hι, c, hc, hi, hq⟩ := h (U.ι x)
  refine ⟨U.ι ⁻¹ᵁ V, hx, ι, hι, U.ι ∣_ V ≫ c, hc, inferInstance, ?_⟩
  rw [Category.assoc, hq, morphismRestrict_ι_assoc]

/-- **Stability under base change**: if `q'` is a base change of `q`, and `q` locally embeds
into `𝔸ᵐ_S`, then `q'` locally embeds into `𝔸ᵐ_{S'}`. -/
lemma of_isPullback {T' S' : Scheme.{u}} {q' : T' ⟶ S'} {g' : T' ⟶ T} {g : S' ⟶ S}
    (hpb : IsPullback g' q' q g) (h : q.LocallyEmbedsInAffineSpace m) :
    q'.LocallyEmbedsInAffineSpace m := fun x ↦ by
  obtain ⟨V, hx, ι, hι, c, hc, hi, hq⟩ := h (g' x)
  have hV : IsPullback (g' ∣_ V) ((g' ⁻¹ᵁ V).ι ≫ q') (c ≫ 𝔸(ι; S) ↘ S) g := by
    rw [hq]
    exact (isPullback_morphismRestrict g' V).paste_vert hpb
  have hA := AffineSpace.isPullback_map (n := ι) g
  exact ⟨g' ⁻¹ᵁ V, hx, ι, hι, _, hc,
    MorphismProperty.of_isPullback (IsPullback.of_bot' hV hA) hi, hA.lift_snd _ _ _⟩

end LocallyEmbedsInAffineSpace

/-- A quasi-compact morphism locally of finite type to an affine scheme locally embeds into some
affine space: finitely many affine opens cover the source, and each of them is a closed subscheme
of an affine space over the base
(`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_of_isAffine`). -/
lemma exists_locallyEmbedsInAffineSpace [IsAffine S] (q : T ⟶ S) [LocallyOfFiniteType q]
    [QuasiCompact q] : ∃ m, q.LocallyEmbedsInAffineSpace m := by
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace q
  have hU (x : T) : ∃ U : T.affineOpens, x ∈ (U : T.Opens) := by
    obtain ⟨U, hU, hxU, -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
        (show x ∈ (⊤ : T.Opens) from trivial)
    exact ⟨⟨U, hU⟩, hxU⟩
  choose U hxU using hU
  choose n c hcq hc using fun x ↦
    exists_isClosedImmersion_affineSpace_of_isAffine ((U x : T.Opens).ι ≫ q)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ ((U x : T.Opens) : Set T))
    (fun x ↦ (U x : T.Opens).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxU x⟩)
  refine ⟨s.sup n, fun x ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact ⟨U y, hxy, ULift (Fin (n y)), inferInstance, c y, by simpa using Finset.le_sup hy,
    inferInstance, hcq y⟩

end Scheme.Hom

/-- **Slicing a chart along one coordinate.** Let `c : V ⟶ 𝔸(ι; S)` be an immersion over `S`,
`i ∈ ι` a coordinate, and `σ : S' ⟶ 𝔸¹_S` any morphism. Then the fibre product
`V ×_{𝔸¹_S} S'` of the `i`-th coordinate `V ⟶ 𝔸¹_S` of `c` with `σ` admits an immersion over
`S'` into `𝔸({j // j ≠ i}; S')`: indeed `𝔸(ι; S) ×_{𝔸¹_S} S' = 𝔸({j // j ≠ i}; S')`. -/
theorem exists_isImmersion_pullback_reindex {V S' : Scheme.{u}} {ι : Type u}
    (c : V ⟶ 𝔸(ι; S)) [IsImmersion c] (i : ι) (σ : S' ⟶ 𝔸(ULift.{u} (Fin 1); S)) :
    ∃ c' : pullback (c ≫ AffineSpace.reindex (fun _ : ULift.{u} (Fin 1) ↦ i) S) σ ⟶
        𝔸({j : ι // j ≠ i}; S'),
      IsImmersion c' ∧ c' ≫ 𝔸({j : ι // j ≠ i}; S') ↘ S' = pullback.snd _ _ := by
  classical
  let e : ULift.{u} (Fin 1) ⊕ {j : ι // j ≠ i} ≃ ι :=
    { toFun := Sum.elim (fun _ ↦ i) Subtype.val
      invFun := fun j ↦ if h : j = i then .inl ⟨0⟩ else .inr ⟨j, h⟩
      left_inv := by
        rintro (⟨⟨k⟩⟩ | ⟨j, hj⟩)
        · simp [Fin.fin_one_eq_zero k]
        · simp [hj]
      right_inv := fun j ↦ by by_cases h : j = i <;> simp [h] }
  -- `Φ : 𝔸(ι; S) ≅ 𝔸({j ≠ i}; 𝔸¹_S)` turns the `i`-th coordinate into the structure morphism.
  let Φ := (AffineSpace.reindexIso S e).hom ≫ (AffineSpace.sumIso S).hom
  have hΦ : AffineSpace.reindex (fun _ : ULift.{u} (Fin 1) ↦ i) S =
      Φ ≫ 𝔸({j : ι // j ≠ i}; 𝔸(ULift.{u} (Fin 1); S)) ↘ 𝔸(ULift.{u} (Fin 1); S) := by
    rw [Category.assoc, AffineSpace.sumIso_hom, AffineSpace.sumHom_over]
    ext1
    · simp
    · simp [e, AffineSpace.reindex_appTop_coord]
  have hc : c ≫ AffineSpace.reindex (fun _ : ULift.{u} (Fin 1) ↦ i) S =
      (c ≫ Φ) ≫ 𝔸({j : ι // j ≠ i}; 𝔸(ULift.{u} (Fin 1); S)) ↘ 𝔸(ULift.{u} (Fin 1); S) := by
    rw [Category.assoc, ← hΦ]
  have := MorphismProperty.pullbackMap (P := @IsImmersion) (i₁ := c ≫ Φ) (i₂ := 𝟙 S')
    inferInstance inferInstance hc (Category.id_comp σ).symm
  refine ⟨pullback.map _ _ _ _ (c ≫ Φ) (𝟙 S') (𝟙 _) ((Category.comp_id _).trans hc)
      ((Category.comp_id _).trans (Category.id_comp σ).symm) ≫
    (AffineSpace.isPullback_map (n := {j : ι // j ≠ i}) σ).isoPullback.inv, inferInstance, ?_⟩
  simp

end AlgebraicGeometry
