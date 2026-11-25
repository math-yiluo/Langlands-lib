/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Descent of properties of morphisms along fpqc coverings

We record the descent of properties of morphisms of schemes along fpqc coverings
(Stacks, Section 02KM).

## Main results

- `AlgebraicGeometry.fpqc_local_on_base_criterion`: a property of morphisms which is invariant
  under isomorphisms, stable under flat base change, Zariski local on the base and which descends
  along faithfully flat morphisms of affine schemes descends along fpqc coverings (Stacks 02KP).
- `AlgebraicGeometry.Scheme.fpqcCover_of_smallEtaleCover`: a covering family of the small étale
  site is an fpqc covering.

## References

* [Stacks: Section 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks: Tag 02KP](https://stacks.math.columbia.edu/tag/02KP)
-/

@[expose] public section

universe v u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

section Criterion

variable {P : MorphismProperty Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-- A property local at the target which descends along faithfully flat quasi-compact morphisms
and is stable under flat base change descends along a finite jointly surjective family of flat
morphisms from affine schemes to an affine scheme. -/
private lemma of_finite_affine_flat_family [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] {U X : Scheme.{u}} [IsAffine U]
    (f : X ⟶ U) {κ : Type u} [Finite κ] {V : κ → Scheme.{u}} [∀ k, IsAffine (V k)]
    (h : ∀ k, V k ⟶ U) (hflat : ∀ k, Flat (h k)) (hsurj : ⋃ k, Set.range (h k) = Set.univ)
    (H : ∀ k, P (pullback.snd f (h k))) : P f := by
  let p : ∐ V ⟶ U := Sigma.desc h
  have : Flat p := by
    have := hflat
    infer_instance
  have hp : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) p :=
    ⟨⟨Surjective.sigmaDesc_of_union_range_eq_univ hsurj, this⟩, inferInstance⟩
  refine MorphismProperty.of_pullback_fst_of_descendsAlong (P := P) hp ?_
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) (sigmaOpenCover _)]
  intro j
  have hsq := (IsPullback.of_hasPullback (pullback.fst p f) (Sigma.ι V j)).paste_horiz
    (IsPullback.of_hasPullback p f).flip
  have hj : Sigma.ι V j ≫ p = h j := Sigma.ι_comp_desc _ _
  rw [hj] at hsq
  have key : P (pullback.snd (pullback.fst p f) (Sigma.ι V j)) := by
    rw [← hsq.isoPullback_hom_snd, P.cancel_left_of_respectsIso]
    exact H j
  exact key

set_option backward.isDefEq.respectTransparency.types false in
/-- A property local at the target which descends along faithfully flat quasi-compact morphisms
and is stable under flat base change descends along fpqc coverings. -/
private lemma of_ofArrows_mem_fpqcPrecoverage [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    (hP : ∀ ⦃A B C D : Scheme.{u}⦄ (a : A ⟶ B) (b : A ⟶ C) (q : B ⟶ D) (m : C ⟶ D),
      IsPullback a b q m → Flat m → P q → P b)
    {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type v} {T : ι → Scheme.{u}} (g : ∀ i, T i ⟶ S)
    (hg : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S)
    (H : ∀ i, P (pullback.snd f (g i))) : P f := by
  let E : PreZeroHypercover.{v} S := ⟨ι, T, g⟩
  have hE : E.presieve₀ = Presieve.ofArrows T g := rfl
  obtain ⟨hqc, hflat⟩ := hg
  rw [← hE, Scheme.presieve₀_mem_qcPrecoverage_iff] at hqc
  rw [Scheme.ofArrows_mem_precoverage_iff] at hflat
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun U : S.affineOpens ↦ (U : S.Opens))
    (iSup_affineOpens_eq_top S) fun U ↦ ?_
  have : IsAffine U := U.2
  obtain ⟨n, idx, W, hW, hcov⟩ :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact E (U := U) U.2.isCompact
  have hsub (k : Fin n) : Set.range ((W k).ι ≫ g (idx k)) ⊆ Set.range (U : S.Opens).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    rw [← hcov]
    exact Set.mem_iUnion.mpr ⟨k, y.1, y.2, rfl⟩
  let h (k : Fin n) : (W k : Scheme) ⟶ U := IsOpenImmersion.lift _ _ (hsub k)
  have hh (k : Fin n) : h k ≫ (U : S.Opens).ι = (W k).ι ≫ g (idx k) :=
    IsOpenImmersion.lift_fac _ _ _
  have : ∀ k, IsAffine (W k : Scheme) := fun k ↦ hW k
  refine of_finite_affine_flat_family (f ∣_ (U : S.Opens)) (κ := ULift.{u} (Fin n))
    (V := fun k ↦ W k.down) (fun k ↦ h k.down) (fun k ↦ ?_) ?_ fun k ↦ ?_
  · have : Flat (h k.down ≫ (U : S.Opens).ι) := by
      rw [hh]
      have := hflat.2 (idx k.down)
      infer_instance
    exact MorphismProperty.of_postcomp (W := @Flat) (W' := @IsOpenImmersion) _ _
      (inferInstanceAs (IsOpenImmersion (U : S.Opens).ι)) this
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    have hx : (U : S.Opens).ι x ∈ (U : Set S) := by simp
    rw [← hcov] at hx
    obtain ⟨_, ⟨k, rfl⟩, y, hy, hyx⟩ := hx
    refine Set.mem_iUnion.mpr
      ⟨⟨k⟩, ⟨y, hy⟩, (U : S.Opens).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hh]
    exact hyx
  · -- The base change of `f ∣_ U` along `h k` is a base change of `pullback.snd f (g (idx k))`
    -- along the flat morphism `(W k).ι`.
    have s : IsPullback _ _ f (h k.down ≫ (U : S.Opens).ι) :=
      (IsPullback.of_hasPullback (f ∣_ (U : S.Opens)) (h k.down)).paste_horiz
        (isPullback_morphismRestrict f (U : S.Opens)).flip
    rw [hh] at s
    exact hP _ _ _ _ (IsPullback.of_right' s (IsPullback.of_hasPullback f (g (idx k.down))))
      inferInstance (H _)

set_option backward.isDefEq.respectTransparency.types false in
/-- **Criterion for fpqc descent of a property of morphisms** (Stacks 02KP, fpqc case). Let `P`
be a property of morphisms of schemes which

* (0) is invariant under isomorphisms of arrows,
* (1) is stable under flat base change,
* (2) is Zariski local on the base, and
* (3) descends along faithfully flat morphisms of affine schemes.

Then `P` descends along fpqc coverings: if `{g i: T i ⟶ S}` is an fpqc covering of `S` and all
the base changes `pullback.snd f (g i)` of `f: X ⟶ S` have `P`, then `f` has `P`. -/
theorem fpqc_local_on_base_criterion
    (h₀ : ∀ ⦃X S X' S' : Scheme.{u}⦄ (f : X ⟶ S) (f' : X' ⟶ S') (a : X ≅ X')
      (b : S ≅ S'),
      f ≫ b.hom = a.hom ≫ f' → P f → P f')
    (h₁ : ∀ ⦃X S S' : Scheme.{u}⦄ (f : X ⟶ S) (g : S' ⟶ S), Flat g → P f →
      P (pullback.snd f g))
    (h₂ : ∀ ⦃X S : Scheme.{u}⦄ (f : X ⟶ S) {K : Type u} (V : K → S.Opens),
      iSup V = ⊤ →
      (∀ k, P (f ∣_ V k)) → P f)
    (h₃ : ∀ ⦃X S S' : Scheme.{u}⦄ [IsAffine S] [IsAffine S'] (g : S' ⟶ S) (f : X ⟶ S),
      Flat g → Surjective g → P (pullback.snd f g) → P f)
    {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type v} {T : ι → Scheme.{u}} (g : ∀ i, T i ⟶ S)
    (hg : Presieve.ofArrows T g ∈ Scheme.fpqcPrecoverage S)
    (H : ∀ i, P (pullback.snd f (g i))) : P f := by
  have : P.RespectsIso := RespectsIso.of_respects_arrow_iso _ fun f f' e hf ↦
    h₀ f.hom f'.hom (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e) e.hom.w.symm hf
  -- stability under flat base change, in terms of pullback squares
  have hP : ∀ ⦃A B C D : Scheme.{u}⦄ (a : A ⟶ B) (b : A ⟶ C) (q : B ⟶ D) (m : C ⟶ D),
      IsPullback a b q m → Flat m → P q → P b := by
    intro A B C D a b q m hpb hm hq
    rw [← hpb.isoPullback_hom_snd, P.cancel_left_of_respectsIso]
    exact h₁ q m hm hq
  have : IsZariskiLocalAtTarget P := by
    refine IsZariskiLocalAtTarget.mk' (fun f U hf ↦ ?_) (fun f _ U hU H ↦ h₂ f U hU H)
    exact hP _ _ _ _ (isPullback_morphismRestrict f U).flip inferInstance hf
  have : P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
    apply IsZariskiLocalAtTarget.descendsAlong
    intro R X Y f g ⟨⟨hsurj, hflat⟩, hqc⟩ hfst
    have : CompactSpace X := by
      simpa [← quasiCompact_iff_compactSpace f] using hqc
    obtain ⟨T, p, hpsurj, hpflat, hT⟩ := X.exists_hom_isAffine_of_isZariskiLocalAtSource @Flat
    have := hT
    refine h₃ (p ≫ f) g inferInstance inferInstance ?_
    exact hP _ _ _ _ (IsPullback.of_bot' (IsPullback.of_hasPullback g (p ≫ f)).flip
      (IsPullback.of_hasPullback f g)).flip hpflat hfst
  exact of_ofArrows_mem_fpqcPrecoverage hP f g hg H

end Criterion

/-- **The fpqc topology is finer than the small étale topology**: a covering family
`{f i: V i ⟶ U}` of the small étale site of `T` is an fpqc covering of `U`; in particular every
`f i` is flat. -/
theorem Scheme.fpqcCover_of_smallEtaleCover {T : Scheme.{u}} {U : T.Etale} {ι : Type v}
    {V : ι → T.Etale} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ T.smallEtaleTopology U) :
    Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (f i).left) ∈ fpqcPrecoverage U.left := by
  refine fppfPrecoverage_le_fpqcPrecoverage _ ?_
  rw [fppfPrecoverage, ofArrows_mem_precoverage_iff]
  refine ⟨fun x ↦ ?_, fun i ↦ ⟨inferInstance, inferInstance⟩⟩
  have hx : x ∈ ⋃ i, Set.range (f i).left := by
    rw [(ofArrows_mem_smallEtaleTopology_iff f).mp hf]
    trivial
  exact Set.mem_iUnion.mp hx

end AlgebraicGeometry
