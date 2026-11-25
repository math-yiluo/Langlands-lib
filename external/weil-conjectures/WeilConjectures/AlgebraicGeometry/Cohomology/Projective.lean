/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechBaseChange

/-!
# Coherent cohomology of projective schemes

Let `A` be a noetherian ring. The cohomology of a coherent sheaf on a closed subscheme of
`ℙⁿ_A` consists of finite `A`-modules, and vanishes above `n`. In relative form, the higher
direct images of a coherent sheaf along a projective morphism `f : X ⟶ S` to a locally noetherian
scheme are coherent, and vanish above the dimension of the ambient projective space. For a
quasi-compact and quasi-separated morphism to a quasi-compact base, the higher direct images of
quasi-coherent sheaves vanish in degrees bounded uniformly in the sheaf and the base change.

A projective morphism `f : X ⟶ S` is presented through a closed immersion `i : X ⟶ ℙ(n; S)` over
`S`, as in the blueprint's definition of (H-)projective morphisms. The finiteness of the
cohomology over a noetherian ring is in
`WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveFinite`
(`AlgebraicGeometry.ProjectiveSpace.finite_H`,
`AlgebraicGeometry.Scheme.Modules.finite_H_of_isClosedImmersion`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_of_isPullback`: the uniform
  vanishing bound for a quasi-compact quasi-separated morphism over a quasi-compact base.
- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_isClosedImmersion`: the vanishing of the
  cohomology of a closed subscheme of `ℙⁿ_A` above `n`.
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage_of_isClosedImmersion`
  and `isZero_higherDirectImage_of_isClosedImmersion`: coherence and vanishing of the higher
  direct images along a projective morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X T : Scheme.{u}}

/-- **Uniform vanishing of the higher direct images.** Let `f : X ⟶ T` be quasi-compact and
quasi-separated, with `T` quasi-compact. There is an integer `n` such that `R^p f'_* ℱ' = 0` for
all `p ≥ n`, all base changes `f' : X' ⟶ T'` of `f` along morphisms `g : T' ⟶ T`, and all
quasi-coherent `𝒪_{X'}`-modules `ℱ'`.

Over an affine open `A` of `T`, cover `f⁻¹ A` by `t` affine opens `Uᵢ`, each intersection
`Uᵢ ∩ Uⱼ` being covered by at most `m` affine opens (`X` is quasi-separated over `T`). Induction
on `t` with the Mayer–Vietoris sequence of the higher direct images for `U₁` and `U₂ ∪ ⋯ ∪ U_t`,
where `U₁ ∩ (U₂ ∪ ⋯ ∪ U_t)` is a union of affine opens of the affine `U₁`, gives the bound
`n = t m + 2` (`AlgebraicGeometry.Scheme.Modules.higherDirectImageBound_of_affineCover`).
Over an affine open `W' ⊆ g⁻¹ A` of `T'`, the preimages of these opens in `f'⁻¹ W'` are
again affine, being fibre products of affine schemes, and form a covering of the same shape
[Stacks, Tag 01XJ]. Quasi-coherence of the `R^p f_* ℱ`, the first part of the blueprint
lemma, is `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`.

(blueprint: `lem-pc-finite-support-hi`) -/
theorem exists_isZero_higherDirectImage_of_isPullback [CompactSpace T] (f : X ⟶ T)
    [QuasiCompact f] [QuasiSeparated f] :
    ∃ n : ℕ, ∀ {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
      [HasInjectiveResolutions X'.Modules], IsPullback g' f' f g →
      ∀ (ℱ' : X'.Modules) [SheafOfModules.IsQuasicoherent (R := X'.ringCatSheaf) ℱ'],
      ∀ p ≥ n, IsZero ((higherDirectImage f' p).obj ℱ') := by
  classical
  -- the bound over an affine open `A` of `T`
  have key (A : T.affineOpens) : ∃ n : ℕ, ∀ {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X)
      (f' : X' ⟶ T') [HasInjectiveResolutions X'.Modules], IsPullback g' f' f g →
      ∀ (W' : T'.Opens), IsAffineOpen W' → W' ≤ g ⁻¹ᵁ A →
      ∀ (ℱ' : X'.Modules) [SheafOfModules.IsQuasicoherent (R := X'.ringCatSheaf) ℱ'],
      ∀ p ≥ n, IsZero (((higherDirectImage f' p).obj ℱ').restrict W'.ι) := by
    -- a finite cover of `f⁻¹ A` by affine opens, whose intersections are finite unions of
    -- affine opens
    obtain ⟨s, hsne, hs⟩ := exists_finset_affineOpens_sup_eq (f.isCompact_preimage A.2.isCompact)
    have hsA (i : X.affineOpens) (hi : i ∈ s) : (i : X.Opens) ≤ f ⁻¹ᵁ A :=
      hs ▸ Finset.le_sup (f := fun V : X.affineOpens ↦ (V : X.Opens)) hi
    have hqs := f.isQuasiSeparated_preimage A.2.isQuasiSeparated
    have (i j : X.affineOpens) : ∃ t : Finset X.affineOpens,
        i ∈ s → j ∈ s → t.sup (fun V ↦ (V : X.Opens)) = (i : X.Opens) ⊓ j := by
      by_cases h : i ∈ s ∧ j ∈ s
      · obtain ⟨t, -, ht⟩ := exists_finset_affineOpens_sup_eq (W := (i : X.Opens) ⊓ j)
          (hqs _ _ (hsA i h.1) i.1.isOpen i.2.isCompact (hsA j h.2) j.1.isOpen j.2.isCompact)
        exact ⟨t, fun _ _ ↦ ht⟩
      · exact ⟨∅, fun hi hj ↦ (h ⟨hi, hj⟩).elim⟩
    choose t ht using this
    let m := (s ×ˢ s).sup fun p ↦ (t p.1 p.2).card
    refine ⟨s.card * m + 2, fun g g' f' _ sq W' hW' hW'A ℱ' _ p hp ↦ ?_⟩
    have : IsAffine W' := hW'
    have := isGrothendieckAbelian (f' ⁻¹ᵁ W')
    refine IsZero.of_iso ?_
      (higherDirectImagePullbackIsoRestrict (isPullback_morphismRestrict f' W').flip ℱ' p).symm
    -- the preimages in `f'⁻¹ W'` of the affine opens of `X` over `A` are affine
    have haff (U : X.Opens) (hU : IsAffineOpen U) (hUA : U ≤ f ⁻¹ᵁ A) :
        IsAffineOpen (((f' ⁻¹ᵁ W').ι ≫ g') ⁻¹ᵁ U) := by
      have : IsAffine U := hU
      have : IsAffine (A : T.Opens) := A.2
      have H := Scheme.Hom.isPullback_resLE sq (US := (A : T.Opens)) (UT := W') (UX := U) hW'A
        hUA (UY := g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W') rfl
      have h : IsAffineOpen (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W') := .of_isIso H.isoPullback.hom
      rw [← (f' ⁻¹ᵁ W').ι.isAffineOpen_iff_of_isOpenImmersion]
      convert h using 1
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι, inf_comm]
    have hB := higherDirectImageBound_of_affineCover (f' ∣_ W')
      ((Modules.pullback (f' ⁻¹ᵁ W').ι).obj ℱ') s hsne
      (fun i ↦ ((f' ⁻¹ᵁ W').ι ≫ g') ⁻¹ᵁ (i : X.Opens)) (fun i hi ↦ haff i i.2 (hsA i hi)) t
      (fun V ↦ ((f' ⁻¹ᵁ W').ι ≫ g') ⁻¹ᵁ (V : X.Opens))
      (fun i hi j hj k hk ↦ haff k k.2 (((Finset.le_sup (f := fun V : X.affineOpens ↦
        (V : X.Opens)) hk).trans (ht i j hi hj).le).trans (inf_le_left.trans (hsA i hi))))
      (fun i hi j hj ↦ by rw [← preimage_finset_sup, ht i j hi hj, Scheme.Hom.preimage_inf]) m
      (fun i hi j hj ↦ Finset.le_sup (f := fun p : X.affineOpens × X.affineOpens ↦
        (t p.1 p.2).card) (b := (i, j)) (Finset.mem_product.2 ⟨hi, hj⟩))
    have hcov : s.sup (fun i ↦ ((f' ⁻¹ᵁ W').ι ≫ g') ⁻¹ᵁ (i : X.Opens)) = ⊤ := by
      rw [← preimage_finset_sup, hs, ← Scheme.Hom.comp_preimage, Category.assoc, sq.w,
        eq_top_iff, ← Scheme.Opens.ι_preimage_self (f' ⁻¹ᵁ W')]
      exact (f' ⁻¹ᵁ W').ι.preimage_mono (f'.preimage_mono hW'A)
    rw [hcov] at hB
    exact hB.higherDirectImage.2 p hp
  choose n hn using key
  obtain ⟨sT, -, hsT⟩ := exists_finset_isAffineOpen_sup_eq_top (X := T)
  refine ⟨sT.sup n, fun {T'} {X'} g g' f' _ sq ℱ' _ p hp ↦
    isZero_of_forall_exists_isZero_restrict _ fun t' ↦ ?_⟩
  obtain ⟨A, hA, hgA⟩ : ∃ A ∈ sT, g t' ∈ (A : T.Opens) := by
    have : g t' ∈ sT.sup (fun U ↦ (U : T.Opens)) := hsT ▸ trivial
    simpa only [Finset.sup_eq_iSup, TopologicalSpace.Opens.mem_iSup, exists_prop] using this
  obtain ⟨W', hW', ht'W', hW'A⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 T'.isBasis_affineOpens)
      (show t' ∈ g ⁻¹ᵁ (A : T.Opens) from hgA)
  exact ⟨W', ht'W', hn A g g' f' sq W' hW' hW'A ℱ' p ((Finset.le_sup hA).trans hp)⟩

end Scheme.Modules

open Scheme.Modules

variable {n : Type u} [Finite n] {X : Scheme.{u}}

/-- **Vanishing of the cohomology of a projective scheme above the dimension.** Let
`i : X ⟶ ℙᵈ_A` be a closed immersion, `ℙᵈ_A = ℙ(n; Spec A)` with `Nat.card n = d + 1`, and
`ℱ` a quasi-coherent `𝒪_X`-module. Then `H^q(X, ℱ) = 0` for `q > d`: the separated scheme `X` is
covered by the `d + 1` affine preimages of the standard affine opens, and quasi-coherent
cohomology vanishes above the number of affine opens in such a covering
(`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_card_le`).

This is the vanishing clause of the blueprint lemma.

(blueprint: `lem-pc-projective-coherent-finiteness`) -/
theorem Scheme.Modules.subsingleton_H_of_isClosedImmersion (A : Type u) [CommRing A]
    (i : X ⟶ ℙ(n; Spec (.of A))) [IsClosedImmersion i] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {d : ℕ} (hn : Nat.card n = d + 1)
    {q : ℕ} (hq : d < q) : Subsingleton (ℱ.H q) := by
  classical
  have : Fintype n := Fintype.ofFinite n
  have : IsSeparated (terminal.from X) := by
    rw [terminal.hom_ext (terminal.from X) ((i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A)) ≫
      terminal.from _)]
    infer_instance
  have : Nonempty n := (Nat.card_pos_iff.1 (by omega)).1
  refine subsingleton_H_of_card_le Finset.univ Finset.univ_nonempty
    (fun j ↦ i ⁻¹ᵁ ProjectiveSpace.standardOpen n _ j)
    (fun j _ ↦ (ProjectiveSpace.isAffineOpen_standardOpen n _ j).preimage i) ?_ _
    (cechAcyclicOnAffines_of_isQuasicoherent ℱ) ?_
  · rw [Finset.sup_univ_eq_iSup, ← Scheme.Hom.preimage_iSup, ProjectiveSpace.iSup_standardOpen,
      Scheme.Hom.preimage_top]
  · rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hn]
    omega

namespace Scheme.Modules

variable {S : Scheme.{u}} (f : X ⟶ S) (i : X ⟶ ℙ(n; S)) [IsClosedImmersion i]
  (hi : i ≫ ℙ(n; S) ↘ S = f) [HasInjectiveResolutions X.Modules] (ℱ : X.Modules)
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

include hi in
/-- **Coherence of the higher direct images of a projective morphism.** Let `S` be locally
noetherian, `f : X ⟶ S` projective, i.e. `f = π ∘ i` for a closed immersion `i : X ⟶ ℙⁿ_S`,
and `ℱ` a coherent `𝒪_X`-module. Then every `R^q f_* ℱ` is coherent.

A projective morphism is proper, so this is a case of
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage`. (The blueprint proves
it directly, as the input of the proper case: over an affine open `Spec A` of `S`, the Čech
complex of a finite affine cover of `f⁻¹(Spec A)` localises, so `R^q f_* ℱ` is the sheaf
associated with the finite `A`-module `H^q(f⁻¹(Spec A), ℱ)`.)

(blueprint: `lem-pc-projective-coherent-higher-images`) -/
theorem isFinitePresentation_higherDirectImage_of_isClosedImmersion [IsLocallyNoetherian S]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsFinitePresentation := by
  subst hi
  have : LocallyOfFinitePresentation (i ≫ ℙ(n; S) ↘ S) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType).mpr inferInstance
  exact isFinitePresentation_higherDirectImage _ ℱ q

include hi in
/-- **Vanishing of the higher direct images of a projective morphism.** In the situation of
`isFinitePresentation_higherDirectImage_of_isClosedImmersion`, with `Nat.card n = d + 1`, the
higher direct images `R^q f_* ℱ` vanish for `q > d`: over an affine open `S'` of `S`, the base
change of `X` is separated and covered by the `d + 1` affine preimages of the standard affine
opens, and the Mayer–Vietoris sequence of the higher direct images gives the vanishing above
`d` (`AlgebraicGeometry.Scheme.Modules.higherDirectImageBound_finsetSup`).

(blueprint: `lem-pc-projective-coherent-higher-images`) -/
theorem isZero_higherDirectImage_of_isClosedImmersion {d : ℕ} (hn : Nat.card n = d + 1)
    {q : ℕ} (hq : d < q) : IsZero ((higherDirectImage f q).obj ℱ) := by
  classical
  subst hi
  have : Fintype n := Fintype.ofFinite n
  have : Nonempty n := (Nat.card_pos_iff.1 (by omega)).1
  refine isZero_of_forall_exists_isZero_restrict _ fun s ↦ ?_
  obtain ⟨S', hS', hsS', -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) (show s ∈ ⊤ from trivial)
  have : IsAffine S' := hS'
  have sq := IsPullback.of_hasPullback (i ≫ ℙ(n; S) ↘ S) (Scheme.Opens.ι S')
  let g := pullback.fst (i ≫ ℙ(n; S) ↘ S) (Scheme.Opens.ι S')
  let f' := pullback.snd (i ≫ ℙ(n; S) ↘ S) (Scheme.Opens.ι S')
  have := isGrothendieckAbelian (Limits.pullback (i ≫ ℙ(n; S) ↘ S) (Scheme.Opens.ι S'))
  refine ⟨S', hsS', IsZero.of_iso ?_ (higherDirectImagePullbackIsoRestrict sq ℱ q).symm⟩
  -- the base change of `X` to `S'` is covered by the `d + 1` affine opens over the standard ones
  let U (j : n) := g ⁻¹ᵁ (i ⁻¹ᵁ ProjectiveSpace.standardOpen n S j ⊓ (i ≫ ℙ(n; S) ↘ S) ⁻¹ᵁ S')
  have hU (j : n) : IsAffineOpen (U j) := by
    refine isAffineOpen_preimage_of_isPullback sq hS' (by simp) inf_le_right ?_
    have : IsAffineHom ((ProjectiveSpace.standardOpen n S j).ι ≫ ℙ(n; S) ↘ S) := by
      rw [← ProjectiveSpace.standardOpenIso_hom_over]
      infer_instance
    have h := ((hS'.preimage ((ProjectiveSpace.standardOpen n S j).ι ≫ ℙ(n; S) ↘ S)
      ).image_of_isOpenImmersion (ProjectiveSpace.standardOpen n S j).ι).preimage i
    rwa [image_preimage_ι_comp, Scheme.Hom.preimage_inf, inf_comm, ← Scheme.Hom.comp_preimage]
      at h
  have hsep (V₁ V₂ : (Limits.pullback (i ≫ ℙ(n; S) ↘ S) (Scheme.Opens.ι S')).Opens)
      (h₁ : IsAffineOpen V₁) (h₂ : IsAffineOpen V₂) : IsAffineOpen (V₁ ⊓ V₂) :=
    (isAffineHom_diagonal_iff (f := f')).mp inferInstance ⊤ (isAffineOpen_top _) V₁ (by simp) V₂
      (by simp) h₁ h₂
  have hcov : (Finset.univ : Finset n).sup U = ⊤ := by
    rw [Finset.sup_univ_eq_iSup]
    simp only [U, Scheme.Hom.preimage_inf]
    rw [← iSup_inf_eq, ← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup,
      ProjectiveSpace.iSup_standardOpen, Scheme.Hom.preimage_top, Scheme.Hom.preimage_top,
      top_inf_eq, ← Scheme.Hom.comp_preimage, sq.w, Scheme.Hom.comp_preimage,
      Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
  have hB := higherDirectImageBound_finsetSup f' ((Modules.pullback g).obj ℱ) IsAffineOpen hsep
    (fun W hW ↦ higherDirectImageBound_of_isAffineOpen f' _ hW) Finset.univ Finset.univ_nonempty
    U fun j _ ↦ hU j
  rw [hcov] at hB
  exact hB.higherDirectImage.2 q (by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hn]
    omega)

end Scheme.Modules

end AlgebraicGeometry
