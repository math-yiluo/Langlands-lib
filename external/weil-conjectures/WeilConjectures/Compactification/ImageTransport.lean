/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-!

# Transport of scheme-theoretic images through admissible blow-ups

This file records the transport of scheme-theoretic images through an admissible blow-up
(Stacks Project Tag 0F3Y; blueprint `thm:0F3Y`,
`lemma:nagata-scheme-image-strict-transform`,
`lemma:nagata-scheme-image-transport-strict-transform`; proof order item 31):

- `AlgebraicGeometry.Scheme.Hom.ker_lift_admissibleBlowup`: the scheme-theoretic image of
  a lift along a `U`-admissible blow-up is the strict transform of the scheme-theoretic
  image.

It is consumed by the graph extension of
`WeilConjectures.Compactification.GraphExtension`.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section ImageTransport

variable {S X Y V : Scheme.{u}} {x : X ⟶ S} {y : Y ⟶ S}

/-- **Scheme-theoretic images and admissible blow-ups** (Stacks Project Tag 0F3Y;
blueprint: `lemma:nagata-scheme-image-strict-transform`,
`lemma:nagata-scheme-image-transport-strict-transform`; proof order item 31).

Differences from the informal statement. The two closed subschemes of `X' ×_S Y` are
recorded by the kernels of the corresponding closed immersions, so the statement is in
kernel ideal sheaf form. The Stacks Project and the blueprint also assume `h`
quasi-separated; Mathlib's kernel ideal sheaf theory only needs quasi-compactness, so that
hypothesis is dropped here.

The right-hand side is a strict transform, so the theorem carries the standing
quasi-compactness assumption of `WeilConjectures.Compactification.StrictTransform`: the
inclusion of the open locus over the preserved open must be a quasi-compact morphism. It
is not implied by the remaining hypotheses — nothing here makes `U`, `B.preservedOpen` or
`X` quasi-compact — and is discharged from finiteness data by
`AlgebraicGeometry.quasiCompact_strictTransformOpen_ι_of_isCompact`. (The
specialization `AlgebraicGeometry.quasiCompact_strictTransformOpen_ι` does *not* apply:
it is stated for a blow-up map of an ideal sheaf, not for the base-changed blow-up
occurring here.) -/
theorem Scheme.Hom.ker_lift_admissibleBlowup
    {U : X.Opens} (B : IsAdmissible X U)
    (h : V ⟶ pullback x y) [QuasiCompact h]
    (hfac : Set.range (h ≫ pullback.fst x y) ⊆ (U : Set X))
    (h' : V ⟶ pullback (B.I.blowupMap ≫ x) y)
    (hlift : h' ≫ partialSectionOpenι x y B.I.blowupMap = h)
    [QuasiCompact (strictTransformOpen h.imageι (partialSectionOpenι x y B.I.blowupMap)
      (pullback.fst x y ⁻¹ᵁ B.preservedOpen)).ι] :
    h'.ker =
      (strictTransformMap h.imageι (partialSectionOpenι x y B.I.blowupMap)
        (pullback.fst x y ⁻¹ᵁ B.preservedOpen)).ker := by
  set ρ := partialSectionOpenι x y B.I.blowupMap
  set W : (pullback x y).Opens := pullback.fst x y ⁻¹ᵁ B.preservedOpen
  set L := strictTransformOpen h.imageι ρ W
  -- `h` lands over the preserved open, because it lands over `U ≤ B.preservedOpen`.
  have hrange : Set.range h ⊆ (W : Set ↥(pullback x y)) := by
    rintro _ ⟨v, rfl⟩
    exact B.le_preservedOpen (by simpa [Scheme.Hom.comp_apply] using hfac ⟨v, rfl⟩)
  -- The blow-up is an isomorphism over its own preserved open, ...
  have : IsIso (B.I.blowupMap ∣_ B.preservedOpen) :=
    B.I.isIso_blowupMap_restrict_support_compl
  -- ... hence so is its base change, over the preimage of the preserved open.
  have : IsIso (ρ ∣_ W) :=
    isIso_partialSectionOpenι_restrict x y B.I.blowupMap B.preservedOpen
  -- So the open locus is the restriction of `SIm(h)` over the preserved open.
  have hPB := isPullback_strictTransformOpen h.imageι ρ W
  -- The lift of `h` to `SIm(h) ×_(X ×_S Y) (X' ×_S Y)`.
  have hcond : h.toImage ≫ h.imageι = h' ≫ ρ := by
    rw [Scheme.Hom.toImage_imageι, hlift]
  set k := pullback.lift h.toImage h' hcond
  have hkfst : k ≫ pullback.fst h.imageι ρ = h.toImage := pullback.lift_fst _ _ _
  have hksnd : k ≫ pullback.snd h.imageι ρ = h' := pullback.lift_snd _ _ _
  -- It lands in the open locus, again because `h` lands over the preserved open.
  have hkrange : Set.range (k ≫ pullback.fst h.imageι ρ ≫ h.imageι) ⊆
      (W : Set ↥(pullback x y)) := by
    rw [← Category.assoc, hkfst, Scheme.Hom.toImage_imageι]
    exact hrange
  set m := strictTransformOpenLift h.imageι ρ W k hkrange
  have hmfac : m ≫ L.ι = k := strictTransformOpenLift_ι h.imageι ρ W k hkrange
  -- The projection of the open locus to `SIm(h)` is a base change of the open immersion
  -- `W ⟶ X ×_S Y`, so `V` sits inside the open locus as a flat base change of
  -- `V ⟶ SIm(h)`, and scheme-theoretic dominance descends.
  have : IsOpenImmersion (L.ι ≫ pullback.fst h.imageι ρ) :=
    IsOpenImmersion.of_isPullback hPB.flip inferInstance
  have hsq : IsPullback (𝟙 V) m h.toImage (L.ι ≫ pullback.fst h.imageι ρ) :=
    IsPullback.of_horiz_isIso_mono
      ⟨by rw [Category.id_comp, ← Category.assoc, hmfac, hkfst]⟩
  have : IsSchemeTheoreticallyDominant m := .of_isPullback hsq
  calc h'.ker = (m ≫ (L.ι ≫ pullback.snd h.imageι ρ)).ker := by
        rw [← Category.assoc, hmfac, hksnd]
    _ = (L.ι ≫ pullback.snd h.imageι ρ).ker :=
        Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant _ _
    _ = _ := (ker_strictTransformMap h.imageι ρ W).symm

end ImageTransport

end AlgebraicGeometry
