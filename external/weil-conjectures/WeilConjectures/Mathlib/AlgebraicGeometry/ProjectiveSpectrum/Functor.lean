/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Functoriality of `Proj`

We record that `Proj.map` only depends on the underlying graded ring homomorphism, the
naturality of `Proj.toSpecZero` with respect to `Proj.map`, and that `Proj.map` of a
surjective graded ring homomorphism is a closed immersion.

## Main results

- `AlgebraicGeometry.Proj.map_toSpecZero` — naturality of `Proj.toSpecZero`;
- `AlgebraicGeometry.Proj.isClosedImmersion_map` — `Proj` of a surjective graded ring
  homomorphism is a closed immersion.
-/

@[expose] public section

universe u

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- `Proj.map` only depends on the underlying graded ring homomorphism. -/
lemma Proj.map_congr {f g : 𝒜 →+*ᵍ ℬ} (e : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    Proj.map f hf = Proj.map g hg := by
  subst e; rfl

/-- Naturality of `Proj.toSpecZero` with respect to `Proj.map`: the square

```
Proj ℬ  ⟶  Proj 𝒜
  |            |
  v            v
Spec (ℬ 0) ⟶ Spec (𝒜 0)
```

commutes. -/
lemma Proj.map_toSpecZero (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradeZeroRingHom) := by
  refine (Proj.mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  rw [Proj.awayι_comp_map_assoc f hf s.1.2 _ s.2.2, Proj.awayι_toSpecZero,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    HomogeneousLocalization.Away.map_comp_fromZeroRingHom]

/-- The standard affine opens `D₊(s)`, for `s` homogeneous of positive degree, cover
`Proj 𝒜`. -/
lemma Proj.iSup_basicOpen_homogeneous_eq_top :
    ⨆ i : Σ n : PNat, 𝒜 (n : ℕ), Proj.basicOpen 𝒜 (i.2 : A) = ⊤ := by
  rw [← Scheme.OpenCover.iSup_opensRange (Proj.affineOpenCover 𝒜).openCover]
  exact iSup_congr fun i ↦ (Proj.opensRange_awayι 𝒜 _ i.2.2 i.1.2).symm

/-- **`Proj` of a surjective graded ring homomorphism is a closed immersion.**

`IsClosedImmersion` is Zariski-local on the target, so it suffices to check this over the
standard affine opens `D₊(s) ⊆ Proj 𝒜` for `s` homogeneous of positive degree. There
`Proj.awayι_comp_map` identifies the restriction of `Proj.map f hf` with
`Spec.map (HomogeneousLocalization.Away.map f s)`, which is a closed immersion because
`HomogeneousLocalization.Away.map` of a surjection is surjective. -/
theorem Proj.isClosedImmersion_map (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hsurj : Function.Surjective f) :
    IsClosedImmersion (Proj.map f hf) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) _
    (Proj.iSup_basicOpen_homogeneous_eq_top (𝒜 := 𝒜)) fun i ↦ ?_
  have hs : (i.2 : A) ∈ 𝒜 (i.1 : ℕ) := i.2.2
  have hi : 0 < (i.1 : ℕ) := i.1.2
  have e : Arrow.mk (Proj.map f hf ∣_ (Proj.awayι 𝒜 (i.2 : A) hs hi).opensRange) ≅
      Arrow.mk (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f (i.2 : A)))) :=
    morphismRestrictArrowIso (Proj.map f hf) _ (Proj.awayι_comp_map f hf hi _ hs)
      (by rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.map_preimage_basicOpen])
  have H : IsClosedImmersion (Proj.map f hf ∣_ (Proj.awayι 𝒜 (i.2 : A) hs hi).opensRange) :=
    (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion e).mpr <|
      IsClosedImmersion.spec_of_surjective _
        (HomogeneousLocalization.Away.map_surjective f hsurj hs)
  rwa [Proj.opensRange_awayι] at H

end AlgebraicGeometry
