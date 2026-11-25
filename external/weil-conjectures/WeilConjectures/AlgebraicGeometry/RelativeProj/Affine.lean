/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.RelativeProj.ChartBaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Base change of `Proj` of a graded algebra

For a graded `R`-algebra `𝒜` we write `Proj.toSpecOfAlgebra 𝒜: Proj 𝒜 ⟶ Spec R` for the structure
morphism. If `φ: 𝒜 →+*ᵍ ℬ` is a coefficientwise base change along `R → S`
(`GradedRingHom.IsGradedBaseChange`), then

```
Proj ℬ ⟶ Proj 𝒜
  |          |
Spec S  ⟶  Spec R
```

is a pullback square, i.e. `Proj (S ⊗[R] 𝒜) ≅ Spec S ×_{Spec R} Proj 𝒜`. The two main
instances are the localization `𝒜 → 𝒜[1/f]` (restriction of `Proj` to the basic open
`D(f) ⊆ Spec R`) and the base change `𝒜 → S ⊗[R] 𝒜`.

## Main results

- `AlgebraicGeometry.Proj.toSpecOfAlgebra` — the structure morphism `Proj 𝒜 ⟶ Spec R`.
- `AlgebraicGeometry.Proj.isPullback_map_of_isGradedBaseChange` — the base change square is a
  pullback.

This is a generic version of `AlgebraicGeometry.AffineBlowup.isPullback_hom_of_isLocalization`.
The material of this file would belong to `Mathlib.AlgebraicGeometry.ProjectiveSpectrum`.
-/

@[expose] public section

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The structure morphism `Proj 𝒜 ⟶ Spec R` of the `Proj` of a graded `R`-algebra. -/
noncomputable def toSpecOfAlgebra : Proj 𝒜 ⟶ Spec (.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))

@[reassoc]
lemma awayι_toSpecOfAlgebra {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    Proj.awayι 𝒜 s hs hd ≫ toSpecOfAlgebra 𝒜 =
      Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜 s))) := by
  rw [toSpecOfAlgebra, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

variable {𝒜} {S B : Type u} [CommRing S] [Algebra R S] [CommRing B] [Algebra S B] [Algebra R B]
  [IsScalarTower R S B] {ℬ : ℕ → Submodule S B} [GradedAlgebra ℬ]

/-- The base change square of `Proj` commutes. -/
@[reassoc]
lemma map_toSpecOfAlgebra (φ : 𝒜 →+*ᵍ ℬ)
    (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap R B r)
    (hirr : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ) :
    Proj.map φ hirr ≫ toSpecOfAlgebra 𝒜 =
      toSpecOfAlgebra ℬ ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  rw [toSpecOfAlgebra, toSpecOfAlgebra, ← Category.assoc, Proj.map_toSpecZero, Category.assoc,
    Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext r
  simp [hφ, IsScalarTower.algebraMap_apply R S B]

omit [Algebra R S] [Algebra R B] [IsScalarTower R S B] in
/-- The chart squares of `Proj.map` are pullbacks. -/
lemma isPullback_awayι_map (φ : 𝒜 →+*ᵍ ℬ)
    (hirr : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map φ s)))
      (Proj.awayι ℬ (φ s) (φ.map_mem hs) hd) (Proj.awayι 𝒜 s hs hd) (Proj.map φ hirr) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (Proj.awayι_comp_map φ hirr hd s hs) ?_
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
  exact Proj.map_preimage_basicOpen φ hirr s

attribute [local instance] GradedRingHom.awayAlgebra GradedRingHom.awayMapAlgebra
  GradedRingHom.awayAlgebra_isScalarTower

/-- **Base change for `Proj`**: if `φ: 𝒜 →+*ᵍ ℬ` is a coefficientwise base change along
`R → S`, then `Proj ℬ ≅ Spec S ×_{Spec R} Proj 𝒜`, i.e. the square formed by `Proj.map φ` and
the structure morphisms is a pullback. -/
theorem isPullback_map_of_isGradedBaseChange (φ : 𝒜 →+*ᵍ ℬ) (h : φ.IsGradedBaseChange) :
    IsPullback (Proj.map φ h.irrelevant_le) (toSpecOfAlgebra ℬ) (toSpecOfAlgebra 𝒜)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (Proj.affineOpenCover 𝒜).openCover fun i ↦ ?_
  obtain ⟨⟨d, hd⟩, s, hs⟩ := i
  have := GradedRingHom.awayMapAlgebra_isScalarTower (φ := φ) s h.map_algebraMap
  have := h.isPushout_away hs
  have Q1 := (isPullback_awayι_map φ h.irrelevant_le hs hd).flip
  have Q2 := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S (Away 𝒜 s) (Away ℬ (φ s)))).flip
  refine Q2.of_iso Q1.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (Q1.isoPullback_hom_snd).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    change _ = Q1.isoPullback.hom ≫ pullback.fst _ _ ≫ _
    rw [Q1.isoPullback_hom_fst_assoc, awayι_toSpecOfAlgebra]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    change _ = Proj.awayι 𝒜 s hs hd ≫ _
    rw [awayι_toSpecOfAlgebra]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

end AlgebraicGeometry.Proj

namespace GradedRingHom

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra R A] [CommRing B]
  [Algebra S B] {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {ℬ : ℕ → Submodule S B}
  [GradedAlgebra ℬ]

/-- `φ : 𝒜 →+*ᵍ ℬ` is a coefficientwise base change along the ring homomorphism `f : R →+* S`:
this is `GradedRingHom.IsGradedBaseChange` for the algebra structures induced by `f`. -/
def IsGradedBaseChangeAlong (f : R →+* S) (φ : 𝒜 →+*ᵍ ℬ) : Prop :=
  letI := f.toAlgebra
  letI : Algebra R B := ((algebraMap S B).comp f).toAlgebra
  haveI : IsScalarTower R S B := .of_algebraMap_eq' rfl
  φ.IsGradedBaseChange

namespace IsGradedBaseChangeAlong

variable {f : R →+* S} {φ : 𝒜 →+*ᵍ ℬ} (h : φ.IsGradedBaseChangeAlong f)
include h

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
lemma map_algebraMap (r : R) : φ (algebraMap R A r) = algebraMap S B (f r) :=
  letI := f.toAlgebra
  letI : Algebra R B := ((algebraMap S B).comp f).toAlgebra
  haveI : IsScalarTower R S B := .of_algebraMap_eq' rfl
  IsGradedBaseChange.map_algebraMap h r

lemma irrelevant_le :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ :=
  letI := f.toAlgebra
  letI : Algebra R B := ((algebraMap S B).comp f).toAlgebra
  haveI : IsScalarTower R S B := .of_algebraMap_eq' rfl
  IsGradedBaseChange.irrelevant_le h

end IsGradedBaseChangeAlong

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- For an `R`-algebra `S` and compatible algebra structures, `IsGradedBaseChangeAlong` along
`algebraMap R S` is `IsGradedBaseChange`. -/
theorem isGradedBaseChangeAlong_algebraMap_iff [Algebra R S] [Algebra R B] [IsScalarTower R S B]
    {φ : 𝒜 →+*ᵍ ℬ} : φ.IsGradedBaseChangeAlong (algebraMap R S) ↔ φ.IsGradedBaseChange := by
  obtain ⟨f, hf⟩ : ∃ f : R →+* S, algebraMap R S = f := ⟨_, rfl⟩
  rw [hf]
  have e2 : ‹Algebra R B› = ((algebraMap S B).comp f).toAlgebra :=
    Algebra.algebra_ext _ _ fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R S B, hf]; rfl
  have e1 : ‹Algebra R S› = f.toAlgebra :=
    Algebra.algebra_ext _ _ fun r ↦ congrArg (fun g : R →+* S ↦ g r) hf
  subst e2
  subst e1
  rfl

end GradedRingHom

namespace AlgebraicGeometry.Proj

variable {R A S B : Type u} [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [CommRing B]
  [Algebra S B] {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {ℬ : ℕ → Submodule S B}
  [GradedAlgebra ℬ]

/-- Naturality of `Proj.toSpecOfAlgebra` along a ring homomorphism `f : R →+* S`. -/
@[reassoc]
lemma map_toSpecOfAlgebra_of_comp (f : R →+* S) (φ : 𝒜 →+*ᵍ ℬ)
    (hφ : ∀ r : R, φ (algebraMap R A r) = algebraMap S B (f r))
    (hirr : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ) :
    Proj.map φ hirr ≫ toSpecOfAlgebra 𝒜 = toSpecOfAlgebra ℬ ≫ Spec.map (CommRingCat.ofHom f) :=
  letI := f.toAlgebra
  letI : Algebra R B := ((algebraMap S B).comp f).toAlgebra
  haveI : IsScalarTower R S B := .of_algebraMap_eq' rfl
  map_toSpecOfAlgebra φ hφ hirr

/-- **Base change for `Proj`** along a ring homomorphism `f: R →+* S`. -/
theorem isPullback_map_of_isGradedBaseChangeAlong (f : R →+* S) (φ : 𝒜 →+*ᵍ ℬ)
    (h : φ.IsGradedBaseChangeAlong f) :
    IsPullback (Proj.map φ h.irrelevant_le) (toSpecOfAlgebra ℬ) (toSpecOfAlgebra 𝒜)
      (Spec.map (CommRingCat.ofHom f)) :=
  letI := f.toAlgebra
  letI : Algebra R B := ((algebraMap S B).comp f).toAlgebra
  haveI : IsScalarTower R S B := .of_algebraMap_eq' rfl
  isPullback_map_of_isGradedBaseChange φ h

end AlgebraicGeometry.Proj
