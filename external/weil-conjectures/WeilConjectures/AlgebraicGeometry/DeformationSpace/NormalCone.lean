/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone

/-!
# Geometry of the normal cone of a section

Let `g : V ⟶ B` have a section `s`. The projection `π_N : N_s ⟶ B` of the normal cone
(`AlgebraicGeometry.Scheme.Hom.normalConeProj`) factors through the affine morphism
`N_s = Spec_V (⨁ I^r / I^{r+1}) ⟶ V` followed by `g`. Hence it is affine, separated or
quasi-compact as soon as `g` is. When `g` is smooth of relative dimension `d` and `s` is a closed
section, `π_N` is smooth of relative dimension `d`, being the fibre over `t = 0` of the smooth
deformation `g̃` (blueprint `prose-09-11`, `prose-09-12` (1)). It is
then compactifiable over a quasi-compact quasi-separated base, by Nagata's theorem. These are
the hypotheses under which the section invariant `𝒞(π_N, 0_N)` of `lemma-section-normal-bundle` is
defined.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_normalConeProj`
- `AlgebraicGeometry.Scheme.Hom.hasCompactification_normalConeProj`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {V B : Scheme.{u}} (g : V ⟶ B) (s : B ⟶ V)

/-- The projection of the normal cone is affine if `g` is. -/
instance [IsAffineHom g] : IsAffineHom (normalConeProj g s) := by
  rw [normalConeProj]
  infer_instance

/-- The projection of the normal cone is separated if `g` is. -/
instance [IsSeparated g] : IsSeparated (normalConeProj g s) := by
  rw [normalConeProj]
  infer_instance

/-- The projection of the normal cone is quasi-compact if `g` is. -/
instance [QuasiCompact g] : QuasiCompact (normalConeProj g s) := by
  rw [normalConeProj]
  infer_instance

variable {g s}

/-- Blueprint `prose-09-11`: the normal cone of a closed section of a morphism smooth of
relative dimension `d` is smooth of relative dimension `d` over the base, being the fibre of the
smooth deformation `g̃` over `t = 0`. -/
theorem smoothOfRelativeDimension_normalConeProj (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    SmoothOfRelativeDimension d (normalConeProj g s) :=
  (normalConeData d hs).smoothOfRelativeDimension_proj

/-- The projection of the normal cone of a closed section of a separated quasi-compact morphism
smooth of relative dimension `d` is compactifiable over a quasi-compact quasi-separated base, by
Nagata's compactification theorem. -/
theorem hasCompactification_normalConeProj (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [CompactSpace B] [QuasiSeparatedSpace B]
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    HasCompactification (normalConeProj g s) :=
  have := smoothOfRelativeDimension_normalConeProj d hs
  have := SmoothOfRelativeDimension.smooth d (normalConeProj g s)
  (NagataCompactification (normalConeProj g s)).hasCompactification

end AlgebraicGeometry.Scheme.Hom
