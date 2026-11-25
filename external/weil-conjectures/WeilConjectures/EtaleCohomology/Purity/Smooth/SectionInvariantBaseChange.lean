/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange

/-!
# Base change of section invariants

In a cartesian square `g' ≫ f = f' ≫ g` with sections `s` of `f` and `s'` of `f'` compatible
with `g'`, the canonical base change map of dualizing complexes `Lg'^* ω_f ⟶ ω_{f'}`
(`AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap`) induces
`Lg^* 𝒞(f, s) ≅ 𝒞(f', s')` on section invariants when it is invertible, which is the case for
`f` smooth (`proposition-exceptional-inverse-image-smooth-morphism` (c)). These are the fibre
identifications of the deformation to the normal cone (`prose-09-12` (1)).

## Main definitions

- `AlgebraicGeometry.Etale.sectionInvariantBaseChangeIso`: `Lg^* 𝒞(f, s) ≅ 𝒞(f', s')`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
  {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} [HasCompactification f] [HasCompactification f']
  [QuasiCompact f']

/-- Blueprint `prose-09-12` (1): *base change of section invariants.* In a
cartesian square `g' ≫ f = f' ≫ g` whose base change map of dualizing complexes
`Lg'^* ω_f ⟶ ω_{f'}` is invertible, and for sections `s` of `f` and `s'` of `f'` with
`s' ≫ g' = g ≫ s`,

`Lg^* 𝒞(f, s) = Lg^* Ls^* ω_f ≅ Ls'^* Lg'^* ω_f ≅ Ls'^* ω_{f'} = 𝒞(f', s')`. -/
noncomputable def sectionInvariantBaseChangeIso (sq : IsPullback g' f' f g)
    [IsIso (dualizingComplexBaseChangeMap Λ sq)] (s : Y ⟶ X) (s' : Y' ⟶ X')
    (hs : s' ≫ g' = g ≫ s) :
    (upperStar (ModuleCat.{u + 1} Λ) g).leftDerivedFunctor.obj (sectionInvariant Λ f s) ≅
      sectionInvariant Λ f' s' :=
  ((leftDerivedUpperStarComp _ g s).app _).symm ≪≫
    (leftDerivedUpperStarComp _ s' g' (g ≫ s) hs.symm).app _ ≪≫
    (upperStar (ModuleCat.{u + 1} Λ) s').leftDerivedFunctor.mapIso
      (asIso (dualizingComplexBaseChangeMap Λ sq))

/-- Blueprint `proposition-exceptional-inverse-image-smooth-morphism` (c): for `f` smooth of
relative dimension `d` over a quasi-separated base, the base change map of dualizing complexes
`Lg'^* ω_f ⟶ ω_{f'}` is an isomorphism. -/
theorem isIso_dualizingComplexBaseChangeMap_of_smoothOfRelativeDimension [QuasiSeparatedSpace Y]
    [HasInvertibleExponent Λ X] (d : ℕ) [SmoothOfRelativeDimension d f]
    (sq : IsPullback g' f' f g) : IsIso (dualizingComplexBaseChangeMap Λ sq) := by
  rw [isIso_dualizingComplexBaseChangeMap_iff]
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ f d sq
  infer_instance

end AlgebraicGeometry.Etale
