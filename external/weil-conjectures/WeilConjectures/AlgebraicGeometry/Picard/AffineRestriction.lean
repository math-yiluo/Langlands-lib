/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import WeilConjectures.AlgebraicGeometry.Picard.Defs

/-!
# The Picard functor on affine schemes

Let `f : X ⟶ S` be a morphism of schemes. The relative Picard functor
`AlgebraicGeometry.picardFunctor f` is the fppf sheafification of the Picard presheaf
`T ↦ Pic (X_T)` on the category of all `S`-schemes. In the chapter on smooth curves the Picard
functor of a curve `C / k` is presented on `k`-algebras, as the fppf sheafification of
`R ↦ Pic (C ×_k Spec R)`. The two agree on affine schemes: the affine `S`-schemes form a dense
subsite of the big fppf site of `S` (every `S`-scheme has a Zariski, hence fppf, covering by
affine schemes), so restricting a sheafification to the affine `S`-schemes is the
sheafification of the restriction.

## Main definitions

- `AlgebraicGeometry.Scheme.AffineOver S`: the full subcategory of affine `S`-schemes, with the
  topology induced by the fppf topology of `Over S`.

## Main statements

- `AlgebraicGeometry.picardFunctorAffineRestrictionIso`: the restriction of `Pic_{X/S}` to affine
  `S`-schemes is the fppf sheafification of the restriction of the Picard presheaf.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

variable (S) in
/-- The full subcategory of `Over S` of the affine `S`-schemes `T ⟶ S`. -/
abbrev Scheme.AffineOver : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun T : Over S ↦ IsAffine T.left

variable (S) in
/-- The inclusion of the affine `S`-schemes into all `S`-schemes. -/
abbrev Scheme.AffineOver.ι : Scheme.AffineOver S ⥤ Over S :=
  ObjectProperty.ι _

/-- The affine `S`-schemes are cover-dense in the big fppf site of `S`: the affine open cover of
an `S`-scheme `T` is a Zariski covering, hence an fppf covering, by affine `S`-schemes. -/
instance Scheme.AffineOver.isCoverDense :
    (Scheme.AffineOver.ι S).IsCoverDense (Scheme.fppfTopology.over S) where
  is_cover T := by
    rw [GrothendieckTopology.mem_over_iff]
    refine (Scheme.fppfTopology).superset_covering ?_
      (zariskiTopology_le_fppfTopology _ T.left.affineCover.mem_grothendieckTopology)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    rw [Sieve.overEquiv_iff]
    exact Presieve.in_coverByImage (Scheme.AffineOver.ι S)
      (X := T)
      (Y := ⟨Over.mk (T.left.affineCover.f i ≫ T.hom), inferInstanceAs (IsAffine (Spec _))⟩)
      (Over.homMk (T.left.affineCover.f i))

variable (S) in
/-- The topology on the affine `S`-schemes induced by the fppf topology. -/
abbrev Scheme.AffineOver.topology : GrothendieckTopology (Scheme.AffineOver S) :=
  (Scheme.AffineOver.ι S).inducedTopology (Scheme.fppfTopology.over S)

/-- **The Picard functor agrees with its affine presentation.** For `f: X ⟶ S`, the restriction of
the relative Picard functor `Pic_{X/S}` to affine `S`-schemes `T = Spec R` is canonically the fppf
sheafification, on the site of affine `S`-schemes, of `Spec R ↦ Pic (X ×_S Spec R)`. For
`S = Spec k` and `X` a smooth projective curve this is the Picard functor of the chapter on smooth
curves, which is presented on `k`-algebras. -/
noncomputable def picardFunctorAffineRestrictionIso (f : X ⟶ S) :
    (presheafToSheaf (Scheme.AffineOver.topology S) (Type (u + 1))).obj
        ((Scheme.AffineOver.ι S).op ⋙ picardPresheaf f) ≅
      ((Scheme.AffineOver.ι S).sheafPushforwardContinuous (Type (u + 1))
        (Scheme.AffineOver.topology S) (Scheme.fppfTopology.over S)).obj (picardFunctor f) :=
  (Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility (Scheme.AffineOver.topology S)
    (Scheme.fppfTopology.over S) (Scheme.AffineOver.ι S) (Type (u + 1))).app (picardPresheaf f)

end AlgebraicGeometry
