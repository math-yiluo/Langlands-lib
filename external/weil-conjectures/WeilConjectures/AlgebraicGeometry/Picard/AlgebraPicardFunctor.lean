/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import WeilConjectures.AlgebraicGeometry.Picard.AffineRestriction

/-!
# The Picard functor on algebras

Let `k` be a commutative ring and `f: X ⟶ Spec k` a `k`-scheme. The Picard functor of a curve
`X / k` is often presented on `k`-algebras, as the fppf sheafification of
`R ↦ Pic (X ×_k Spec R)`. We define this functor
on `(CommAlgCat k)ᵒᵖ`, the fppf topology being induced along
`Spec: (CommAlgCat k)ᵒᵖ ⥤ Over (Spec k)` (`AlgebraicGeometry.algSpec`), and show that it agrees
with the restriction of the relative Picard functor `Pic_{X/k}` of `AlgebraicGeometry.picardFunctor`
along `Spec`.

## Main definitions

- `AlgebraicGeometry.algFppfTopology k`: the fppf topology on `(CommAlgCat k)ᵒᵖ`.
- `AlgebraicGeometry.algPicardPresheaf f`: the presheaf `R ↦ Pic (X ×_k Spec R)` on `k`-algebras.
- `AlgebraicGeometry.algPicardFunctor f`: its fppf sheafification.

## Main statements

- `AlgebraicGeometry.algPicardFunctorIso`: `algPicardFunctor f` is the restriction of
  `picardFunctor f` along `Spec`; in particular `Pic_{X/k}(Spec R) ≅ Pic^{sc}_{X/k}(R)`
  (`AlgebraicGeometry.algPicardFunctorObjIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable {k : CommRingCat.{u}} {X : Scheme.{u}}

/-- The affine `k`-schemes `Spec R`, for `R` a `k`-algebra, are cover-dense in the big fppf site of
`Spec k`: the affine open cover of a `k`-scheme `T` is a Zariski covering, hence an fppf covering,
by spectra of `k`-algebras. -/
instance algSpec.isCoverDense :
    (algSpec k).IsCoverDense (Scheme.fppfTopology.over (Spec k)) where
  is_cover T := by
    rw [GrothendieckTopology.mem_over_iff]
    refine (Scheme.fppfTopology).superset_covering ?_
      (Scheme.zariskiTopology_le_fppfTopology _
        T.left.affineOpenCover.openCover.mem_grothendieckTopology)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    rw [Sieve.overEquiv_iff]
    have h := (Sieve.coverByImage (algSpec k) T).downward_closed
      (Presieve.in_coverByImage (algSpec k) (X := T)
        (Y := op ((commAlgCatEquivUnder k).inverse.obj
          (Under.mk (Spec.preimage (T.left.affineOpenCover.openCover.f i ≫ T.hom)))))
        (Over.homMk (T.left.affineOpenCover.openCover.f i) (Spec.map_preimage _).symm))
      (Over.homMk (U := Over.mk (T.left.affineOpenCover.openCover.f i ≫ T.hom)) (𝟙 _)
        ((Category.id_comp _).trans (Spec.map_preimage _)))
    convert h using 1
    exact Over.OverMorphism.ext (by simp)

variable (k) in
/-- The fppf topology on (the opposite of) the category of `k`-algebras: a family of morphisms
`R ⟶ R_i` of `k`-algebras is a covering if `(Spec R_i ⟶ Spec R)_i` is an fppf covering, i.e. the
topology induced along `Spec : (CommAlgCat k)ᵒᵖ ⥤ Over (Spec k)`. -/
noncomputable abbrev algFppfTopology : GrothendieckTopology (CommAlgCat k)ᵒᵖ :=
  (algSpec k).inducedTopology (Scheme.fppfTopology.over (Spec k))

/-- The Picard presheaf on `k`-algebras of a `k`-scheme `f : X ⟶ Spec k`: it sends a `k`-algebra
`R` to `Pic (X ×_k Spec R)`, and a morphism of `k`-algebras to the pullback map on Picard
groups. -/
noncomputable abbrev algPicardPresheaf (f : X ⟶ Spec k) : (CommAlgCat k)ᵒᵖᵒᵖ ⥤ Type (u + 1) :=
  (algSpec k).op ⋙ picardPresheaf f

/-- **The Picard functor on `k`-algebras.** For a `k`-scheme `f: X ⟶ Spec k`, this is the fppf
sheafification on `k`-algebras of `R ↦ Pic (X ×_k Spec R)`. -/
noncomputable def algPicardFunctor (f : X ⟶ Spec k) :
    Sheaf (algFppfTopology k) (Type (u + 1)) :=
  (presheafToSheaf (algFppfTopology k) (Type (u + 1))).obj (algPicardPresheaf f)

/-- **The Picard functor agrees with its presentation on algebras.** For a `k`-scheme
`f: X ⟶ Spec k`, the restriction of the relative Picard functor `Pic_{X/k}`
(`AlgebraicGeometry.picardFunctor`) along `Spec: (CommAlgCat k)ᵒᵖ ⥤ Over (Spec k)` is canonically
isomorphic to `AlgebraicGeometry.algPicardFunctor f`. -/
noncomputable def algPicardFunctorIso (f : X ⟶ Spec k) :
    algPicardFunctor f ≅
      ((algSpec k).sheafPushforwardContinuous (Type (u + 1)) (algFppfTopology k)
        (Scheme.fppfTopology.over (Spec k))).obj (picardFunctor f) :=
  (Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility (algFppfTopology k)
    (Scheme.fppfTopology.over (Spec k)) (algSpec k) (Type (u + 1))).app (picardPresheaf f)

/-- The values of the two Picard functors agree: `Pic^{sc}_{X/k}(R) ≅ Pic_{X/k}(Spec R)` for every
`k`-algebra `R`, naturally in `R`. -/
noncomputable def algPicardFunctorObjIso (f : X ⟶ Spec k) (R : CommAlgCat k) :
    (algPicardFunctor f).obj.obj (op (op R)) ≅
      (picardFunctor f).obj.obj (op ((algSpec k).obj (op R))) :=
  ((sheafToPresheaf _ _).mapIso (algPicardFunctorIso f)).app (op (op R))

end AlgebraicGeometry
