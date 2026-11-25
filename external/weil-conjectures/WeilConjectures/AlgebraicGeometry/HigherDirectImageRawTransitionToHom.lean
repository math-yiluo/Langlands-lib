/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback


public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackExtension
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTransitionToHomCore
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf

/-! # Raw pullback and the derived-Hom comparison

Source: Stacks Project, Tags 03Q8 and 09Z1, canonical comparison maps.
(blueprint: sbc-lem-higher-image-raw-transition-to-hom).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Pullback of raw classes commutes with the comparison to morphisms from the free sheaf,
before evaluating those morphisms on sections, with a specified coefficient morphism.
Source: Stacks Project, Tags 03Q8 and 09Z1, canonical cohomology comparison maps.
(blueprint: sbc-lem-higher-image-raw-transition-to-hom).

Proof: Write the comparison as the derived adjunction on the class, preceded by the
single-complex comparison, followed by degree-zero homology and the homology shift
comparison. Write the derived transition as the unit for h', pullback composition,
and pullback of the counit for h. Naturality of the unit and the adjunction triangle
identity show that composing the adjunct of z with this transition is the adjunct
of the pulled-back class. Compatibility of pullback composition with the single
complexes identifies its source map with the first two displayed factors. The shift
compatibility of the unit, counit, and pullback composition transports the shift
comparison past this identity, giving the fourth factor. Apply degree-zero homology,
use naturality of the identification H^0(L[q]) = H^q(L), and precompose with the inverse
single-complex homology comparison. This gives the stated equality of morphisms from
the free sheaf, without evaluation. Finally use naturality in the coefficient morphism v to
postcompose on raw classes by v[q] and on higher images by H^q(Rh'_*v).
The argument works for every integer q, every bounded-below K, and every commutative
triangle, including identity arrows and zero objects; it uses no qcqs hypotheses. -/
theorem higherDirectImageRawTransition_toHom
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K')
    (U : S.Etale) (z : (higherDirectImagePresheaf Λ h q K).obj (op U)) :
    (higherDirectImagePresheafToHom Λ h' q K').app (op U)
        (higherDirectImageRawTrianglePullback Λ a h h' w q K K' v U z) =
      (higherDirectImagePresheafToHom Λ h q K).app (op U) z ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map
          (lowerStarPlusTransition Λ a h h' w K ≫
            R+((h')_*[ModuleCat.{u + 1} Λ]).map v) := by
  have H := higherDirectImageRawTransition_toHom_core Λ a h h' w q K K' v U
  have Hz := congrArg (fun f => f z) H
  exact Hz

end AlgebraicGeometry.Etale
