/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-! # Canonical transition maps for higher direct images

These are the unchanged definitions moved from the source Transition module to
allow its continuity proof to import independent coherence and affine-continuity lemmas.
Source: Stacks Project, Tag 09Z1 and Tag 03Q8.
(blueprint: def-sbc-module-higher-image-transitions).
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

section Transition

variable {X Y Y' : Scheme.{u}}

/-- The transition map `Rh_* K ⟶ Rh'_* (a^* K)` attached to a commutative triangle
`a ≫ h = h'`: the unit of `Lh'^* ⊣ Rh'_*` at `Rh_* K`, followed by `Rh'_*` applied to the
composition isomorphism `Lh'^* ≅ Lh^* ⋙ La^*` and to `La^*` of the counit of
`Lh^* ⊣ Rh_*` at `K`. 
(blueprint: def-sbc-module-higher-image-transitions)
-/
noncomputable def Etale.lowerStarPlusTransition (a : Y' ⟶ Y) (h : Y ⟶ X) (h' : Y' ⟶ X)
    (w : a ≫ h = h') (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    R+((h)_*[ModuleCat.{u + 1} Λ]).obj K ⟶
      R+((h')_*[ModuleCat.{u + 1} Λ]).obj (D+((a)^*[ModuleCat.{u + 1} Λ]).obj K) :=
  (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h').unit.app _ ≫
    R+((h')_*[ModuleCat.{u + 1} Λ]).map
      ((eqToIso (by rw [← w]) ≪≫ Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom.app _ ≫
        D+((a)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).counit.app K))

/-- The transition map `R^q h_* F ⟶ R^q h'_* a^* F` of higher direct images attached to a
commutative triangle `a ≫ h = h'`: the degree-`q` homology of
`AlgebraicGeometry.Etale.lowerStarPlusTransition` at `F` placed in degree `0`, followed by the
identification `a^*(F[0]) ≅ (a^* F)[0]`. 
(blueprint: def-sbc-module-higher-image-transitions)
-/
noncomputable def Etale.higherDirectImageTransition (a : Y' ⟶ Y) (h : Y ⟶ X) (h' : Y' ⟶ X)
    (w : a ≫ h = h') (q : ℤ) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.higherDirectImage Λ h q F ⟶
      Etale.higherDirectImage Λ h' q (((a)^*[ModuleCat.{u + 1} Λ]).obj F) :=
  (DerivedCategory.Plus.homologyFunctor _ q).map
    (Etale.lowerStarPlusTransition Λ a h h' w _ ≫
      R+((h')_*[ModuleCat.{u + 1} Λ]).map
        ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))

/-- The transition map of higher direct images along a morphism `φ : U ⟶ V` of schemes over
`W`, for the sheaves pulled back from a fixed sheaf `G` on `W` and the structure morphisms
composed with `k : W ⟶ S`:
`R^q (V → S)_* (G|_V) ⟶ R^q (U → S)_* (G|_U)`. It is
`AlgebraicGeometry.Etale.higherDirectImageTransition` followed by the identification
`φ^*(G|_V) ≅ G|_U`. 
(blueprint: def-sbc-module-higher-image-transitions)
-/
noncomputable def Etale.higherDirectImageOverMap {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) {U V : Over W}
    (φ : U ⟶ V) :
    Etale.higherDirectImage Λ (V.hom ≫ k) q (((V.hom)^*[ModuleCat.{u + 1} Λ]).obj G) ⟶
      Etale.higherDirectImage Λ (U.hom ≫ k) q (((U.hom)^*[ModuleCat.{u + 1} Λ]).obj G) :=
  Etale.higherDirectImageTransition Λ φ.left (V.hom ≫ k) (U.hom ≫ k)
      (by rw [← Category.assoc, Over.w]) q _ ≫
    (DerivedCategory.Plus.homologyFunctor _ q).map (R+((U.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom (Over.w φ).symm).inv.app
          G)))

end Transition

end AlgebraicGeometry
