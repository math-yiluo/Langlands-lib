/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions


import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitionCoreComposition
import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitionNaturality

/-! # Composition of higher direct image triangles

Source: Stacks Project, Tag 09Z1, canonical comparison maps, and Tag 03Q8.
(blueprint: lem-sbc-higher-image-transition-composition).
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The two successive transitions in a tower of commutative triangles agree with
its composite, after the ordinary pullback composition comparison.
Source: Stacks Project, Tag 09Z1, canonical comparisons; Tag 03Q8.
(blueprint: lem-sbc-higher-image-transition-composition).

Proof: Before homology, expand both transitions as the adjoints of the pulled-back
counits. Express the unit for the composite pullback adjunction as the successive
units, transported through the inverse-image composition comparison. Naturality
moves the middle unit past the first counit; the triangle identity cancels this
pair. Associativity of the pullback comparisons identifies the remaining expression
with the transition for `b ≫ a`. For a sheaf placed in degree zero, the exact-functor
comparison with singleFunctor commutes with composition: compute on the degree-zero
complex using the factorization through the homotopy category. This identifies the
remaining derived pullback comparison with singleFunctor applied to the ordinary
pullback comparison. Naturality in the coefficient sheaf moves the map f past the second transition.
Apply homology, preserving compositions. The equalities of the
three structure morphisms occur only as proof-irrelevant transports. -/
theorem higher_direct_image_transition_composition
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' Y'' : Scheme.{u}}
    (a : Y' ⟶ Y) (b : Y'' ⟶ Y') (h : Y ⟶ S) (h' : Y' ⟶ S) (h'' : Y'' ⟶ S)
    (wa : a ≫ h = h') (wb : b ≫ h' = h'') (q : ℤ)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (F' : Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (F'' : Sheaf Y''.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : ((a)^*[ModuleCat.{u + 1} Λ]).obj F ⟶ F')
    (g : ((b)^*[ModuleCat.{u + 1} Λ]).obj F' ⟶ F'') :
    higherDirectImageTransition Λ (b ≫ a) h h''
        (by rw [Category.assoc, wa, wb]) q F ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h'')_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) b a).hom.app F ≫
            ((b)^*[ModuleCat.{u + 1} Λ]).map f ≫ g))) =
      (higherDirectImageTransition Λ a h h' wa q F ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h')_*[ModuleCat.{u + 1} Λ]).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map f))) ≫
      (higherDirectImageTransition Λ b h' h'' wb q F' ≫
        (DerivedCategory.Plus.homologyFunctor _ q).map
          (R+((h'')_*[ModuleCat.{u + 1} Λ]).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map g)))  := by
  have hc := higher_direct_image_transition_core_composition Λ a b h h' h'' wa wb q F
  have hn := higher_direct_image_transition_naturality Λ b h' h'' wb q
    (((a)^*[ModuleCat.{u + 1} Λ]).obj F) F' f
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hc, ← reassoc_of% hn]


end AlgebraicGeometry.Etale
