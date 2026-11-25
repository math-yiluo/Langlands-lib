/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverNaturality
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackComposition
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRestrictedCoefficientComposition

/-! # Bundled formula for composition of raw cohomology pullbacks

Source: Stacks Project, Tag 09Z1, canonical comparison maps.
(blueprint: lem-sbc-higher-image-raw-pullback-composition-formula).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] higherDirectImageRawOverComplex
  higherDirectImageRawOverCoefficient

private theorem restrictedCoefficient_comp
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {A B C : Over W} (f : A ⟶ B) (g : B ⟶ C) :
    (upperStarPlusComp (ModuleCat.{u + 1} Λ) f.left g.left).hom.app
        (higherDirectImageRawOverComplex Λ G C) ≫
      D+((f.left)^*[ModuleCat.{u + 1} Λ]).map
        (higherDirectImageRawOverCoefficient Λ G g) ≫
      higherDirectImageRawOverCoefficient Λ G f =
        higherDirectImageRawOverCoefficient Λ G (f ≫ g) := by
  convert (closePre := false) (closePost := false) (typeEqs := true) (sameFun := false)
    higherDirectImageRestrictedCoefficient_comp Λ G f g using 12
  all_goals first
    | exact higherDirectImageRawOverCoefficient_heq Λ G _
    | exact higherDirectImageRawOverComplex_eq Λ G _

/-- The explicit raw pullback formula is compositional as a function on classes.
Source: Stacks Project, Tag 09Z1, canonical comparison maps. The proof expands the
five factors, applies derived inverse-image composition, upper-star associativity,
single-functor composition, and shift compatibility.
(blueprint: lem-sbc-higher-image-raw-pullback-composition-formula) -/
theorem higherDirectImageRawOverPullback_function_comp
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B C : Over W} (f : A ⟶ B) (g : B ⟶ C) (U : S.Etale) :
    higherDirectImageRawOverPullback Λ k G q (f ≫ g) U =
      (higherDirectImageRawOverPullback Λ k G q f U) ∘
        (higherDirectImageRawOverPullback Λ k G q g U)  := by
  funext z
  change higherDirectImageRawTrianglePullback Λ (f.left ≫ g.left)
      (C.hom ≫ k) (A.hom ≫ k)
      (by rw [Category.assoc, ← Category.assoc g.left C.hom k, Over.w,
        ← Category.assoc, Over.w]) q
      (higherDirectImageRawOverComplex Λ G C) (higherDirectImageRawOverComplex Λ G A)
      (higherDirectImageRawOverCoefficient Λ G (f ≫ g)) U z = _
  exact (congrArg (fun v ↦ higherDirectImageRawTrianglePullback Λ (f.left ≫ g.left)
      (C.hom ≫ k) (A.hom ≫ k)
      (by rw [Category.assoc, ← Category.assoc g.left C.hom k, Over.w,
        ← Category.assoc, Over.w]) q
      (higherDirectImageRawOverComplex Λ G C) (higherDirectImageRawOverComplex Λ G A)
      v U z) (restrictedCoefficient_comp Λ G f g)).symm.trans
    (higherDirectImageRawTrianglePullback_comp Λ f.left g.left
      (C.hom ≫ k) (B.hom ≫ k) (A.hom ≫ k)
      (by rw [← Category.assoc, Over.w])
      (by rw [← Category.assoc, Over.w]) q
      (higherDirectImageRawOverComplex Λ G C) (higherDirectImageRawOverComplex Λ G B)
      (higherDirectImageRawOverComplex Λ G A)
      (higherDirectImageRawOverCoefficient Λ G g)
      (higherDirectImageRawOverCoefficient Λ G f) U z)

end AlgebraicGeometry.Etale
