/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
public import WeilConjectures.CategoryTheory.FinitePrecoverage
public import Mathlib.CategoryTheory.Category.Cat
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteSystemPairs.SiteSystemStrictificationCategory
import WeilConjectures.CategoryTheory.Site.SiteSystemFiniteCoverings
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Data.Finset.Order

/-!
# The finite colimit construction for coherent affine étale sites

Source: Stacks Project, Categories 004A; Sites 0A34 and 09YL; Étale Cohomology 0EYL.
(blueprint: lem-weil-pbc-affine-etale-finite-colimit-construction).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace PresentationPairs

open CategoryTheory.SiteSystemPairs
variable {I : Type u} [Preorder I] (C : I → Cat.{u, u + 1})
  (U : ∀ i j, i ≤ j → C i ⥤ C j)
  (gamma : ∀ i j k (h : i ≤ j) (h' : j ≤ k), U i j h ⋙ U j k h' ≅ U i k (h.trans h'))
  (T : Type (u + 1)) [Category.{u} T] (v : ∀ i, C i ⥤ T)
  (delta : ∀ i j (h : i ≤ j), U i j h ⋙ v j ≅ v i)
variable (hdelta : ∀ i j k (h : i ≤ j) (h' : j ≤ k) (A : C i),
  (v k).map ((gamma i j k h h').hom.app A) ≫ (delta i k (h.trans h')).hom.app A =
    (delta j k h').hom.app ((U i j h).obj A) ≫ (delta i j h).hom.app A)
variable [Nonempty I] [IsDirected I (· ≤ ·)]
variable (hUid : ∀ i, U i i le_rfl = 𝟭 (C i))
  (hgammaRight : ∀ i k (h : i ≤ k),
    HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
  (hgamma : ∀ i j k l (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (A : C i),
    (gamma j k l h' h'').hom.app ((U i j h).obj A) ≫
      (gamma i j l h (h'.trans h'')).hom.app A =
    (U k l h'').map ((gamma i j k h h').hom.app A) ≫
      (gamma i k l (h.trans h') h'').hom.app A)
end PresentationPairs

end AlgebraicGeometry.Scheme
