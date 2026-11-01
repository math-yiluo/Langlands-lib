import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Lifting a covering family of open scheme charts across a thickening

The single-open lifting comes from Stacks Project Tag 05ZP. The indexed
formulation, base-change thickenings and covering conclusion are derived.
This module defines the proposition and supplies no proof of it.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A covering family of open scheme charts lifts across any space thickening,
with the same indices, actual pullback squares and a covering lifted family. -/
def OpenFamilyLiftingStatement : Prop :=
  ∀ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (i : X ⟶ Y),
    IsThickening (hom i) →
    ∀ (I : Type u) (U : I → Over S)
      (a : ∀ k, (schemeYoneda S).obj (U k) ⟶ X.presheaf),
      (∀ k, IsOpenImmersion (a k)) →
      CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) (Sigma.desc a) →
      ∃ (V : I → AlgebraicSpace S) (j : ∀ k, V k ⟶ Y)
        (c : ∀ k, (schemeToSpace S).obj (U k) ⟶ V k),
        (∀ k, IsOpenImmersion (hom (j k))) ∧
        (∀ k, IsThickening (hom (c k))) ∧
        (∀ k, IsPullback (a k) (hom (c k)) (hom i) (hom (j k))) ∧
        CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
          (Sigma.desc (fun k => hom (j k)))

end Langlands.AlgebraicGeometry.AlgebraicSpace
