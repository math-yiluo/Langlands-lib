/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficientBaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback

/-!
# The first Chern class with coefficients in `Λ`

The first Chern class `c₁(L) : Λ_X ⟶ Λ_X(1)[2]` of a line bundle `L` is the Kummer boundary of
the class of `L` in `H¹(X, 𝔾ₘ) = Pic(X)`, with coefficients extended from `μₙ` to
`Λ(1) = μₙ ⊗ Λ` (`AlgebraicGeometry.Etale.chernClass`). It is additive
(`AlgebraicGeometry.Etale.chernClass_mul`) and compatible with pullback.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

/-- The classical first Chern class `c₁(L) ∈ H²(X, μₙ)` of a line bundle: the Kummer boundary of
its class in `H¹(X, 𝔾ₘ) = Pic(X)`. -/
noncomputable def Scheme.Pic.chernClassRootsOfUnity {X : Scheme.{u}} (n : ℕ)
    (hn : IsUnit (n : Γ(X, ⊤))) (L : X.Pic) : Sheaf.H (X.rootsOfUnitySheaf n) 2 :=
  X.kummerδ₁ n hn (Pic.toCohomologicalPicardGroup X L)

lemma Scheme.Pic.chernClassRootsOfUnity_mul {X : Scheme.{u}} (n : ℕ) (hn : IsUnit (n : Γ(X, ⊤)))
    (L L' : X.Pic) :
    chernClassRootsOfUnity n hn (L * L') =
      chernClassRootsOfUnity n hn L + chernClassRootsOfUnity n hn L' := by
  rw [chernClassRootsOfUnity, Pic.toCohomologicalPicardGroup_mul, map_add]
  rfl

lemma Scheme.Pic.chernClassRootsOfUnity_map {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ)
    (hY : IsUnit (n : Γ(Y, ⊤))) (hX : IsUnit (n : Γ(X, ⊤))) (L : Y.Pic) :
    rootsOfUnityCohomologyMap g n 2 (chernClassRootsOfUnity n hY L) =
      chernClassRootsOfUnity n hX (Pic.map g L) := by
  rw [chernClassRootsOfUnity, chernClassRootsOfUnity, rootsOfUnityCohomologyMap_kummerδ₁,
    gmCohomologyMap_toCohomologicalPicardGroup]

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) [CompactSpace X]
  [QuasiSeparatedSpace X] [HasInvertibleExponent Λ X] [NeZero (ringChar Λ)]

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- Blueprint `proposition-purity-vector-bundles` (the class): the first Chern class
`c₁(L) : Λ_X ⟶ Λ_X(1)[2]` of a line bundle `L`, the image of the class of `L` in
`H¹(X, 𝔾ₘ) = Pic(X)` under the Kummer boundary `H¹(X, 𝔾ₘ) ⟶ H²(X, μₙ)` followed by the coefficient
extension `H²(X, μₙ) ⟶ H²(X, μₙ ⊗ Λ) = Hom(Λ_X, Λ_X(1)[2])`. -/
noncomputable def chernClass (L : X.Pic) :
    constantComplex Λ X ⟶ (tateTwistObject Λ X 1)⟦(2 : ℤ)⟧ :=
  (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom ≫
    Abelian.Ext.homAddEquiv (kummerCoefficientMap Λ X 2
      (Pic.chernClassRootsOfUnity (ringChar Λ) (isUnit_ringChar_of_hasInvertibleExponent X) L)) ≫
    (tateTwistObjectOneIso X Λ).inv⟦(2 : ℤ)⟧'

/-- **Additivity of the first Chern class**: `c₁(L ⊗ L') = c₁(L) + c₁(L')`. -/
lemma chernClass_mul (L L' : X.Pic) :
    chernClass Λ X (L * L') = chernClass Λ X L + chernClass Λ X L' := by
  simp only [chernClass, Pic.chernClassRootsOfUnity_mul, map_add, Preadditive.add_comp,
    Preadditive.comp_add]

end Etale

end AlgebraicGeometry
