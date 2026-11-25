/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.CartierKummerClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion

/-!
# The glued Kummer class in the smooth case

For a regular closed immersion `i : Z ⟶ X` of a regular scheme into a scheme smooth over a
perfect field, the purity hypothesis `AlgebraicGeometry.Etale.SupportedTatePure` of
`WeilConjectures.EtaleCohomology.Purity.Smooth.CartierKummerClass` holds by purity, and the glued
class `AlgebraicGeometry.Etale.pureFundamentalClass` is the fundamental class
`AlgebraicGeometry.Etale.fundamentalClass`. In particular, for an effective Cartier divisor in a
scheme smooth over a perfect field, the class `AlgebraicGeometry.Etale.cartierKummerClass` is
defined with no further hypothesis.

## Main statements

- `AlgebraicGeometry.Etale.supportedTatePure_of_smooth`
- `AlgebraicGeometry.Etale.pureFundamentalClass_eq_fundamentalClass`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Z : Scheme.{u}} [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ X] (c : ℕ) (i : Z ⟶ X)
  [IsRegularImmersion c i] {k : Type u} [Field k] [PerfectField k]

/-- Under smoothness over a perfect field and regularity of `Z`, a regular closed immersion
satisfies the purity hypothesis
(`AlgebraicGeometry.Etale.exists_iso_singleFunctor_rightDerivedLowerShriek_of_isRegularImmersion`).
-/
theorem supportedTatePure_of_smooth (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) :
    SupportedTatePure Λ c i :=
  exists_iso_singleFunctor_rightDerivedLowerShriek_of_isRegularImmersion Λ c i aX hZ

/-- For a regular immersion of a regular scheme into a scheme smooth over a perfect field, the
glued class is the fundamental class `AlgebraicGeometry.Etale.fundamentalClass`: both restrict
to the frame classes. -/
theorem pureFundamentalClass_eq_fundamentalClass (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (hP : SupportedTatePure Λ c i) :
    pureFundamentalClass Λ c i hP = fundamentalClass Λ c i aX hZ :=
  (existsUnique_pureFundamentalClass Λ c i hP).unique
    (frameRestriction_pureFundamentalClass Λ c i hP)
    (frameRestriction_fundamentalClass Λ c i aX hZ)

end Etale

end AlgebraicGeometry
