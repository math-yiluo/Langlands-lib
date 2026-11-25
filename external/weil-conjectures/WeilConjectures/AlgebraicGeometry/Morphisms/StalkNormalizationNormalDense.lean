/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationDensePart

/-!
# Normality and density of the localized relative normalization

## References

* Stacks Project, Tags 035L (normality of relative normalization), 035K (locality), 035I
  (dominance), 0307 (localization), and 0EYJ
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Localization of the relative normalization is normal, with dense punctured source. -/
theorem stalk_normalization_normal_and_dense {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
    let l := pullback.fst c (S.fromSpecStalk s)
    let n := pullback.snd f.fromNormalization l
    (∀ z : (pullback f.fromNormalization l : Scheme.{u}),
      IsDomain ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z)) ∧
    Dense (↑(n ⁻¹ᵁ (l ⁻¹ᵁ (c ⁻¹ᵁ U))) :
      Set (pullback f.fromNormalization l : Scheme.{u})) := by
  exact ⟨stalk_normalization_normal_part hS c U PA s,
    stalk_normalization_dense_part hS c U PA s⟩

end AlgebraicGeometry.Scheme
