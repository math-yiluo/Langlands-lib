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
public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimTwoTransfer

/-!
# Boundary stalks of the localized normalization have dimension at least two

## References

* Stacks Project, Tags 0EYJ, 0337, 00LK, 033C and 00H8
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- Boundary stalks of the finite localized normalization have dimension at least two. -/
theorem stalk_normalization_boundary_dimension_two {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    IsFinite n → ∀ z : (pullback
      (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a) : Scheme.{u}),
      n z ∉ (pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U) →
      (2 : WithBot ℕ∞) ≤ ringKrullDim
        ((pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
          (pullback.fst c a) : Scheme.{u}).presheaf.stalk z) := by
  apply stalk_normalization_boundary_dimension_two_transfer hS c U PA s
  exact stalk_normalization_boundary_dimension_two_target c U s hmin hdepth
end AlgebraicGeometry.Scheme
