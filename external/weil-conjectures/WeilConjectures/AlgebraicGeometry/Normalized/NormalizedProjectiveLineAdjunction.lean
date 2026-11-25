/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedTateLineComparison
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteP1AdjunctionOfIntegrals

/-! # The projective-line adjunction for a normalized twist datum

The projective-line geometric input to the affine-space induction.

## Implementation details

The finite-root splitting (`exists_arbitraryBaseFiniteP1Integrals`) and the Tate line comparison
(`nonempty_normalizedTateLineComparison`) are chosen, as the base results only assert their
existence.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The projective-line adjunction `Rq_* ⊣ Lq^*(1)[2]` determined by a finite-root splitting, a
supported diagonal class `κ` whose two diagonal integrals are identities, and an identification
`e: Λ(1) ≅ Λ_N(1)` of the Tate object on the projective line with the finite root-of-unity
line: the adjunction
`finiteP1AdjunctionOfIntegrals` transported along `e`. Its counit is the trace counit, see
`normalizedProjectiveLineAdjunctionOfIntegrals_counit_app`. -/
noncomputable def normalizedProjectiveLineAdjunctionOfIntegrals
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
    (N : ℕ) (hN : 0 < N) (hΛ : (N : Λ) = 0)
    (t : OrdinaryFiniteTwistTransport Λ N hΛ)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting Λ N hΛ t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange Λ N hΛ t d)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (κ : Abelian.Ext
      (C := Sheaf
        (Limits.pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ))
      ((lowerStar (ModuleCat.{u + 1} Λ)
        (Z := ProjectiveLine S)
        (Y := Limits.pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (Limits.pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant Λ (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (Limits.pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N Λ hΛ) 2)
    (hκ : ∀ a : Bool, ordinaryFiniteP1DiagonalSupportedMap Λ N hΛ S a κ ≫
        arbitraryBaseFiniteP1DiagonalTrace Λ N hΛ t d S hS a =
      𝟙 (ordinaryFiniteUnit Λ (ProjectiveLine S)))
    (e : tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1 ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateLine ℙ(Option (ULift.{u} (Fin 1)); S) N Λ hΛ)) :
    R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)_*[ModuleCat.{u + 1} Λ]) ⊣
      L((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1 :=
  (finiteP1AdjunctionOfIntegrals Λ N hN hΛ t d hbc S hS κ hκ).ofNatIsoRight
    (Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      ((derivedTensor (ModuleCat.{u + 1} Λ) ℙ(Option (ULift.{u} (Fin 1)); S)).flip.mapIso e.symm)
      (shiftFunctor _ (2 : ℤ))))

/-- The counit of `normalizedProjectiveLineAdjunctionOfIntegrals` is the trace counit of
`finiteP1AdjunctionOfIntegrals` (see `finiteP1AdjunctionOfIntegrals_eq`), after
replacing `Λ(1)` by the finite root-of-unity line along `e`. -/
@[simp]
theorem normalizedProjectiveLineAdjunctionOfIntegrals_counit_app
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
    (N : ℕ) (hN : 0 < N) (hΛ : (N : Λ) = 0)
    (t : OrdinaryFiniteTwistTransport Λ N hΛ)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting Λ N hΛ t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange Λ N hΛ t d)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (κ : Abelian.Ext
      (C := Sheaf
        (Limits.pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ))
      ((lowerStar (ModuleCat.{u + 1} Λ)
        (Z := ProjectiveLine S)
        (Y := Limits.pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (Limits.pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant Λ (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (Limits.pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N Λ hΛ) 2)
    (hκ : ∀ a : Bool, ordinaryFiniteP1DiagonalSupportedMap Λ N hΛ S a κ ≫
        arbitraryBaseFiniteP1DiagonalTrace Λ N hΛ t d S hS a =
      𝟙 (ordinaryFiniteUnit Λ (ProjectiveLine S)))
    (e : tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1 ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateLine ℙ(Option (ULift.{u} (Fin 1)); S) N Λ hΛ))
    (K : DerivedCategoryModule Λ S) :
    (normalizedProjectiveLineAdjunctionOfIntegrals Λ N hN hΛ t d hbc S hS κ hκ e).counit.app K =
      (R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)_*[ModuleCat.{u + 1} Λ])).map
          ((shiftFunctor _ (2 : ℤ)).map
            (((derivedTensor (ModuleCat.{u + 1} Λ) ℙ(Option (ULift.{u} (Fin 1)); S)).obj
              ((L((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)^*[ModuleCat.{u + 1} Λ])).obj K)).map
                e.hom)) ≫
        (finiteP1AdjunctionOfIntegrals Λ N hN hΛ t d hbc S hS κ hκ).counit.app K :=
  rfl

/-- **The projective-line adjunction** `Rq_* ⊣ Lq^*(1)[2]` for a normalized Tate twist: the
adjunction `normalizedProjectiveLineAdjunctionOfIntegrals` for chosen finite-root splitting
data, diagonal class and Tate line comparison. -/
noncomputable def normalizedProjectiveLineAdjunction
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)_*[ModuleCat.{u + 1} Λ]) ⊣
      L((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)^*[ModuleCat.{u + 1} Λ]) ⋙
        twistShift Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1 :=
  have : HasInvertibleExponent Λ ℙ(Option (ULift.{u} (Fin 1)); S) :=
    .of_hom (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
  have hN := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := S)
  have hint := exists_arbitraryBaseFiniteP1Integrals hN.choose hN.choose_spec.1 Λ
    hN.choose_spec.2.1
  have hi := hint.choose_spec.choose_spec.2 S hN.choose_spec.2.2
  normalizedProjectiveLineAdjunctionOfIntegrals Λ hN.choose hN.choose_spec.1 hN.choose_spec.2.1
    hint.choose hint.choose_spec.choose hint.choose_spec.choose_spec.1 S hN.choose_spec.2.2
    (finiteP1DiagonalClass Λ _ _ _ _ S _ hi) (finiteP1DiagonalClass_integral Λ _ _ _ _ S _ hi)
    (nonempty_normalizedTateLineComparison Λ hN.choose hN.choose_spec.1 hN.choose_spec.2.1 _
      (by simpa using
        hN.choose_spec.2.2.map (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S).appTop.hom)).some

end AlgebraicGeometry.Etale
