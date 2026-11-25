/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.ConstructibleSheaf.DistTriang
public import WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.DivisorComplementDirectImage
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion

/-!
# Local constancy of the direct images from the complement of a divisor along the divisor

If `j : U ⟶ X` has the higher direct images of the complement of a divisor `i : D ⟶ X`
(`AlgebraicGeometry.Etale.HasDivisorComplementDirectImages`: `R⁰j_* ℤ/ℓ ≅ ℤ/ℓ`,
`R¹j_* ℤ/ℓ ≅ i_* ℤ/ℓ`, `R^q j_* ℤ/ℓ = 0` for `q ≥ 2`), then for every morphism `ι : Y ⟶ X`
landing in `D` the cohomology sheaves of `ι^* Rj_* ℤ/ℓ` are finite locally constant: they are
`ι^* ℤ/ℓ = ℤ/ℓ`, `ι^* i_* ℤ/ℓ` and `0`, and `ι^* i_* ℤ/ℓ` is the pushforward of `ℤ/ℓ` along the
surjective closed immersion `D ×_X Y ⟶ Y` (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`).

## Main statements

- `AlgebraicGeometry.Etale.HasDivisorComplementDirectImages.hasFiniteLocallyConstantHomology`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The pushforward of the constant sheaf `ℤ/ℓ` along a surjective closed immersion is finite
locally constant. -/
theorem isFiniteLocallyConstantSheaf_lowerStar_constantZModModule {W Y : Scheme.{u}}
    (p : W ⟶ Y) [IsClosedImmersion p] [Surjective p] :
    IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} (ZModCoeff.{u} ℓ) ↦ M →ₗ[_] N)
      (CA := fun M : ModuleCat.{u + 1} (ZModCoeff.{u} ℓ) ↦ M)
      ((p)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj (constantZModModule W ℓ)) := by
  have : IsFiniteLocallyConstantSheaf
      (FA := fun M N : ModuleCat.{u + 1} (ZModCoeff.{u} ℓ) ↦ M →ₗ[ZModCoeff.{u} ℓ] N)
      (CA := fun M : ModuleCat.{u + 1} (ZModCoeff.{u} ℓ) ↦ M)
      ((p)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj
        ((p)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].obj (constantZModModule W ℓ))) :=
    @IsFiniteLocallyConstantSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _ (asIso
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)) p).counit.app
      (constantZModModule W ℓ))).symm (isFiniteLocallyConstantSheaf_constantSheaf _)
  exact IsFiniteLocallyConstantSheaf.of_upperStar p _

variable {ℓ}

/-- Blueprint `lemma-cohomology-near-two-transverse-divisors--1`: if `j : U ⟶ X` has the higher
direct images of the complement of the divisor `i : D ⟶ X`, then for every `ι : Y ⟶ X` with image in
`D` the complex `ι^* Rj_* ℤ/ℓ` has finite locally constant cohomology sheaves. -/
theorem HasDivisorComplementDirectImages.hasFiniteLocallyConstantHomology {U X D Y : Scheme.{u}}
    {j : U ⟶ X} {i : D ⟶ X} [IsClosedImmersion i] (hj : HasDivisorComplementDirectImages ℓ j i)
    (ι : Y ⟶ X) (hι : Set.range ι ⊆ Set.range i) :
    HasFiniteLocallyConstantHomology Y
      ((L((ι)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj
        ((R((j)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj
          ((DerivedCategory.singleFunctor _ 0).obj (constantZModModule U ℓ)))) := by
  intro n
  let K := (R((j)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)])).obj
    ((DerivedCategory.singleFunctor _ 0).obj (constantZModModule U ℓ))
  refine @IsFiniteLocallyConstantSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
    ((leftDerivedUpperStarHomologyFunctorIso _ ι n).app K) ?_
  obtain ⟨q, rfl⟩ | hn : (∃ q : ℕ, n = q) ∨ n < 0 := by
    rcases le_or_gt 0 n with h | h
    · exact Or.inl ⟨n.toNat, (Int.toNat_of_nonneg h).symm⟩
    · exact Or.inr h
  · let e : (DerivedCategory.homologyFunctor _ q).obj K ≅
        higherDirectImage (ZModCoeff.{u} ℓ) j q (constantZModModule U ℓ) :=
      Functor.homologyRightDerivedFunctorObjSingleFunctorIso _ _ q ≪≫
        (Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso _ _ q).symm
    refine @IsFiniteLocallyConstantSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
      ((ι)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].mapIso e).symm ?_
    obtain hq | rfl | rfl : 2 ≤ q ∨ q = 0 ∨ q = 1 := by lia
    · exact IsFiniteLocallyConstantSheaf.of_isZero (Functor.map_isZero _ (hj.1 q hq))
    · obtain ⟨e₀⟩ := hj.2.1
      exact @IsFiniteLocallyConstantSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
        (((ι)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].mapIso e₀ ≪≫
          (Scheme.upperStarConstantSheafIso _ ι).app _).symm) inferInstance
    · obtain ⟨e₁⟩ := hj.2.2
      obtain ⟨e₂⟩ := nonempty_iso_upperStar_lowerStar_constantZModModule i ι ℓ
      have : Surjective (pullback.snd i ι) := ⟨by
        rw [← Set.range_eq_univ, Pullback.range_snd, Set.preimage_eq_univ_iff]
        exact hι⟩
      have := isFiniteLocallyConstantSheaf_lowerStar_constantZModModule ℓ (pullback.snd i ι)
      exact @IsFiniteLocallyConstantSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
        (((ι)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)].mapIso e₁ ≪≫ e₂).symm) this
  · have := Functor.isGE_rightDerivedFunctor_obj_singleFunctor
      (j)_*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)] (constantZModModule U ℓ)
    exact IsFiniteLocallyConstantSheaf.of_isZero
      (Functor.map_isZero (ι)^*[ModuleCat.{u + 1} (ZModCoeff.{u} ℓ)]
        (DerivedCategory.isZero_of_isGE K 0 n hn))

end AlgebraicGeometry.Etale
