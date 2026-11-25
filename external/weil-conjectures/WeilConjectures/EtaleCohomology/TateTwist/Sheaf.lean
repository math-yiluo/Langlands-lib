/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponentBase
public import WeilConjectures.AlgebraicGeometry.PrimitiveRootsCover
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnityConstant
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ExtendScalars
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse

/-!
# The Tate sheaf `Λ(1) = μₙ ⊗ Λ`

Let `Λ` be a commutative ring of characteristic `n`. The *Tate sheaf* of `Λ` on a scheme `X` is
the étale sheaf of `Λ`-modules `Λ_X(1) = μₙ ⊗_ℤ Λ` (`AlgebraicGeometry.Etale.tateSheaf`), where
`μₙ = ker(n : 𝔾ₘ ⟶ 𝔾ₘ)` is the sheaf of `n`-th roots of unity. When `ℓ^N` is the exponent of `Λ`
this is `μ_{ℓ^N} ⊗_{ℤ/ℓ^N} Λ`, the finite-level twist of the blueprint.

The pullback of `μₙ` maps to `μₙ`
(`AlgebraicGeometry.Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf`), isomorphically along
étale morphisms, and accordingly for the Tate sheaf. Over a scheme with a global `n`-th root of
unity `ζ` whose powers have invertible differences, `μₙ ≅ ℤ/n` through `ζ`, so the Tate sheaf is
the constant sheaf `Λ`. On the universal base `Spec ℤ[1/n]` on which the exponent of `Λ` is
invertible, adjoining such a root of unity is an étale cover
(`AlgebraicGeometry.primitiveRootsCover`), so the Tate sheaf there is étale-locally trivial, and
it is invertible: its dual is a tensor inverse
(`AlgebraicGeometry.Etale.tateSheafTensorInverse`).

## Main definitions

- `AlgebraicGeometry.Etale.tateSheaf`: the Tate sheaf `μₙ ⊗ Λ`.
- `AlgebraicGeometry.Etale.upperStarTateSheafToTateSheaf`: the comparison `g^* Λ_Y(1) ⟶ Λ_X(1)`.
- `AlgebraicGeometry.Etale.tateSheafTensorInverse`: a tensor inverse of the Tate sheaf on the
  universal base.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}} (n : ℕ)

/-- The comparison `g^* μₙ ⟶ μₙ` for `g : X ⟶ Y`, induced on kernels of the `n`-th power maps by
the comparison `g^* 𝔾ₘ ⟶ 𝔾ₘ` (`AlgebraicGeometry.Scheme.upperStarGmSheafToGmSheaf`). -/
noncomputable def upperStarRootsOfUnitySheafToRootsOfUnitySheaf (g : X ⟶ Y) :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).obj (Y.rootsOfUnitySheaf n) ⟶
      X.rootsOfUnitySheaf n :=
  kernel.lift _ ((Etale.upperStar _ g).map (kernel.ι _) ≫ upperStarGmSheafToGmSheaf g) (by
    have h : upperStarGmSheafToGmSheaf g ≫ (n • 𝟙 X.gmSheaf) =
        (n • 𝟙 _) ≫ upperStarGmSheafToGmSheaf g := by
      rw [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]
    rw [Category.assoc, h, ← Category.assoc, ← CategoryTheory.Functor.map_id,
      ← Functor.map_nsmul, ← Functor.map_comp, kernel.condition, Functor.map_zero, zero_comp])

@[reassoc (attr := simp)]
lemma upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι (g : X ⟶ Y) :
    upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g ≫ kernel.ι _ =
      (Etale.upperStar _ g).map (kernel.ι _) ≫ upperStarGmSheafToGmSheaf g :=
  kernel.lift_ι _ _ _

/-- For an étale morphism `g`, the comparison `g^* μₙ ⟶ μₙ` is an isomorphism: `g^*` is exact
and the comparison `g^* 𝔾ₘ ⟶ 𝔾ₘ` is an isomorphism. -/
theorem isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf (g : X ⟶ Y) [Etale g] :
    IsIso (upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g) := by
  have := isIso_upperStarGmSheafToGmSheaf g
  let G := Etale.upperStar AddCommGrpCat.{u + 1} g
  let c := asIso (upperStarGmSheafToGmSheaf g)
  have hw : G.map (n • 𝟙 Y.gmSheaf) ≫ c.hom = c.hom ≫ (n • 𝟙 X.gmSheaf) := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.nsmul_comp,
      Preadditive.comp_nsmul, Category.comp_id, Category.id_comp]
  let e : G.obj (Y.rootsOfUnitySheaf n) ≅ X.rootsOfUnitySheaf n :=
    PreservesKernel.iso G (n • 𝟙 Y.gmSheaf) ≪≫ kernel.mapIso _ _ c c hw
  have : upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g = e.hom := by
    refine equalizer.hom_ext ?_
    simp [e, G, c]
  rw [this]
  infer_instance

end Scheme

namespace Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) {Y : Scheme.{u}}

/-- Blueprint `definition-tate-twists`: Coefficient Tate twists.

The *Tate sheaf* `Λ_X(1) = μₙ ⊗_ℤ Λ` on `X`, for `n` the characteristic of `Λ`: the extension of
scalars to `Λ` of the étale sheaf `μₙ` of `n`-th roots of unity. When `ℓ^N` is the exponent of
`Λ`, this is the finite-level twist `μ_{ℓ^N} ⊗_{ℤ/ℓ^N} Λ`. -/
noncomputable def tateSheaf : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ))

variable {X}

/-- The comparison `g^* Λ_Y(1) ⟶ Λ_X(1)` of Tate sheaves for `g : X ⟶ Y`, induced by the
comparison `g^* μₙ ⟶ μₙ`. -/
noncomputable def upperStarTateSheafToTateSheaf (g : X ⟶ Y) :
    (g)^*[ModuleCat.{u + 1} Λ].obj (tateSheaf Λ Y) ⟶ tateSheaf Λ X :=
  (upperStarExtendScalarsIso Λ g).hom.app _ ≫
    (extendScalars Λ X).map (upperStarRootsOfUnitySheafToRootsOfUnitySheaf _ g)

instance isIso_upperStarTateSheafToTateSheaf (g : X ⟶ Y) [Etale g] :
    IsIso (upperStarTateSheafToTateSheaf Λ g) := by
  have := isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) g
  dsimp only [upperStarTateSheafToTateSheaf]
  infer_instance

variable {Λ} (X)

/-- Over a scheme with a global `n`-th root of unity `ζ` whose powers have invertible
differences, `n ≠ 0` being the characteristic of `Λ`, the Tate sheaf is the constant sheaf `Λ`:
`μₙ ≅ ℤ/n` through `ζ`, and `ℤ/n ⊗ Λ = Λ`. -/
noncomputable def tateSheafIsoConstantSheaf [NeZero (ringChar Λ)] (ζ : Γ(X, ⊤)ˣ)
    (hζ : ζ ^ ringChar Λ = 1)
    (hζ' : ∀ i < ringChar Λ, ∀ j < ringChar Λ, i ≠ j →
      IsUnit ((ζ : Γ(X, ⊤)) ^ i - (ζ : Γ(X, ⊤)) ^ j)) :
    tateSheaf Λ X ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) :=
  haveI := X.isIso_constantZModToRootsOfUnitySheaf_of_isUnit_sub (ringChar Λ) ζ hζ hζ'
  (extendScalars Λ X).mapIso
      (asIso (X.constantZModToRootsOfUnitySheaf (ringChar Λ) ζ hζ)).symm ≪≫
    extendScalarsConstantZModIso X (ringChar.Nat.cast_ringChar)

end Etale

end AlgebraicGeometry
