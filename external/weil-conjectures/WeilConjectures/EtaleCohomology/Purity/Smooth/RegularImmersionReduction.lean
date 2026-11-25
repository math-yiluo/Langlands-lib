/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-!
# Purity for regular closed immersions and finite reduction

Let `i : Z ⟶ X` be a regular closed immersion of pure codimension `c`, with `X` smooth over a
perfect field `k` and `Z` regular, and let `J` be an ideal of the finite coefficient ring `Λ`.
The purity isomorphism `cl_i : Λ_Z ≅ Ri^! (Λ_X(c)[2c])`
(`AlgebraicGeometry.Etale.isIso_fundamentalClassMap`) reduces modulo `J` to a morphism

`cl_i mod J : Λ_Z ⊗ᴸ (Λ/J)_Z ⟶ Ri^! (Λ_X(c)[2c] ⊗ᴸ (Λ/J)_X)`,

the reduction of `cl_i` followed by the canonical comparison
`Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)` and `(Λ/J)_Z ≅ Li^* (Λ/J)_X`. This is the form of the
finite reduction `A_{E,n} ⟶ A_{E,n-1}` of item 4 of blueprint
`prop-pur-regular-immersion-purity-compatibilities` in which the reduction is applied to the
target *before* `Ri^!`.

The reduction map `ρ : K ⟶ K ⊗ᴸ (Λ/J)_X` is natural in `K`, and the adjoint of the reduced
fundamental class is the purity map followed by `Ri^!(ρ)`: the classes reduce compatibly.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekDerivedTensorMap`: the comparison
  `Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)`, adjoint to the inverse of the projection map followed by
  the counit of `Ri_! ⊣ Ri^!`.
- `AlgebraicGeometry.Etale.fundamentalClassMapModIdeal`: the reduced purity map `cl_i mod J`.
- `AlgebraicGeometry.Etale.constantComplexToQuotient`: the map `Λ_X ⟶ (Λ/J)_X` induced by the
  quotient map `Λ ⟶ Λ/J`.
- `AlgebraicGeometry.Etale.reductionModIdealUnit`: the reduction map `K ⟶ K ⊗ᴸ (Λ/J)_X`, natural
  in `K`.

## Main statements

- `AlgebraicGeometry.Etale.supportedClassMap_comp_map_rightDerivedUpperShriek`: the adjoint
  `Λ_Z ⟶ Ri^! L` of a class with supports is natural in the coefficients `L`.
- `AlgebraicGeometry.Etale.supportedClassMap_fundamentalClass_reductionModIdealUnit`: the
  adjoint of the reduced fundamental class is the purity map followed by `Ri^!(ρ)`.
- `AlgebraicGeometry.Etale.reductionModIdealUnit_app_comp_fundamentalClassMapModIdeal`: the
  reduced purity map `cl_i mod J` is compatible with the reduction maps `ρ` and the purity map
  `cl_i` (blueprint `prop-pur-regular-immersion-purity-compatibilities`, item 4).

The unit comparisons of the derived pullback and the right unitality of the projection map used
here are in `WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Comparison

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
  [HasCompactification i]

/-- The canonical comparison `Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)` for `K, M ∈ D(X_ét, Λ)`: the
adjoint, under `Ri_! ⊣ Ri^!`, of the composite

`Ri_! (Ri^! K ⊗ᴸ Li^* M) ≅ Ri_! Ri^! K ⊗ᴸ M ⟶ K ⊗ᴸ M`

of the inverse of the projection map (`AlgebraicGeometry.Etale.projectionMap`, invertible at a
finite coefficient ring by `AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`) and of the
counit of the adjunction. -/
noncomputable def rightDerivedUpperShriekDerivedTensorMap
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj ((R(i)^![Λ]).obj K)).obj
        ((L((i)^*[ModuleCat.{u + 1} Λ])).obj M) ⟶
      (R(i)^![Λ]).obj (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj M) :=
  haveI := isIso_projectionMap_of_finite Λ i
  (rightDerivedUpperShriekAdjunction Λ i).homEquiv _ _
    (inv (((projectionMap (ModuleCat.{u + 1} Λ) i).app
        ((R(i)^![Λ]).obj K)).app M) ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
        ((rightDerivedUpperShriekAdjunction Λ i).counit.app K)).app M)

end Comparison

section Reduction

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) (J : Ideal Λ)

/-- The map `Λ_X ⟶ (Λ/J)_X` of constant complexes induced by the quotient map `Λ ⟶ Λ/J`: the
constant complex `Λ_X` is the unit sheaf, which is the constant sheaf on `Λ`, placed in degree
zero (`AlgebraicGeometry.Etale.singleFunctorObjUnitIso`). -/
noncomputable def constantComplexToQuotient :
    constantComplex Λ X ⟶ constantSingle (ModuleCat.{u + 1} Λ) X (ModuleCat.of Λ (Λ ⧸ J)) :=
  unitToConstantSingle (ModuleCat.{u + 1} Λ) X
    (ModuleCat.ofHom (Ideal.Quotient.mkₐ Λ J).toLinearMap)

/-- The reduction map `ρ_K : K ⟶ K ⊗ᴸ (Λ/J)_X` to the reduction of the coefficients modulo `J`
(`AlgebraicGeometry.Etale.reductionModIdeal`): the inverse of the right unitor
`K ⊗ᴸ Λ_X ≅ K` followed by `K ⊗ᴸ (Λ_X ⟶ (Λ/J)_X)`
(`AlgebraicGeometry.Etale.constantComplexToQuotient`). It is natural in `K`. -/
noncomputable def reductionModIdealUnit : 𝟭 _ ⟶ reductionModIdeal Λ X J :=
  derivedTensorRightUnitorInvComp (ModuleCat.{u + 1} Λ) X (constantComplexToQuotient Λ X J)

lemma reductionModIdealUnit_app
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (reductionModIdealUnit Λ X J).app K =
      (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X K).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map (constantComplexToQuotient Λ X J) :=
  rfl

end Reduction

section SupportedClass

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Z : Scheme.{u}} (i : Z ⟶ X)
  [IsClosedImmersion i]

/-- The adjoint `Λ_Z ⟶ Ri^! L` of a class with supports `γ : Λ_X ⟶ Ri_! Ri^! L`
(`AlgebraicGeometry.Etale.supportedClassMap`) is natural in the coefficients `L`. -/
theorem supportedClassMap_comp_map_rightDerivedUpperShriek
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) (f : L ⟶ L') :
    supportedClassMap Λ i (γ ≫ (R(i)_![ModuleCat.{u + 1} Λ]).map
      ((R(i)^![Λ]).map f)) =
      supportedClassMap Λ i γ ≫ (R(i)^![Λ]).map f := by
  rw [supportedClassMap_eq_supportedTranspose, supportedClassMap_eq_supportedTranspose,
    supportedTranspose_comp]

end SupportedClass

section ReductionComparison

variable (Λ : Type (u + 1)) [CommRing Λ] {X Z : Scheme.{u}} (i : Z ⟶ X) (J : Ideal Λ)

/-- The derived pullback of `Λ_X ⟶ (Λ/J)_X` is, under `Li^* (Λ/J)_X ≅ (Λ/J)_Z` and the unit
comparison `Li^* Λ_X ≅ Λ_Z`, the map `Λ_Z ⟶ (Λ/J)_Z`. -/
lemma leftDerivedUpperStar_map_constantComplexToQuotient :
    (L((i)^*[ModuleCat.{u + 1} Λ])).map (constantComplexToQuotient Λ X J) ≫
        (leftDerivedUpperStarSingleConstantSheafIso _ i (ModuleCat.of Λ (Λ ⧸ J))).hom =
      (leftDerivedUpperStarUnitIso _ i).hom ≫ constantComplexToQuotient Λ Z J :=
  leftDerivedUpperStar_map_unitToConstantSingle _ i
    (ModuleCat.ofHom (Ideal.Quotient.mkₐ Λ J).toLinearMap)

variable [Finite Λ] [HasCompactification i]

/-- The reduction map `ρ : Ri^! K ⟶ Ri^! K ⊗ᴸ (Λ/J)_Z`, followed by
`(Λ/J)_Z ≅ Li^* (Λ/J)_X` and the comparison `Ri^! K ⊗ᴸ Li^* (Λ/J)_X ⟶ Ri^!(K ⊗ᴸ (Λ/J)_X)`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekDerivedTensorMap`), is `Ri^!` of the reduction
map `ρ : K ⟶ K ⊗ᴸ (Λ/J)_X`. -/
lemma reductionModIdealUnit_app_comp_rightDerivedUpperShriekDerivedTensorMap
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (reductionModIdealUnit Λ Z J).app ((R(i)^![Λ]).obj K) ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj _).map
        (leftDerivedUpperStarSingleConstantSheafIso _ i (ModuleCat.of Λ (Λ ⧸ J))).inv ≫
      rightDerivedUpperShriekDerivedTensorMap Λ i _ _ =
    (R(i)^![Λ]).map ((reductionModIdealUnit Λ X J).app K) :=
  have := isIso_projectionMap_of_finite Λ i
  rightDerivedUpperShriek_map_rightUnitor_inv_comp_whiskerLeft Λ i _ _ _
    (leftDerivedUpperStar_map_constantComplexToQuotient Λ i J) K

end ReductionComparison

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {X Z : Scheme.{u}} [HasInvertibleExponent Λ X] {k : Type u}
  [Field k] [PerfectField k] (c : ℕ) (i : Z ⟶ X) [IsRegularImmersion c i]

/-- The purity map reduced modulo an ideal `J` of `Λ`,

`cl_i mod J : Λ_Z ⊗ᴸ (Λ/J)_Z ⟶ Ri^! (Λ_X(c)[2c] ⊗ᴸ (Λ/J)_X)`:

the reduction `cl_i ⊗ᴸ (Λ/J)_Z` of `cl_i`
(`AlgebraicGeometry.Etale.fundamentalClassMap`), followed by `(Λ/J)_Z ≅ Li^* (Λ/J)_X` and the
comparison `Ri^! K ⊗ᴸ Li^* M ⟶ Ri^! (K ⊗ᴸ M)`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekDerivedTensorMap`). -/
noncomputable def fundamentalClassMapModIdeal (aX : X ⟶ Spec (.of k)) [Smooth aX]
    (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (J : Ideal Λ) :
    (reductionModIdeal Λ Z J).obj (constantComplex Λ Z) ⟶
      (R(i)^![Λ]).obj
        ((reductionModIdeal Λ X J).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) :=
  (reductionModIdeal Λ Z J).map (fundamentalClassMap Λ c i aX hZ) ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj _).map
      (leftDerivedUpperStarSingleConstantSheafIso _ i (ModuleCat.of Λ (Λ ⧸ J))).inv ≫
    rightDerivedUpperShriekDerivedTensorMap Λ i _ _

/-- Blueprint `prop-pur-regular-immersion-purity-compatibilities`: Compatibilities of purity for
regular immersions

**Finite reduction** (item 4), on the level of classes. For an ideal `J` of `Λ` (for
`Λ = A_{E,n}` and `J = ϖ^{n-1}` this is the reduction `A_{E,n} ⟶ A_{E,n-1}`), the reduction
`ρ : K ⟶ K ⊗ᴸ (Λ/J)_X` (`AlgebraicGeometry.Etale.reductionModIdealUnit`) carries the fundamental
class `[Z ⊂ X] : Λ_X ⟶ Ri_! Ri^! (Λ_X(c)[2c])` to a class with supports in the reduced
coefficients `Λ_X(c)[2c] ⊗ᴸ (Λ/J)_X`, and the adjoint of this reduced class is the purity map
`cl_i` followed by `Ri^!(ρ)`: the purity map is natural in the coefficients, so the classes
reduce compatibly. -/
theorem supportedClassMap_fundamentalClass_reductionModIdealUnit (aX : X ⟶ Spec (.of k))
    [Smooth aX] (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (J : Ideal Λ) :
    supportedClassMap Λ i (fundamentalClass Λ c i aX hZ ≫
      (R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![Λ]).map
        ((reductionModIdealUnit Λ X J).app ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)))) =
      fundamentalClassMap Λ c i aX hZ ≫ (R(i)^![Λ]).map
        ((reductionModIdealUnit Λ X J).app ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) :=
  supportedClassMap_comp_map_rightDerivedUpperShriek Λ i _ _

/-- Blueprint `prop-pur-regular-immersion-purity-compatibilities`: Compatibilities of purity for
regular immersions

Item 4, finite reduction `A_{E,n} → A_{E,n-1}`: reducing the coefficients modulo `J` commutes
with the purity map `cl_i`. The square
```
  Λ_Z ─────────────cl_i─────────────▶ Ri^! (Λ_X(c)[2c])
   │                                         │
 ρ │                                         │ Ri^!(ρ)
   ▼                                         ▼
  Λ_Z ⊗ᴸ (Λ/J)_Z ──cl_i mod J──▶ Ri^! (Λ_X(c)[2c] ⊗ᴸ (Λ/J)_X)
```
commutes, where `ρ` is the reduction map `K ⟶ K ⊗ᴸ (Λ/J)`
(`AlgebraicGeometry.Etale.reductionModIdealUnit`) and `cl_i mod J` is the reduced purity map
(`AlgebraicGeometry.Etale.fundamentalClassMapModIdeal`); for `Λ = A_{E,n}` and `J = ϖ^{n-1}`
this is the reduction `A_{E,n} ⟶ A_{E,n-1}`. -/
theorem reductionModIdealUnit_app_comp_fundamentalClassMapModIdeal (aX : X ⟶ Spec (.of k))
    [Smooth aX] (hZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) (J : Ideal Λ) :
    (reductionModIdealUnit Λ Z J).app (constantComplex Λ Z) ≫
        fundamentalClassMapModIdeal Λ c i aX hZ J =
      fundamentalClassMap Λ c i aX hZ ≫ (R(i)^![Λ]).map
        ((reductionModIdealUnit Λ X J).app ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) := by
  rw [fundamentalClassMapModIdeal, ← Category.assoc,
    ← (reductionModIdealUnit Λ Z J).naturality, Category.assoc]
  exact congrArg (_ ≫ ·) (reductionModIdealUnit_app_comp_rightDerivedUpperShriekDerivedTensorMap
    Λ i J _)

end Etale

end AlgebraicGeometry
