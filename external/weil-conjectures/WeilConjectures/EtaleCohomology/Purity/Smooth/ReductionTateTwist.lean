/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionTateShiftData
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TensorInverseZPowMap
public import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence
public import WeilConjectures.TateTwist.EtaleTateSheafPow
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFlat

/-!
# The Tate twists under the reduction of coefficients

Let `ρ : Λ →+* Λ'` be a surjective morphism of commutative rings of positive characteristics
`n` and `n'` with principal kernel, for instance the reduction `A_{E,N+1} → A_{E,N}`, and
`Ψ = - ⊗ᴸ_Λ Λ'` the derived extension of scalars. On a scheme `X` on which `n` is invertible:

* `Λ' ⊗_Λ (μₙ ⊗ Λ) ≅ μₙ ⊗ Λ'` by transitivity of the extension of scalars
  (`AlgebraicGeometry.Etale.extendScalarsCompSheafExtendScalarsIso`), and the power map
  `μₙ ⟶ μ_{n'}`, `u ↦ u^{n/n'}`, induces `μₙ ⊗ Λ' ≅ μ_{n'} ⊗ Λ'`
  (`AlgebraicGeometry.Etale.extendScalarsRootsOfUnityIsoTateTwistSheaf`); hence
  `Λ' ⊗_Λ Λ_X(1) ≅ Λ'_X(1)` on the Tate sheaves
  (`AlgebraicGeometry.Etale.sheafExtendScalarsTateSheafIso`);
* the extension of scalars being monoidal, `Λ' ⊗_Λ Λ_X(m) ≅ Λ'_X(m)` for all `m ∈ ℤ`
  (`AlgebraicGeometry.Etale.sheafExtendScalarsTateTwistSheafIso`);
* the Tate twists being flat sheaves placed in degree zero, `Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]`
  (`AlgebraicGeometry.Etale.derivedExtendScalarsTateShiftIso`).

Pulled back from the universal base `Spec ℤ[1/n]`, these identifications form the Tate shift
datum of `Ψ` (`AlgebraicGeometry.Etale.reductionTateShiftData`, blueprint
`proposition-compatibility-purity-change-coefficients`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance instEssentiallySmallEtale_reductionTateTwist
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- Sheaves of modules on the small étale site have countable coproducts. Instance search times
out on this. -/
local instance instHasCountableCoproductsSheaf_reductionTateTwist
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    HasCountableCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ⟨fun _ _ ↦ (inferInstance : HasColimitsOfSize.{0, 0} (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))).has_colimits_of_shape _⟩

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

section Sheaf

variable (X : Scheme.{u})

/-- **Transitivity of the extension of scalars**, `Λ' ⊗_Λ (Λ ⊗_ℤ F) ≅ Λ' ⊗_ℤ F` for étale
sheaves of abelian groups `F`: both functors are left adjoint to the forgetful functor from
sheaves of `Λ'`-modules. -/
noncomputable def extendScalarsCompSheafExtendScalarsIso :
    extendScalars Λ X ⋙ Sheaf.extendScalars X.smallEtaleTopology ρ ≅ extendScalars Λ' X :=
  ((extendScalarsAdjunction Λ X).comp (Sheaf.extendScalarsAdjunction _ ρ)).leftAdjointUniq
    ((extendScalarsAdjunction Λ' X).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)))

variable [NeZero (ringChar Λ')] [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X]

/-- The extension of scalars of the Tate sheaf: `Λ' ⊗_Λ (μₙ ⊗ Λ) ≅ μₙ ⊗ Λ' ≅ μ_{n'} ⊗ Λ'`, the
second identification induced by the power map `μₙ ⟶ μ_{n'}`, `u ↦ u^{n/n'}`
(`AlgebraicGeometry.Etale.extendScalarsRootsOfUnityIsoTateTwistSheaf`). -/
noncomputable def sheafExtendScalarsTateSheafIso :
    (Sheaf.extendScalars X.smallEtaleTopology ρ).obj (tateSheaf Λ X) ≅ tateSheaf Λ' X :=
  (extendScalarsCompSheafExtendScalarsIso ρ X).app _ ≪≫
    extendScalarsRootsOfUnityIsoTateTwistSheaf Λ' (ringChar Λ)
      (by rw [← map_natCast ρ, ringChar.Nat.cast_ringChar, map_zero])
      (isUnit_ringChar_of_hasInvertibleExponent X) ≪≫
    tateTwistSheafOneIso X Λ'

variable [NeZero (ringChar Λ)]

/-- The extension of scalars of the pulled back Tate sheaf of `Spec ℤ[1/n]` is the pulled back
Tate sheaf of `Spec ℤ[1/n']`. -/
noncomputable def sheafExtendScalarsUpperStarTateSheafIso :
    ((toInvertibleExponentBase (Λ := Λ) X)^*[ModuleCat.{u + 1} Λ] ⋙
        Sheaf.extendScalars X.smallEtaleTopology ρ).obj
        (tateSheaf Λ (invertibleExponentBase.{u} Λ)) ≅
      (toInvertibleExponentBase (Λ := Λ') X)^*[ModuleCat.{u + 1} Λ'].obj
        (tateSheaf Λ' (invertibleExponentBase.{u} Λ')) :=
  (Sheaf.extendScalars X.smallEtaleTopology ρ).mapIso (upperStarTateSheafIso Λ X) ≪≫
    sheafExtendScalarsTateSheafIso ρ X ≪≫ (upperStarTateSheafIso Λ' X).symm

/-- **The extension of scalars of the Tate twists**, `Λ' ⊗_Λ Λ_X(m) ≅ Λ'_X(m)` for the sheaves
`(μₙ ⊗ Λ)^{⊗ m}` (`AlgebraicGeometry.Etale.tateTwistSheaf`), `m ∈ ℤ`: the extension of scalars
and the pullbacks are monoidal, and `Λ' ⊗_Λ Λ_X(1) ≅ Λ'_X(1)`
(`AlgebraicGeometry.Etale.sheafExtendScalarsTateSheafIso`). -/
noncomputable def sheafExtendScalarsTateTwistSheafIso (m : ℤ) :
    (Sheaf.extendScalars X.smallEtaleTopology ρ).obj (tateTwistSheaf Λ X m) ≅
      tateTwistSheaf Λ' X m :=
  let e' := (tateSheafTensorInverse Λ').map
    (toInvertibleExponentBase (Λ := Λ') X)^*[ModuleCat.{u + 1} Λ']
  (tateSheafTensorInverse Λ).zpowMapIso e' _ (sheafExtendScalarsUpperStarTateSheafIso ρ X) m ≪≫
    ((tateSheafTensorInverse Λ').zpowMapIso e' _ (Iso.refl _) m).symm

end Sheaf

section Derived

variable {ρ} (hρ : Function.Surjective ρ) {a : Λ} (ha : RingHom.ker ρ = Ideal.span {a})
  (X : Scheme.{u})

/-- The derived extension of scalars commutes with the shifts, as the left adjoint of the
derived restriction of scalars. -/
@[instance_reducible]
noncomputable def derivedExtendScalarsCommShift : (derivedExtendScalars hρ ha X).CommShift ℤ :=
  (derivedExtendScalarsAdjunction hρ ha X).leftAdjointCommShift ℤ

variable [NeZero (ringChar Λ)] [NeZero (ringChar Λ')] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ' X]

/-- **The derived extension of scalars of the Tate twists**, `Ψ Λ_X(m) ≅ Λ'_X(m)`: the twist
`Λ_X(m)` is the flat sheaf `(μₙ ⊗ Λ)^{⊗ m}` placed in degree zero, on which `Ψ` is computed by the
extension of scalars of sheaves (`CategoryTheory.Functor.leftDerivedFunctorSingleFunctorIsoOfFlat`),
and `Λ' ⊗_Λ (μₙ ⊗ Λ)^{⊗ m} ≅ (μ_{n'} ⊗ Λ')^{⊗ m}`
(`AlgebraicGeometry.Etale.sheafExtendScalarsTateTwistSheafIso`). -/
noncomputable def derivedExtendScalarsTateObjectIso (m : ℤ) :
    (derivedExtendScalars hρ ha X).obj (tateObject Λ X m) ≅ tateObject Λ' X m :=
  haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
  (derivedExtendScalars hρ ha X).mapIso (tateTwistObjectIsoSingleFunctor Λ X m) ≪≫
    Functor.leftDerivedFunctorSingleFunctorIsoOfFlat _ (flat_tateTwistSheaf Λ X m) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (sheafExtendScalarsTateTwistSheafIso ρ X m) ≪≫
    (tateTwistObjectIsoSingleFunctor Λ' X m).symm

/-- The derived extension of scalars of the shifted Tate twists,
`Ψ(Λ_X(m)[2m]) ≅ (Ψ Λ_X(m))[2m] ≅ Λ'_X(m)[2m]`. -/
noncomputable def derivedExtendScalarsTateShiftIso (m : ℤ) :
    (derivedExtendScalars hρ ha X).obj ((tateObject Λ X m)⟦2 * m⟧) ≅
      (tateObject Λ' X m)⟦2 * m⟧ :=
  letI := derivedExtendScalarsCommShift hρ ha X
  ((derivedExtendScalars hρ ha X).commShiftIso (2 * m)).app _ ≪≫
    (shiftFunctor _ (2 * m)).mapIso (derivedExtendScalarsTateObjectIso hρ ha X m)

/-- Blueprint `proposition-compatibility-purity-change-coefficients`

**The Tate shift datum of the reduction of coefficients.** For a surjective morphism
`ρ : Λ →+* Λ'` of rings of positive characteristics with principal kernel (for instance
`A_{E,N+1} → A_{E,N}`), the identifications `Ψ(Λ_S(m)[2m]) ≅ Λ'_S(m)[2m]` on
`S = Spec ℤ[1/n]` induced by `μₙ ⊗ Λ' ≅ μ_{n'} ⊗ Λ'`
(`AlgebraicGeometry.Etale.derivedExtendScalarsTateShiftIso`), pulled back along the morphisms
`X ⟶ S`, form a Tate shift datum of the derived extension of scalars `Ψ`. -/
noncomputable def reductionTateShiftData :
    DerivedExtendScalarsTateShiftData Λ Λ' hρ ha :=
  haveI := HasInvertibleExponent.of_ringHom ρ (invertibleExponentBase.{u} Λ)
  DerivedExtendScalarsTateShiftData.ofBase hρ ha
    (derivedExtendScalarsTateShiftIso hρ ha (invertibleExponentBase.{u} Λ))

end Derived

end Etale

end AlgebraicGeometry
