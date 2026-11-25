/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction
public import WeilConjectures.CategoryTheory.Sites.SheafComposeBraided
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationCoefficientsTensor
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionSupports
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.RestrictScalarsBraided

/-!
# The monoidal structure of the reduction of coefficients

Let `ρ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel and
`Ψ = - ⊗ᴸ_Λ Λ'` the derived extension of scalars of étale sheaves
(`AlgebraicGeometry.Etale.derivedExtendScalars`), the left derived functor of the strong monoidal
extension of scalars `Sheaf.extendScalars`. Its canonical monoidal structure
(`CategoryTheory.Functor.leftDerivedFunctorMonoidal`, whose comonoidal structure is the tensor
comparison) gives the comparison `Ψ(M ⊗ᴸ N) ≅ Ψ M ⊗ᴸ Ψ N`
(`AlgebraicGeometry.Etale.derivedExtendScalarsDerivedTensorIso`), natural in both variables and
compatible with the left unitors through the counit `Ψ Λ_X ≅ Λ'_X`
(`AlgebraicGeometry.Etale.derivedExtendScalarsConstantComplexEtaIso`). These are the first fields
of `AlgebraicGeometry.Etale.MonoidalSupportedCoefficientChange` for
`AlgebraicGeometry.Etale.reductionSupportedCoefficientChange` (blueprint
`proposition-compatibility-purity-change-coefficients`).

The extension of scalars of sheaves is compatible with the braidings
(`AlgebraicGeometry.Etale.sheafExtendScalars_map_braiding_hom_δ`), hence so is `Ψ`
(`AlgebraicGeometry.Etale.derivedExtendScalars_map_braiding_hom_δ`), for the Koszul braidings
`DerivedCategory.braidedCategory'`.

## Main definitions

- `AlgebraicGeometry.Etale.derivedExtendScalarsMonoidal`: the monoidal structure of `Ψ`.
- `AlgebraicGeometry.Etale.derivedExtendScalarsDerivedTensorIso`: `Ψ(M ⊗ᴸ N) ≅ Ψ M ⊗ᴸ Ψ N`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

-- The braiding of `ModuleCat` through its symmetric structure and the braiding
-- `Etale.sheafBraidedCategory` of étale sheaves, as in the definition of the derived tensor
-- product of étale sheaves (`AlgebraicGeometry.Etale.derivedTensor`).
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

/-- Extension of scalars of étale sheaves of modules is compatible with the braidings:
`(Λ' ⊗_Λ -) β_{F, G} ≫ δ_{G, F} = δ_{F, G} ≫ β_{Λ' ⊗_Λ F, Λ' ⊗_Λ G}`. Its comonoidal structure is
obtained by doctrinal adjunction from the lax monoidal structure of restriction of scalars,
which is lax braided. -/
lemma sheafExtendScalars_map_braiding_hom_δ (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.extendScalars X.smallEtaleTopology ρ).map (β_ F G).hom ≫
        δ (Sheaf.extendScalars X.smallEtaleTopology ρ) G F =
      δ (Sheaf.extendScalars X.smallEtaleTopology ρ) F G ≫ (β_ _ _).hom :=
  ((Sheaf.extendScalarsAdjunction _ ρ).leftAdjointOplaxMonoidal_δ_braiding F G).symm

/-- The monoidal structure of the derived extension of scalars `Ψ = - ⊗ᴸ_Λ Λ'`: the monoidal
structure `CategoryTheory.Functor.leftDerivedFunctorMonoidal` of the left derived functor of the
strong monoidal extension of scalars of étale sheaves. -/
noncomputable abbrev derivedExtendScalarsMonoidal (X : Scheme.{u}) :
    (derivedExtendScalars hρ ha X).Monoidal :=
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorMonoidal

/-- The counit `Ψ Λ_X ≅ Λ'_X` is the unit comparison `η` of the monoidal structure
`derivedExtendScalarsMonoidal`. -/
lemma derivedExtendScalarsConstantComplexEtaIso_hom (X : Scheme.{u}) :
    (derivedExtendScalarsConstantComplexEtaIso hρ ha X).hom =
      letI := derivedExtendScalarsMonoidal hρ ha X
      η (derivedExtendScalars hρ ha X) :=
  rfl

/-- The derived extension of scalars of a derived tensor product, `Ψ(M ⊗ᴸ N) ≅ Ψ M ⊗ᴸ Ψ N`: the
comonoidal structure of `derivedExtendScalarsMonoidal`, that is, the tensor comparison of the
left derived functor of the extension of scalars. -/
noncomputable def derivedExtendScalarsDerivedTensorIso (X : Scheme.{u}) (M N : 𝐃(X, Λ)) :
    (derivedExtendScalars hρ ha X).obj (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).obj N) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ') X).obj ((derivedExtendScalars hρ ha X).obj M)).obj
        ((derivedExtendScalars hρ ha X).obj N) :=
  letI := derivedExtendScalarsMonoidal hρ ha X
  (Functor.Monoidal.μIso _ M N).symm

lemma derivedExtendScalarsDerivedTensorIso_hom (X : Scheme.{u}) (M N : 𝐃(X, Λ)) :
    (derivedExtendScalarsDerivedTensorIso hρ ha X M N).hom =
      letI := derivedExtendScalarsMonoidal hρ ha X
      δ (derivedExtendScalars hρ ha X) M N :=
  rfl

/-- `Ψ(M ⊗ᴸ N) ≅ Ψ M ⊗ᴸ Ψ N` is natural in `M`. -/
@[reassoc]
lemma derivedExtendScalarsDerivedTensorIso_hom_naturality_left (X : Scheme.{u})
    {M M' : 𝐃(X, Λ)} (φ : M ⟶ M') (N : 𝐃(X, Λ)) :
    (derivedExtendScalars hρ ha X).map (((derivedTensor (ModuleCat.{u + 1} Λ) X).map φ).app N) ≫
        (derivedExtendScalarsDerivedTensorIso hρ ha X M' N).hom =
      (derivedExtendScalarsDerivedTensorIso hρ ha X M N).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') X).map
          ((derivedExtendScalars hρ ha X).map φ)).app _ := by
  let := derivedExtendScalarsMonoidal hρ ha X
  exact (δ_natural_left (derivedExtendScalars hρ ha X) φ N).symm

/-- `Ψ(M ⊗ᴸ N) ≅ Ψ M ⊗ᴸ Ψ N` is natural in `N`. -/
@[reassoc]
lemma derivedExtendScalarsDerivedTensorIso_hom_naturality_right (X : Scheme.{u})
    (M : 𝐃(X, Λ)) {N N' : 𝐃(X, Λ)} (ψ : N ⟶ N') :
    (derivedExtendScalars hρ ha X).map (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).map ψ) ≫
        (derivedExtendScalarsDerivedTensorIso hρ ha X M N').hom =
      (derivedExtendScalarsDerivedTensorIso hρ ha X M N).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') X).obj _).map
          ((derivedExtendScalars hρ ha X).map ψ) := by
  let := derivedExtendScalarsMonoidal hρ ha X
  exact (δ_natural_right (derivedExtendScalars hρ ha X) M ψ).symm

/-- `Ψ(M ⊗ᴸ N) ≅ Ψ M ⊗ᴸ Ψ N` is compatible with the left unitors, through the counit
`Ψ Λ_X ≅ Λ'_X` (`derivedExtendScalarsConstantComplexEtaIso`). -/
lemma derivedExtendScalars_map_derivedTensorLeftUnitor_hom (X : Scheme.{u}) (M : 𝐃(X, Λ)) :
    (derivedExtendScalars hρ ha X).map (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) X M).hom =
      (derivedExtendScalarsDerivedTensorIso hρ ha X (constantComplex Λ X) M).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ') X).map
          (derivedExtendScalarsConstantComplexEtaIso hρ ha X).hom).app _ ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ') X _).hom := by
  let := derivedExtendScalarsMonoidal hρ ha X
  exact (Functor.OplaxMonoidal.left_unitality_hom _ M).symm

section Braided

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- **The derived extension of scalars is compatible with the braidings**: for the Koszul
braidings `DerivedCategory.braidedCategory'`,
`Ψ β_{M, N} ≫ δ_{N, M} = δ_{M, N} ≫ β_{Ψ M, Ψ N}`, where `δ` is the comonoidal structure of
`CategoryTheory.Functor.leftDerivedFunctorMonoidal`. -/
lemma derivedExtendScalars_map_braiding_hom_δ (X : Scheme.{u}) (M N : 𝐃(X, Λ)) :
    have := preservesKFlatQuasiIso_extendScalars hρ ha X
    letI : (derivedExtendScalars hρ ha X).Monoidal :=
      (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorMonoidal
    (derivedExtendScalars hρ ha X).map (β_ M N).hom ≫ δ (derivedExtendScalars hρ ha X) N M =
      δ (derivedExtendScalars hρ ha X) M N ≫ (β_ _ _).hom :=
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor_map_braiding_hom_δ
    (sheafExtendScalars_map_braiding_hom_δ X) M N

end Braided

end Etale

end AlgebraicGeometry
