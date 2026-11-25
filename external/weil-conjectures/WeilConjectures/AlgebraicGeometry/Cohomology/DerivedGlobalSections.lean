/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.Algebra.Homology.ExtWithAction
public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ResolutionScalarAction

/-!
# Cohomology of derived global sections

For a morphism of schemes `f : X ⟶ S` and an `𝒪_X`-module `ℱ`, the derived global sections
`RΓ(X, ℱ)` are an object of `D(Γ(S, ⊤))`, where `Γ(S, ⊤)` acts through `f^♯`
(`AlgebraicGeometry.Scheme.Modules.derivedGlobalSectionsOver`). We identify its cohomology in
degree `n` with the sheaf cohomology `H^n(X, ℱ) = Ext^n(ℤ, ℱ)` of the underlying abelian sheaf,
as `Γ(S, ⊤)`-modules, where `Γ(S, ⊤)` acts on the `Ext`-group through multiplication by global
functions (`CategoryTheory.Abelian.Ext.WithAction`).

The additive comparison is `AlgebraicGeometry.Scheme.Modules.moduleCohomologyExtResolutionEquiv`
(injective `𝒪_X`-modules are acyclic for `Γ` on abelian sheaves, Stacks 03FD). It is natural in
`ℱ`, and on both sides multiplication by `a ∈ Γ(X, ⊤)` is induced by the endomorphism `a • -`
of `ℱ` (`AlgebraicGeometry.Scheme.Modules.moduleCohomology_map_smulHom`), so it is linear.

We also record that extension of scalars along a flat ring map is exact, so that it induces a
functor on derived categories commuting with cohomology.
-/

@[expose] public section

universe w wA u

open CategoryTheory Limits TopologicalSpace Opposite

/-- Extension of scalars preserves finite colimits, as a left adjoint. -/
instance ModuleCat.preservesFiniteColimits_extendScalars {R S : Type u} [CommRing R]
    [CommRing S] (φ : R →+* S) : PreservesFiniteColimits (extendScalars.{u, u, u} φ) :=
  have := (extendRestrictScalarsAdj.{u, u, u} φ).leftAdjoint_preservesColimits
  inferInstance

namespace AlgebraicGeometry

/-- Extension of scalars along the map on global functions of a flat morphism of affine
schemes is exact. -/
instance {T S : Scheme.{u}} [IsAffine S] [IsAffine T] (g : T ⟶ S) [Flat g] :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} g.appTop.hom) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat g.flat_appTop

namespace Scheme.Modules

open CategoryTheory.Abelian.Ext

variable {X : Scheme.{u}}

/-- Multiplication by global functions on the underlying abelian sheaf of a sheaf of modules, as
a ring homomorphism to its endomorphisms. -/
noncomputable def smulRingHom (M : X.Modules) :
    Γ(X, ⊤) →+* End ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) where
  toFun a := End.of ((SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom a))
  map_one' := by
    apply End.ext
    rw [smulHom_one, CategoryTheory.Functor.map_id, End.one_asHom]
  map_mul' a b := by
    apply End.ext
    rw [smulHom_mul, CategoryTheory.Functor.map_comp, End.mul_asHom]
  map_zero' := by
    apply End.ext
    rw [smulHom_zero, CategoryTheory.Functor.map_zero, End.zero_asHom]
  map_add' a b := by
    apply End.ext
    rw [smulHom_add, CategoryTheory.Functor.map_add, End.add_asHom]

variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
  [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

/-- The derived global sections `RΓ(X, ℱ)` of an `𝒪_X`-module `ℱ`, as an object of `D(A)` for
`A = Γ(S, ⊤)` acting through `f^♯`. -/
noncomputable abbrev derivedGlobalSectionsOver {S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) :
    DerivedCategory (ModuleCat.{u} Γ(S, ⊤)) :=
  (schemeGlobalScalarRestriction f).obj
    ((schemeDerivedGlobalSections X).obj ((DerivedCategory.singleFunctor _ 0).obj ℱ))

/-- The cohomology of `RΓ(X, ℱ)` in degree `n` is `H^n(X, ℱ)`, as `Γ(X, ⊤)`-modules. -/
noncomputable def homologyDerivedGlobalSectionsLinearEquiv (ℱ : X.Modules) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) n).obj
        ((schemeDerivedGlobalSections X).obj ((DerivedCategory.singleFunctor _ 0).obj ℱ))
          ≃ₗ[Γ(X, ⊤)]
      WithAction (smulRingHom ℱ) ((constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) n :=
  have : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let e₁ : _ ≃ₗ[Γ(X, ⊤)] (RingedSpace.moduleCohomology X.toRingedSpace n).obj ℱ :=
    ((RingedSpace.globalSectionsFunctor
      X.toRingedSpace).homologyRightDerivedFunctorObjSingleFunctorIso ℱ n).toLinearEquiv
  let e₂ := moduleCohomologyExtResolutionEquiv X ℱ n
  let e₃ : (RingedSpace.moduleCohomology X.toRingedSpace n).obj ℱ ≃ₗ[Γ(X, ⊤)]
      WithAction (smulRingHom ℱ) ((constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) n :=
    { e₂ with
      map_smul' := fun a x ↦ by
        change e₂ (a • x) = (mk₀ ((smulRingHom ℱ) a).asHom).postcomp _ (add_zero n) (e₂ x)
        rw [← moduleCohomology_map_smulHom ℱ (injectiveResolution ℱ) n a x,
          moduleCohomologyExtResolutionEquiv_naturality]
        rfl }
  e₁.trans e₃

/-- The cohomology of `RΓ(X, ℱ) ∈ D(Γ(S, ⊤))` in degree `n` is `H^n(X, ℱ)`, as
`Γ(S, ⊤)`-modules, `Γ(S, ⊤)` acting on both sides through `f^♯`. -/
noncomputable def homologyDerivedGlobalSectionsOverLinearEquiv {S : Scheme.{u}} (f : X ⟶ S)
    (ℱ : X.Modules) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(S, ⊤)) n).obj
        (derivedGlobalSectionsOver f ℱ) ≃ₗ[Γ(S, ⊤)]
      WithAction ((smulRingHom ℱ).comp f.appTop.hom) ((constantSheaf
        (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) n :=
  let e₀ := (((ModuleCat.restrictScalars.{u} f.appTop.hom).mapDerivedCategoryHomologyFunctorIso
    n).app ((schemeDerivedGlobalSections X).obj ((DerivedCategory.singleFunctor _ 0).obj ℱ))).symm
  let e := homologyDerivedGlobalSectionsLinearEquiv ℱ n
  e₀.toLinearEquiv.trans
    { e with map_smul' := fun a x ↦ e.map_smul (f.appTop a) x }

end Scheme.Modules

end AlgebraicGeometry
