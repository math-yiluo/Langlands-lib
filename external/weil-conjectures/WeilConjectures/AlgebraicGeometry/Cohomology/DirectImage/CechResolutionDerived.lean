/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Derived.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolutionBase
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AcyclicResolution
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-!
# The Čech resolution computes the derived direct image

Let `f : X ⟶ S` be separated and `U` a finite family of opens covering `X` whose finite
intersections are affine over `S`. For a quasi-coherent `𝒪_X`-module `ℱ`, the derived direct image
`Rf_* ℱ` is the complex `f_* Č(U, ℱ)` in the derived category `D(𝒪_S)`
(`AlgebraicGeometry.Scheme.Modules.derivedPushforwardSingleIsoCechResolution`): the Čech
resolution `ℱ ⟶ Č(U, ℱ)` is a resolution by `f_*`-acyclic modules. This is the derived-category
form of `AlgebraicGeometry.Scheme.Modules.higherDirectImageIsoCechResolutionOfIsAffineHom`.
Its cohomology sheaves are the higher direct images
(`AlgebraicGeometry.Scheme.Modules.homologyDerivedPushforwardSingleIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type u} (U : ι → X.Opens)

instance : PreservesFiniteLimits (pushforward f) :=
  have := (pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
  inferInstance

/-- **The Čech resolution computes the derived direct image.** Let `f : X ⟶ S` be separated, `U`
a finite cover of `X` whose finite intersections are affine over `S`, and `ℱ` a quasi-coherent
`𝒪_X`-module. Then `Rf_* ℱ ≅ f_* Č(U, ℱ)` in `D(𝒪_S)`, where the Čech complex is placed in
degrees `≥ 0`. -/
noncomputable def derivedPushforwardSingleIsoCechResolution [IsSeparated f] [Finite ι]
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineHom ((⨅ l, U (y l)).ι ≫ f))
    (hU' : ⨆ i, U i = ⊤) (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (derivedPushforward f).obj ((DerivedCategory.singleFunctor _ 0).obj ℱ) ≅
      DerivedCategory.Q.obj ((((pushforward f).mapHomologicalComplex _).obj
        (cechResolution U ℱ)).extend ComplexShape.embeddingUpNat) :=
  have := quasiIso_cechResolutionι U ℱ hU'
  (pushforward f).rightDerivedFunctorSingleObjIsoOfResolution (cechResolutionι U ℱ)
      (rightAcyclic_cechResolution_X_of_isAffineHom f U hU ℱ) ≪≫
    DerivedCategory.Q.mapIso ((cechResolution U ℱ).mapExtendIso _ _)

/-- **The cohomology sheaves of the derived direct image** are the higher direct images:
`H^q(Rf_* ℱ) ≅ R^q f_* ℱ`. -/
noncomputable def homologyDerivedPushforwardSingleIso (ℱ : X.Modules) (q : ℕ) :
    (DerivedCategory.homologyFunctor _ q).obj
        ((derivedPushforward f).obj ((DerivedCategory.singleFunctor _ 0).obj ℱ)) ≅
      (higherDirectImage f q).obj ℱ :=
  (pushforward f).homologyRightDerivedFunctorSingleObjIso ℱ q

end AlgebraicGeometry.Scheme.Modules
