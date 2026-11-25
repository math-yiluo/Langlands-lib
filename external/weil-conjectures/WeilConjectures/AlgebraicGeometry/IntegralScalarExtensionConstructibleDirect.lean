/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.TraceFormula.PointFiberFunctorIntegral

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-!
# Direct integral scalar extension

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/sk-prop-scalar-six-ctf.md, preservation clause
(blueprint: lem-weil-integral-scalar-extension-constructible).
-/

/-- The direct derived extension of scalars `T(K) = S ⊗^L_R K` along the coefficient change
`a_Y : p_Y^* 𝒪̲_E → p_Y^* 𝒪̲_L` induced by the inclusion `𝒪_E ⊆ 𝒪_L`: the left derived functor
of `Mod.extendScalars`, as in `prose-07-03`.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
sk-prop-scalar-six-ctf.md, preservation for listed coefficient maps, the functor `T`
(blueprint: lem-weil-integral-scalar-extension-constructible). -/
noncomputable abbrev integralScalarExtension
    (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (Y : Scheme.{u}) :
    DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)) ⥤
      DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) Y)) :=
  (Mod.extendScalars
    (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) Y)).leftDerivedFunctor

/-- Direct derived extension of scalars along `𝒪_E → 𝒪_L` sends `D_cons(Y_proét, R)` into
`D_cons(Y_proét, S)`; no derived completeness condition is involved.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
sk-prop-scalar-six-ctf.md, lemma-extension-scalars-preserves-dctf: preservation for listed
coefficient maps, specialized to the finite integral extension in
proposition-six-operations-change-coefficients (2) (blueprint:
lem-weil-integral-scalar-extension-constructible).

Proof: `cartesianCoefficients_finiteFree` (`lemma-inverse-image-coefficient-sheaves`),
which assembles the integral basis (`lem-sfb-local-field-integral-basis`) and the finite-free
coordinates of `Res_{a_Y} S`, gives at `Y` that `Ext_{a_Y}` preserves finite limits. Then
`boundedConstructible_leftDerivedExtendScalars_obj`
(`lem-weil-pbc-bounded-constructible-exact-scalar-extension`) with `X = Y` and `φ = a_Y` applies:
its constructibility is exactly `boundedConstructible` (`definition-constructible-sheaves--4`) and
its derived functor is `T` (`prose-07-03`); no Noetherian hypothesis.
The statement includes empty schemes, zero complexes, identity extensions, shifts, torsion
cohomology, and ramified finite extensions, and imposes no derived completeness condition.
-/
theorem integralScalarExtension_constructible
    (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (Y : Scheme.{u})
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)))
    (hK : boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y) K) :
    boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) Y)
      ((integralScalarExtension ℓ h Y).obj K) := by
  let hflat := (cartesianCoefficients_finiteFree ℓ h).2.2 Y |>.1
  let : PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) Y)) := hflat
  exact boundedConstructible_leftDerivedExtendScalars_obj _ _ _ K hK

/-- Restriction of the direct derived tensor to the bounded constructible full
subcategories. Its object map is well-defined by
`integralScalarExtension_constructible`, and its morphism map is the ambient
full-subcategory map.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
sk-prop-scalar-six-ctf.md, restriction of `T` to the preserved full subcategories
(blueprint: lem-weil-integral-scalar-extension-constructible).
-/
noncomputable def integralScalarExtensionFunctor
    (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (Y : Scheme.{u}) :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)).FullSubcategory ⥤
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) Y)).FullSubcategory :=
  ObjectProperty.lift _
    ((boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)).ι ⋙
      integralScalarExtension ℓ h Y)
    (fun K ↦ integralScalarExtension_constructible ℓ h Y K.obj K.property)


end AlgebraicGeometry.ProEtale
