/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedLfpCoefficientModel
import WeilConjectures.AlgebraicGeometry.CondensedStratumModelAssembly
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage

/-!
# Descent of a constructible condensed module to finite coefficients

Source: upstream master, SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean,
module docstring, (Obj) descent paragraph
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- A constructible module over the finite-subextension-valued condensed algebraic closure
has a constructible model over one finite coefficient field.
Source: upstream master, SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean,
module docstring, (Obj) descent paragraph
(auxiliary; not a blueprint node).

Proof:
1. For a locally finitely presented sheaf on a topologically noetherian scheme, take a
finite affine pro-etale presentation cover. The base is qcqs, and the covering objects
and their pairwise and triple fibre products are qcqs. The coefficient ring is the
filtered colimit of the finite coefficient rings: first on profinite sets and then by
preservation of colimits under inverse image. The qcqs section calculus descends the
finitely many matrix entries to a common finite field.
2. Form the cokernels of these lifted matrices. Tensor preserves cokernels. The Hom
part of qcqs finitely presented section calculus and tensor adjunction descend the
transition isomorphisms and their inverses on the overlaps. Enlarge the field until
the inverse, diagonal and cocycle identities hold, by eventual equality in the Hom colimit.
3. Ringed-site module-sheaf gluing gives the finite coefficient model. Weakly-etale
localization identifies the slice restrictions with the covering schemes. The ringed-topoi
tensor pullback comparison makes the local scalar-extension isomorphisms compatible.
Sheaf-Hom covering gluing glues these maps and their inverses; uniqueness proves the
global maps inverse. The same cover witnesses local finite presentation of the model.
4. Apply noetherian induction on closed supports. The empty support has the zero model.
Pull stratifications back by fibre products. On a nonempty support choose a nonempty
open contained in one stratum image, using the finite irreducible components. Its base
change to that stratum is a surjective closed immersion, not necessarily a factorization
through the stratum. Empty-complement ringed open-closed localization, also on slices,
gives the coefficient-compatible equivalence reflecting local finite presentation.
The preceding steps descend the open part. Choose a closed subscheme with complementary
support and apply induction to it. Enlarge the two fields to their finite compositum.
5. The ringed open-closed exact sequence expresses the sheaf as an extension of the
closed direct image by the open extension by zero of these models. Both outer models
are constructible on the combined stratification. Tensor adjunction and the open
extension-by-zero adjunction identify scalar extension with open extension by zero.
Finite free tensor commutes with the closed direct image, and its filtered-colimit
compatibility gives the algebraic-closure comparison.
6. Regard the degree-one extension class as a derived map by extension classification.
Flat coefficient derived adjunction identifies its target with the filtered colimit of
finite extensions of the open model, all in degree zero. Constructible sheaf
Ext-continuity in degree one descends this class to one larger finite field.
7. Realize the descended class by a short exact sequence. Serre closure makes its
middle term constructible. Exact scalar extension preserves its class; injectivity
of extension classification identifies its middle term with the original sheaf.

The nodes supplying these steps are respectively qcqs-fp-section-calculus and
profinite-point-pullback; site-module-sheaf-gluing, weakly-etale-localization,
ringed-topoi-module-pullback-tensor and sheaf-hom-cover-gluing; finite irreducible
components, closed-subset-closed-subscheme and proetale-ringed-open-closed;
condensed-flat-coefficient-calculus; ext-one-extension-classification and
condensed-sheaf-ext-continuity; and condensed-constructible-serre. -/
theorem exists_constructible_finiteCoefficient_model
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicAlgClRingObj T ℓ))
    (hM : IsConstructibleModuleObject (padicAlgClRingObj T ℓ) M) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (M_E : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (padicSubfieldRingObj T ℓ E)),
      IsConstructibleModuleObject (padicSubfieldRingObj T ℓ E) M_E ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl T ℓ E)).obj M_E ≅ M) := by
  obtain ⟨S, hS⟩ := hM
  apply exists_finiteCoefficient_model_of_stratum_models T ℓ M S
  intro a
  exact exists_lfp_finiteCoefficient_model_on_immersion T (S.domain a) (S.immersion a) ℓ
    (((upperStar Ab.{u + 1} (S.immersion a)).mapMod (padicAlgClRingObj T ℓ)).obj M) (hS a)

end AlgebraicGeometry.ProEtale
