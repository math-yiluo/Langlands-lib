/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

/-!
# Affine-local pro-etale constructibility with independent coefficient size

Source: Stacks Project, proetale.tex, definition-constructible, Tag 09AJ
(auxiliary; not a blueprint node).

The published coefficient-sized site is equivalent to the original small site. Its
objects and coverings are unchanged. Constant-scalar restriction retains the underlying
additive sheaf and reads intrinsic constant-ring modules as fixed-scalar sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.Scheme

/-- Fixed-scalar inverse image on the existing equivalent pro-etale site models.
This is the usual left Kan extension followed by sheafification along canonical scheme
base change. It reads the constant-ring module inverse image after constant-scalar
restriction, with its canonical constant-coefficient identification.
Source: Stacks Tags 09A5, 00VC and 03D2
(auxiliary; not a blueprint node). -/
def coefficientProEtaleFixedModulePullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Type (max v (u + 1))) [CommRing R] :=
  Functor.sheafPullbackConstruction.sheafPullback
    (coefficientProEtaleModelBaseChange.{u, v} f) (ModuleCat.{max v (u + 1)} R)
    (coefficientProEtaleModelTopology.{u, v} Y) (coefficientProEtaleModelTopology.{u, v} X)

/-- The recorded affine-local constructibility condition, transported to the equivalent
coefficient-sized site. The finite stratification consists of the same immersed schemes.
On every localized site, values are finitely presented modules and may vary with the
covering member. No coefficient-set finiteness or universe equality is imposed.
Source: Stacks Project, Tag 09AJ, definition-constructible; Tag 00IK identifies finite type
and finite presentation over a Noetherian coefficient ring
(auxiliary; not a blueprint node). -/
def IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf (X : Scheme.{u})
    (R : Type (max v (u + 1))) [CommRing R] [IsNoetherianRing R]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X)
        R)) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    ∃ S : Stratification U.toScheme,
      (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
      ∀ (a : Fin S.n) (V : coefficientProEtaleSiteModel.{u, v} (S.domain a)),
        ∃ T : Sieve V, T ∈ coefficientProEtaleModelTopology.{u, v} (S.domain a) V ∧
          ∀ (W : coefficientProEtaleSiteModel.{u, v} (S.domain a)) (f : W ⟶ V), T f →
            ∃ M : ModuleCat.{max v (u + 1)} R, Module.FinitePresentation R M ∧
              Nonempty
                ((((coefficientProEtaleFixedModulePullback.{u, v}
                    (S.immersion a ≫ U.ι) R).obj
                    ((coefficientModelFixedScalars _ R).obj F)).over W) ≅
                  (constantSheaf
                    ((coefficientProEtaleModelTopology.{u, v} (S.domain a)).over W)
                    (ModuleCat.{max v (u + 1)} R)).obj M)

end AlgebraicGeometry.Scheme
