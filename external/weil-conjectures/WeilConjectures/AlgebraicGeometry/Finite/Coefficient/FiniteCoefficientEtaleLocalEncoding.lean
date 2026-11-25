/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleLocalEncodingForward
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleLocalEncodingReverse

/-! # Comparing finite etale models with intrinsic pro-etale local systems

Source: Stacks Project, proetale.tex, Tag 099Y, lemma-compare-locally-constant;
sites-modules.tex, localization of ringed sites, Tag 04IX.
(blueprint: lem-weil-pbc-finite-coefficient-etale-local-encoding).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The etale finite-model condition for a single sheaf agrees with finite
pro-etale models of its existing fixed-scalar chart restriction.
This compares local models; it asserts no exactness or closure property.

Source: Stacks Project, proetale.tex, Tag 099Y, lemma-compare-locally-constant;
sites-modules.tex, Tag 04IX, localization of ringed sites; Tags 03CY and 093J,
constant modules and change of coefficients.
(blueprint: lem-weil-pbc-finite-coefficient-etale-local-encoding).

Proof: use the already constructed finiteCoefficientSliceRestriction. Its scalar
restriction along phi retains the underlying additive sheaf, and its localization
is the sectionwise restriction to the scheme of the chart. The concrete slice
localization equivalence and the normalized constant-module sheafification
comparisons therefore identify the two forms of constant local models.
For the forward implication, the etale-model condition at W = V and id supplies
an etale covering of V. It is also a pro-etale covering. The sheafification
universal property, with the identity on constant sections, identifies each
displayed model with the fixed-coefficient constant sheaf of the lifted N.
Pull back this covering to every pro-etale object to obtain the fixed-scalar
finite local-model condition.

For the reverse implication, restrict to any etale W -> V. Local constant models
restrict to local constant models on its scheme. The lifted ring B is Noetherian,
so the finite modules are finitely presented. Apply the coefficient-sized
finitely presented local-system etale-cover theorem to the fixed-scalar sheaf
associated to this chart restriction. Its etale constant charts cover W.
Each finitely presented module over the finite lifted ring is a finite set, so
choose its finite representative in universe t and transport its B-module action
along the finite-set equivalence. The corresponding lifted module is isomorphic
to the original value. The normalized constant-module and slice comparisons turn
these chart isomorphisms into precisely the displayed completedAdicChange models.
Generate a covering sieve from these charts and restrict the isomorphisms to all
its members. This proves the condition for every W -> V. Empty charts and the
zero ring are included: the arguments use covers and sheafification, and never
require a point or a faithful constant functor. -/
theorem finiteCoefficient_etaleLocal_encoding
    (X : Scheme.{t}) (B : Type t) [CommRing B] [Finite B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (hφ : IsIso φ) (V : X.Etale)
    (F : SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) :
    let R₀ := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
    let P : ObjectProperty (SheafOfModules.{t + 1} R₀) := fun F ↦
      ∀ (W : X.Etale) (_g : W ⟶ V),
        ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
          ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
            ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
              ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj F ≅
                (SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((completedAdicChange X (φ)).obj
                    ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                      ModuleCat.restrictScalars.{t + 1}
                        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                      koszulConstantFunctor X B).obj N)))
    P F ↔ ProFiniteModels.fixedModels (ProEt.topology V.left) (ULift.{t + 1} B)
      ((finiteCoefficientSliceRestriction X B R φ V).obj F) := by
  dsimp
  constructor
  · exact finiteCoefficient_etaleLocal_encoding_forward X B R φ hφ V F
  · exact finiteCoefficient_etaleLocal_encoding_reverse X B R φ hφ V F

end AlgebraicGeometry.Scheme
