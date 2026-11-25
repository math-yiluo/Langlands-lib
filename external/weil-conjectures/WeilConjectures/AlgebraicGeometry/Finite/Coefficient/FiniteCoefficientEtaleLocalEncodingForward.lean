/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleLocalEncodingForwardBridge

/-! # Forward transport from etale finite models to fixed-scalar pro-etale models

Source: Stacks Project, proetale.tex, Tag 099Y; sites-modules.tex, Tag 04IX.
(blueprint: lem-weil-pbc-finite-coefficient-etale-local-encoding-forward).

This is the forward direction of the local-model comparison. It is split from
`finiteCoefficient_etaleLocal_encoding` so that the etale-to-pro-etale covering
transport can be proved independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Etale finite local models give fixed-scalar pro-etale finite local models.

Source: Stacks Project, proetale.tex, Tag 099Y, and sites-modules.tex, Tag 04IX.
(blueprint: lem-weil-pbc-finite-coefficient-etale-local-encoding-forward).

Proof: Use the identity etale chart, regard an etale covering as a pro-etale
covering, and pull it back along each pro-etale object. Transport the displayed
models through scalar restriction, localization, and normalized constant-module
comparisons. -/
theorem finiteCoefficient_etaleLocal_encoding_forward
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
    P F → ProFiniteModels.fixedModels (ProEt.topology V.left) (ULift.{t + 1} B)
      ((finiteCoefficientSliceRestriction X B R φ V).obj F) := by
  dsimp
  intro hP
  let H := finiteCoefficientSliceRestriction X B R φ V
  let e := proEtaleModuleEncoding V.left B
  let G := e.inverse.obj (H.obj F)
  have hG : IsFinitelyPresentedLocallyConstantProEtaleModule G := by
    exact finiteCoefficient_etaleLocal_encoding_forward_bridge X B R φ hφ V F hP
  have hfixed : ProFiniteModels.fixedModels (ProEt.topology V.left)
      (ULift.{t + 1} B) (H.obj F) := by
    have hfixedG := (ProFiniteModels.intrinsic_fixedModels V.left B G).mp hG
    exact ProFiniteModels.fixedModels_of_iso _ _ (e.counitIso.app (H.obj F)) hfixedG
  exact hfixed

end AlgebraicGeometry.Scheme
