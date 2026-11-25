/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Fixed scalar coordinates for restriction to an etale chart

Source: Stacks Project, Tags 03CY, 099R and 09AL
(blueprint: def-weil-pbc-finite-coefficient-slice-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem scalar_exact (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) RingCat.{t + 1}} (φ : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1} φ) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{t + 1} φ) := by
  let U := SheafOfModules.toSheaf.{t + 1} R
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{t + 1} R) :=
    @SheafOfModules.preservesFiniteColimits_toSheaf.{t + 1, t, t + 1, t + 1}
      X.ProEt inferInstance (ProEt.topology X) R inferInstance
        (finitePerfectModelsAbLocallyBijective X)
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{t + 1} S) :=
    @SheafOfModules.preservesFiniteColimits_toSheaf.{t + 1, t, t + 1, t + 1}
      X.ProEt inferInstance (ProEt.topology X) S inferInstance
        (finitePerfectModelsAbLocallyBijective X)
  have : ReflectsFiniteColimits U :=
    { reflects := fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  have : PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1} φ ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{t + 1} S))
  have : PreservesFiniteColimits (SheafOfModules.restrictScalars.{t + 1} φ ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{t + 1} S))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ U,
    preservesFiniteColimits_of_reflects_of_preserves _ U⟩

/-- Restrict the action to constant scalars, then restrict sections to the chart.
Source: Stacks Project, Tags 03CY and 099R
(blueprint: def-weil-pbc-finite-coefficient-slice-restriction). -/
def finiteCoefficientSliceRestriction (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (V : X.Etale) :=
  SheafOfModules.restrictScalars.{t + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ) ⋙
    proEtaleModuleRestriction X B ⋙
      ProEtale.localizationRestriction (ModuleCat.{t + 1} (ULift.{t + 1} B))
        V.hom inferInstance

/-- The coordinate functor is additive and exact.
Source: Stacks Project, Tags 03CY and 099R
(blueprint: def-weil-pbc-finite-coefficient-slice-restriction).
Proof: scalar restriction leaves the additive sheaf unchanged, constant-scalar
encoding is an equivalence, and restriction along a site object is exact. -/
theorem finiteCoefficientSliceRestriction_exact (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (V : X.Etale) :
    (finiteCoefficientSliceRestriction X B R φ V).Additive ∧
      PreservesFiniteLimits (finiteCoefficientSliceRestriction X B R φ V) ∧
      PreservesFiniteColimits (finiteCoefficientSliceRestriction X B R φ V) := by
  have := (scalar_exact X ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)).1
  have := (scalar_exact X ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)).2
  have := proEtaleModuleRestriction_isEquivalence X B
  have : (proEtaleModuleRestriction X B).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (ProEtale.localizationRestriction
      (ModuleCat.{t + 1} (ULift.{t + 1} B)) V.hom inferInstance).Additive :=
    { map_add := rfl }
  have : PreservesFiniteLimits (ProEtale.localizationRestriction
      (ModuleCat.{t + 1} (ULift.{t + 1} B)) V.hom inferInstance) := by
    dsimp [ProEtale.localizationRestriction]
    infer_instance
  have := (ProEtale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{t + 1} (ULift.{t + 1} B)) V.hom inferInstance).isLeftAdjoint
  unfold finiteCoefficientSliceRestriction
  exact ⟨inferInstance, inferInstance, inferInstance⟩

instance finiteCoefficientSliceRestriction_additive (X : Scheme.{t}) (B : Type t)
    [CommRing B] (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (V : X.Etale) :
    (finiteCoefficientSliceRestriction X B R φ V).Additive :=
  (finiteCoefficientSliceRestriction_exact X B R φ V).1

instance finiteCoefficientSliceRestriction_preservesFiniteLimits (X : Scheme.{t})
    (B : Type t) [CommRing B] (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (V : X.Etale) :
    PreservesFiniteLimits (finiteCoefficientSliceRestriction X B R φ V) :=
  (finiteCoefficientSliceRestriction_exact X B R φ V).2.1

instance finiteCoefficientSliceRestriction_preservesFiniteColimits (X : Scheme.{t})
    (B : Type t) [CommRing B] (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (V : X.Etale) :
    PreservesFiniteColimits (finiteCoefficientSliceRestriction X B R φ V) :=
  (finiteCoefficientSliceRestriction_exact X B R φ V).2.2

/-- Vanishing on the ringed slice implies vanishing in fixed scalar coordinates.
Source: Stacks Project, Tag 099R
(blueprint: def-weil-pbc-finite-coefficient-slice-restriction).
Proof: every object of the chart site has its canonical arrow to the chart;
evaluation there is evaluation of the zero restricted module sheaf. -/
theorem finiteCoefficientSliceRestriction_isZero (X : Scheme.{t}) (B : Type t)
    [CommRing B] (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (V : X.Etale)
    (M : SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R))
    (hz : IsZero ((SheafOfModules.overFunctor.{t + 1} _ ((toProEt X).obj V)).obj M)) :
    IsZero ((finiteCoefficientSliceRestriction X B R φ V).obj M) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let U := (MorphismProperty.Over.map (f := V.hom) ⊤
    (show WeaklyEtale V.hom from inferInstance)).obj T.unop
  let p : U ⟶ (toProEt X).obj V := MorphismProperty.Over.homMk T.unop.hom rfl
  have he := ((SheafOfModules.forget _) ⋙
    (PresheafOfModules.evaluation _ (op (Over.mk p)))).map_isZero hz
  have hs := ModuleCat.isZero_iff_subsingleton.mp he
  exact hs.elim _ _

end AlgebraicGeometry.Scheme
