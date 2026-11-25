/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsPowerInclusion
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

/-! # The additive quotient of consecutive nilradical ideal powers

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-ideal-power-quotient)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- The actual module quotient `N^(j+1)/N^(j+2)` on X. Both ideal modules are
categorical kernels of restrictions of the structure sheaf. Their inclusion is
`IdealSheafData.toModulesOfLE`; the quotient is its categorical cokernel.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-ideal-power-quotient) -/
noncomputable def reductionIdealPowerQuotient (X : Scheme.{u}) (j : ℕ) : X.Modules :=
  cokernel (IdealSheafData.toModulesOfLE (reduction_nilradical_power_le X j))

private theorem isQuasicoherent_idealModule {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.toModules.IsQuasicoherent := by
  have := SheafOfModules.isQuasicoherent_unit (R := I.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((SheafOfModules.pushforward I.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) :=
    Modules.isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated I.subschemeι _
  exact Modules.isQuasicoherent_kernel I.toPushforwardSubscheme

/-- The quotient of consecutive nilradical powers is quasi-coherent.
Proof: the module of any ideal sheaf is the kernel of the structure sheaf's
restriction to its closed subscheme. Closed-immersion pushforward preserves
quasi-coherence, and kernels and cokernels of maps of quasi-coherent modules
are quasi-coherent. This needs no finite generation or Noetherian assumption.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-ideal-power-quotient) -/
instance isQuasicoherent_reductionIdealPowerQuotient (X : Scheme.{u}) (j : ℕ) :
    (X.reductionIdealPowerQuotient j).IsQuasicoherent := by
  have := isQuasicoherent_idealModule (X.nilradical ^ (j + 1 + 1))
  have := isQuasicoherent_idealModule (X.nilradical ^ (j + 1))
  exact Modules.isQuasicoherent_cokernel
    (IdealSheafData.toModulesOfLE (reduction_nilradical_power_le X j))

end AlgebraicGeometry.Scheme
