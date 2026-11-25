/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
import WeilConjectures.AlgebraicGeometry.ModuleAcyclicUnderlyingSections

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale

/-- Degree-zero comparison needs only the global sections hypothesis.
Source: Stacks Project, Tags 095T and 01FA.
(blueprint: new-module-acyclic-comparison-zero)

Proof: Forgetting coefficients makes the section restriction bijective. Conjugate
it by the canonical degree-zero cohomology/sections equivalences on X and Y.
The degree-zero pullback formula identifies this conjugate with cohomologyMap. -/
theorem Etale.bijective_cohomologyMap_of_module_acyclic_zero
    {X Y : Scheme.{u}} (i : Y ⟶ X) (r : ℕ)
    (hzero : ∀ G : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))),
      IsIso (globalSectionsUpperStarMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) i G))
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) :
    Function.Bijective (Etale.cohomologyMap i
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))
        AddCommGrpCat.{u + 1})).obj M) 0) := by
  let A := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})).obj M
  let A' := ((i)^*[AddCommGrpCat.{u + 1}]).obj A
  let e : Sheaf.H A 0 ≃+ (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A :=
    (Sheaf.H.equiv₀ A terminalIsTerminal).trans
      (((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).symm.app A)
        |>.addCommGroupIsoToAddEquiv)
  let e' : Sheaf.H A' 0 ≃+ (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A' :=
    (Sheaf.H.equiv₀ A' terminalIsTerminal).trans
      (((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).symm.app A')
        |>.addCommGroupIsoToAddEquiv)
  have hΓ := Etale.bijective_underlying_globalSectionsUpperStarMap i r M (hzero M)
  have he (x : Sheaf.H A 0) : cohomologyMap i A 0 x =
      e'.symm (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i A (e x)) := by
    have hh := cohomologyMap_zero_eq_globalSectionsUpperStarMap i A (e x)
    change cohomologyMap i A 0 (e.symm (e x)) =
      e'.symm (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i A (e x)) at hh
    simpa only [AddEquiv.symm_apply_apply] using hh
  have heq : ⇑(cohomologyMap i A 0) =
      e'.symm ∘ globalSectionsUpperStarMap AddCommGrpCat.{u + 1} i A ∘ e := funext he
  change Function.Bijective (cohomologyMap i A 0)
  rw [heq]
  exact e'.symm.bijective.comp (hΓ.comp e.bijective)

end AlgebraicGeometry
