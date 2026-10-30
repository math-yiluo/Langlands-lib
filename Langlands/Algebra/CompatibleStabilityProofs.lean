import Langlands.Algebra.CompatibleStabilityStatements
import Langlands.LinearAlgebra.StableEndomorphismProofs

/-!
# Proofs of the stability criteria for compatible nonunital algebra actions

Internal specialization of Renard 2026, C.II, Definition and Lemma (i)–(iii),
printed pp. 276–278 / PDF pp. 282–284, to actual compatible actions and linear
intertwiners. The published complex-linear criteria are applied to the underlying
linear maps; kernels, ranges and complementarity are transported through the
compatible-submodule lattice.
-/

set_option autoImplicit false

namespace Langlands.Algebra.CompatibleStability

open Langlands.LinearAlgebra.StableEndomorphism
  (Stable stable_iff_isCompl stable_of_rightExact stable_of_leftExact)

universe uB uV uA uM uC

section OneSpace

variable {B : Type uB} [NonUnitalRing B] [Module ℂ B]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : B →ₙₐ[ℂ] Module.End ℂ V}

/-- The bundled self-composition of an intertwiner has the square as underlying map. -/
theorem toLinearMap_comp_self (f : LinearIntertwiner ρ ρ) :
    (f.comp f).toLinearMap = f.toLinearMap ^ 2 := by
  rw [LinearIntertwiner.toLinearMap_comp, pow_two, Module.End.mul_eq_comp]

/-- Complementarity in the compatible-submodule lattice is complementarity of the
underlying subspaces. -/
theorem isCompl_iff_isCompl_toSubmodule {S T : CompatibleSubmodule ρ} :
    IsCompl S T ↔ IsCompl S.toSubmodule T.toSubmodule := by
  constructor
  · intro h
    refine ⟨disjoint_iff.2 ?_, codisjoint_iff.2 ?_⟩
    · rw [← CompatibleSubmodule.inf_toSubmodule, h.inf_eq_bot,
        CompatibleSubmodule.bot_toSubmodule]
    · rw [← CompatibleSubmodule.sup_toSubmodule, h.sup_eq_top,
        CompatibleSubmodule.top_toSubmodule]
  · intro h
    refine ⟨disjoint_iff.2 ?_, codisjoint_iff.2 ?_⟩
    · apply CompatibleSubmodule.toSubmodule_injective
      rw [CompatibleSubmodule.inf_toSubmodule, h.inf_eq_bot,
        CompatibleSubmodule.bot_toSubmodule]
    · apply CompatibleSubmodule.toSubmodule_injective
      rw [CompatibleSubmodule.sup_toSubmodule, h.sup_eq_top,
        CompatibleSubmodule.top_toSubmodule]

/-- Stability of the underlying map is equality of the compatible kernels and ranges of
the intertwiner and its bundled square. -/
theorem stable_iff_ker_eq_and_range_eq (f : LinearIntertwiner ρ ρ) :
    Stable f.toLinearMap ↔ f.ker = (f.comp f).ker ∧ f.range = (f.comp f).range := by
  rw [← CompatibleSubmodule.toSubmodule_inj, ← CompatibleSubmodule.toSubmodule_inj,
    LinearIntertwiner.ker_toSubmodule, LinearIntertwiner.ker_toSubmodule,
    LinearIntertwiner.range_toSubmodule, LinearIntertwiner.range_toSubmodule,
    toLinearMap_comp_self]
  rfl

/-- Lemma (i) in the compatible-submodule lattice. -/
theorem stable_iff_isCompl_ker_range (f : LinearIntertwiner ρ ρ) :
    Stable f.toLinearMap ↔ IsCompl f.ker f.range := by
  rw [isCompl_iff_isCompl_toSubmodule, LinearIntertwiner.ker_toSubmodule,
    LinearIntertwiner.range_toSubmodule]
  exact stable_iff_isCompl f.toLinearMap

end OneSpace

section Rows

variable {B : Type uB} [NonUnitalRing B] [Module ℂ B]
  {A : Type uA} {M : Type uM} {C : Type uC}
  [AddCommGroup A] [Module ℂ A] [AddCommGroup M] [Module ℂ M] [AddCommGroup C] [Module ℂ C]
  {ρA : B →ₙₐ[ℂ] Module.End ℂ A} {ρM : B →ₙₐ[ℂ] Module.End ℂ M}
  {ρC : B →ₙₐ[ℂ] Module.End ℂ C}

/-- Middle exactness in the compatible lattice is middle exactness of the underlying maps. -/
theorem range_eq_ker_toLinearMap {phi : LinearIntertwiner ρA ρM}
    {psi : LinearIntertwiner ρM ρC} (hexact : phi.range = psi.ker) :
    LinearMap.range phi.toLinearMap = LinearMap.ker psi.toLinearMap := by
  rw [← LinearIntertwiner.range_toSubmodule, ← LinearIntertwiner.ker_toSubmodule, hexact]

/-- Lemma (ii) for actual intertwiners in an exact row `A → M → C → 0`. -/
theorem stable_of_rightExact_intertwiners (phi : LinearIntertwiner ρA ρM)
    (psi : LinearIntertwiner ρM ρC) (fA : LinearIntertwiner ρA ρA)
    (fM : LinearIntertwiner ρM ρM) (fC : LinearIntertwiner ρC ρC)
    (hexact : phi.range = psi.ker) (hsurj : Function.Surjective psi)
    (hphi : fM.comp phi = phi.comp fA) (hpsi : fC.comp psi = psi.comp fM)
    (hA : Stable fA.toLinearMap) (hM : Stable fM.toLinearMap) :
    Stable fC.toLinearMap :=
  stable_of_rightExact phi.toLinearMap psi.toLinearMap fA.toLinearMap fM.toLinearMap
    fC.toLinearMap (range_eq_ker_toLinearMap hexact) hsurj
    (congrArg LinearIntertwiner.toLinearMap hphi)
    (congrArg LinearIntertwiner.toLinearMap hpsi) hA hM

/-- Lemma (iii) for actual intertwiners in an exact row `0 → A → M → C`. -/
theorem stable_of_leftExact_intertwiners (phi : LinearIntertwiner ρA ρM)
    (psi : LinearIntertwiner ρM ρC) (fA : LinearIntertwiner ρA ρA)
    (fM : LinearIntertwiner ρM ρM) (fC : LinearIntertwiner ρC ρC)
    (hinj : Function.Injective phi) (hexact : phi.range = psi.ker)
    (hphi : fM.comp phi = phi.comp fA) (hpsi : fC.comp psi = psi.comp fM)
    (hM : Stable fM.toLinearMap) (hC : Stable fC.toLinearMap) :
    Stable fA.toLinearMap :=
  stable_of_leftExact phi.toLinearMap psi.toLinearMap fA.toLinearMap fM.toLinearMap
    fC.toLinearMap hinj (range_eq_ker_toLinearMap hexact)
    (congrArg LinearIntertwiner.toLinearMap hphi)
    (congrArg LinearIntertwiner.toLinearMap hpsi) hM hC

end Rows

/-! ### The closed statements -/

theorem stableKernelRange : StableKernelRangeStatement.{uB, uV} :=
  fun _ _ _ _ _ _ _ _ _ f => stable_iff_ker_eq_and_range_eq f

theorem stableIffIsCompl : StableIffIsComplStatement.{uB, uV} :=
  fun _ _ _ _ _ _ _ _ _ f => stable_iff_isCompl_ker_range f

theorem stableOfRightExact : StableOfRightExactStatement.{uB, uA, uM, uC} :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ phi psi fA fM fC =>
    stable_of_rightExact_intertwiners phi psi fA fM fC

theorem stableOfLeftExact : StableOfLeftExactStatement.{uB, uA, uM, uC} :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ phi psi fA fM fC =>
    stable_of_leftExact_intertwiners phi psi fA fM fC

/-- The complete closed family of compatible-action stability criteria. -/
theorem compatibleStability : CompatibleStabilityStatements.{uB, uV, uA, uM, uC} :=
  ⟨stableKernelRange, stableIffIsCompl, stableOfRightExact, stableOfLeftExact⟩

end Langlands.Algebra.CompatibleStability
