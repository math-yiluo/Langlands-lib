import Langlands.Algebra.RenardAlgebraActionLocalization
import Langlands.Algebra.CompatibleSubmodule
import Langlands.Algebra.CompatibleUnitization
import Langlands.LinearAlgebra.StableEndomorphismStatements

/-!
# The canonical compatible stable image of actual localization

Internal finiteness-free statement refining the stable-image conclusion
of Renard 2026, Appendix C.II, printed p. 279 / PDF p. 285, over the
actual compatible nonunital algebra action.
-/

set_option autoImplicit false

namespace Langlands.Renard.AlgebraActionLocalization

open Langlands.Algebra EndomorphismLocalization
open Langlands.LinearAlgebra.StableEndomorphism

universe uB uV

/-- Complementarity and the unique action-compatible, operator-compatible
equivalence whose inverse is the restriction of the actual canonical map. -/
def CompatibleStablePowerImageAt {B : Type uB} [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ) (n : ℕ) : Prop :=
  let a := f.toLinearMap
  let ha : ∀ b z, a (ρ b z) = ρ b (a z) := fun b z => f.map_action' b z
  let σ := localizedAction a ρ ha
  letI := CompatibleUnitization.module ρ
  let powers : ℕ → LinearIntertwiner ρ ρ := fun m =>
    CompatibleUnitization.toLinearIntertwiner
      ((CompatibleUnitization.ofLinearIntertwiner f) ^ m)
  let K := (powers n).ker
  let I := (powers n).range
  IsCompl K I ∧
    ∃! e : Localized a ≃ₗ[ℂ] I.toSubmodule,
      (∀ b z, e (σ b z) = I.restrictAction b (e z)) ∧
        I.toSubmodule.subtype.comp (e.toLinearMap.comp (localizedEnd a)) =
          a.comp (I.toSubmodule.subtype.comp e.toLinearMap) ∧
        e.symm.toLinearMap = (iota a).comp I.toSubmodule.subtype

/-- Every positive stable power gives the canonical compatible stable image,
without any finiteness, unit-law or nondegeneracy premise. -/
def CompatibleStablePowerImageStatement : Prop :=
  ∀ (B : Type uB) [NonUnitalRing B] [Module ℂ B]
    [IsScalarTower ℂ B B] [SMulCommClass ℂ B B]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : B →ₙₐ[ℂ] Module.End ℂ V) (f : LinearIntertwiner ρ ρ) (n : ℕ),
    0 < n → Stable (f.toLinearMap ^ n) → CompatibleStablePowerImageAt ρ f n

end Langlands.Renard.AlgebraActionLocalization
