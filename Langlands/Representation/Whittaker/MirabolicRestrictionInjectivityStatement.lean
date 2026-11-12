import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Group.GL.Mirabolic
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Injectivity of restriction to the mirabolic subgroup

Jacquet and Shalika 1981, Section (1.1) (printed pages 504–505): for an irreducible
admissible generic representation `π` of `GL_r(F)` over a nonarchimedean local field
`F`, the map `W ↦ W|P` from the Whittaker model to functions on the mirabolic subgroup
`P` is a bijection onto the Kirillov space. This file states its injective half on the
original representation space.
-/

namespace Langlands.Whittaker

open Langlands.GeneralLinear Langlands.HarmonicAnalysis

universe uF uV

/-- Jacquet and Shalika 1981, Section (1.1), printed page 505, injective half. For every
nonarchimedean local field `F`, every rank `n + 1`, every nontrivial unitary additive
character `ψ` and every irreducible admissible generic representation `π` of
`GL_(n+1)(F)` on a complex vector space `V`, and every nonzero standard `ψ`-Whittaker
functional `ℓ`, the map `v ↦ (p ↦ ℓ(π(p) v))` from `V` to functions on the mirabolic
subgroup `mirabolic n F` is injective. -/
def MirabolicRestrictionInjectivityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V),
    IsGeneric ψ n π →
    ∀ ℓ : glFunctionals ψ n π, ℓ.val ≠ 0 →
      Function.Injective (fun v : V => fun p : mirabolic n F => ℓ.val (π p.val v))

end Langlands.Whittaker
