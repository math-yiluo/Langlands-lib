import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement

/-!
# Reducibility of an adjacent two-supercuspidal product

The reducibility step of Zelevinsky 1980, Proposition 1.11(b), printed p.175:
for supercuspidal representations `ρ, ρ'` of `GL_k`, with `k > 0` and
`ρ' ≅ νρ` or `ρ ≅ νρ'`, the upper normalized product `ρ × ρ'` is not
irreducible. Here `ν = |det|`, and induction uses positive half-modulus
covariance. The field and input carrier universes are independent.

This is a proposition definition, not a proof. Ze80 sketches the analytic
reducibility argument; BZ77 Remark 4.2(2) announces the result.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Ze80 Proposition 1.11(b), reducibility step: for positive rank `k` and
supercuspidal `ρ, ρ'` with `ρ' ≅ νρ` or `ρ ≅ νρ'`, the actual upper normalized
product `ρ × ρ'` is not irreducible. The twist is `ν = |det|`; the factor order
is `ρ` in the first block and `ρ'` in the second. This definition supplies the
proposition only. -/
def TwoSupercuspidalAdjacentProductReducible : Prop :=
  letI := T.topology
  ∀ (k : ℕ) (hk : 0 < k)
    (ρ ρ' : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)),
    (ρ'.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ.isoClass ∨
      ρ.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ'.isoClass) →
    ¬ ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
      (twoBlockFactors hk hk ρ.obj ρ'.obj)).IsIrreducible

end Langlands.Classification
