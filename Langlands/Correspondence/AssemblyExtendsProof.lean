import Langlands.Correspondence.AssemblyZeroMonodromyWitness
import Langlands.Correspondence.AssemblyUniqueness
import Langlands.Correspondence.IrreducibleZeroMonodromy

/-!
# Every assembly of a supercuspidal map extends it

Henniart 2002, §2.9: the full map built from a supercuspidal map `c0` on blocks agrees
with `c0` on irreducible Weil classes. For an irreducible Weil class `σ`, the published
canonical zero-monodromy parameter `D` of `σ` is assembled from `c0` to `c0 σ` with the
single block `σ ⊗ Sp(1)`. An assembly `c` of `c0` assembles `D` to `c D`, and the
published uniqueness of assembled classes gives `c D = c0 σ`.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Henniart 2002, §2.9: every assembly `c` of a supercuspidal map `c0` extends `c0`. -/
theorem assemblyExtends : AssemblyExtendsStatement.{uF, uP, uA} F := by
  intro c0 c hc n σ
  exact ⟨zeroMonodromyParameter F σ, zeroMonodromyParameter_spec F σ,
    isAssembledFrom_unique F c0 (hc n (zeroMonodromyParameter F σ))
      (isAssembledFrom_of_isZeroMonodromyOf F c0 (zeroMonodromyParameter_spec F σ))⟩

end Langlands.Correspondence
