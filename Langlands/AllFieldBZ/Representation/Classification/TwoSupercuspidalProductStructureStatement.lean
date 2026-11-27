import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalTwist
import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement

/-!
# All-field port of `Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement`

The irreducibility proposition of Zelevinsky 1980, Proposition 1.11(a), over an
arbitrary nonarchimedean local field (`Langlands.AllFieldBZ.LocalFieldPackage`).
The field-independent block family `Langlands.Classification.twoBlockFactors` of the
original module is used unchanged. See the paired Markdown.
-/

namespace Langlands.AllFieldBZ.Classification

open Langlands.GeneralLinear

universe uF uV

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

/-- Ze80 Proposition 1.11(a): if `ρ' ≇ νρ` and `ρ ≇ νρ'`, the normalized product
`ρ × ρ'` of supercuspidal representations of `GL_k` and `GL_l` is irreducible.
The two twist relations compare rank-indexed isomorphism classes, so unequal
ranks are never related. -/
def TwoSupercuspidalNonadjacentProductIrreducible : Prop :=
  letI := T.topology
  ∀ (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (ρ : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (ρ' : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := l)),
    (⟨l, ρ'.isoClass⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
      ⟨k, T.supercuspidalClassRealPowerTwist k 1 ρ.isoClass⟩ →
    (⟨k, ρ.isoClass⟩ : Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) ≠
      ⟨l, T.supercuspidalClassRealPowerTwist l 1 ρ'.isoClass⟩ →
    ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks k l hk hl)).obj
      (Langlands.Classification.twoBlockFactors hk hl ρ.obj ρ'.obj)).IsIrreducible

end Langlands.AllFieldBZ.Classification
