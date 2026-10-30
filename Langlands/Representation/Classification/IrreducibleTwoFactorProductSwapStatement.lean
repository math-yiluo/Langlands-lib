import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement

/-!
# Swapping the factors of an irreducible equal-rank product

For irreducible smooth representations `α, β` of `GL_k(F)` with `k > 0`, if the
actual upper normalized product `α × β` on `GL_{2k}(F)` is irreducible, then it
is isomorphic to `β × α`. This is the irreducible case of Zelevinsky 1980,
Theorem 1.9, printed p.174, for two blocks of equal rank. This module supplies
the proposition only.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For positive rank `k` and irreducible smooth representations `α, β` of
`GL_k(F)`, irreducibility of the actual upper normalized product `α × β` (first
block `α`, second block `β`) implies that it is isomorphic, as a smooth
representation of `GL_{2k}(F)`, to `β × α`. This definition supplies the
proposition only. -/
def IrreducibleTwoFactorProductSwap : Prop :=
  letI := T.topology
  ∀ (k : ℕ) (hk : 0 < k)
    (α β : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)),
    α.IsIrreducible → β.IsIrreducible →
    ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
      (twoBlockFactors hk hk α β)).IsIrreducible →
    Nonempty ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
        (twoBlockFactors hk hk α β) ≅
      (T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
        (twoBlockFactors hk hk β α))

end Langlands.Classification
