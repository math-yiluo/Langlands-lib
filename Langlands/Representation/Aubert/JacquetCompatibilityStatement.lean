import Langlands.Representation.Aubert.AlternatingOperator
import Langlands.Representation.Aubert.RefinedAlternatingOperator
import Langlands.Representation.CuspidalSupport.LeviGrothendieckTransport
import Langlands.Group.GL.ReverseBlocks

/-!
# Reversed-Levi Jacquet compatibility of the actual unadjusted Aubert operator

The proposition is the second equality of Aubert's Theorem 1.7(2), specialized
to actual GL block shapes. It is stated on the full exact finite-length K0,
including rank zero. The small concrete reversal-conjugacy lemma is proved;
the asserted Jacquet compatibility is not proved in this module.
-/

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe uF

/-- The existing permutation from reversed-block coordinates to original
coordinates conjugates the actual reversed product Levi onto the original. -/
theorem conjugatesLevi_reversePermutation (F : Type uF) [Field F]
    {n : ℕ} (B : BlockShape n) :
    ConjugatesLevi (F := F) B.reverse B B.reversePermutation := by
  apply conjugatesLevi_of_blockIndex B.reversePermutation (fun i => (i.rev : ℕ))
    (Fin.val_injective.comp Fin.revPerm.injective)
  intro a
  obtain ⟨⟨i, x⟩, rfl⟩ := B.reverse.indexEquiv.surjective a
  change (blockIndex B (B.reversePermutation (B.reverse.index i x)) : ℕ) =
    ((blockIndex B.reverse (B.reverse.index i x)).rev : ℕ)
  have h1 : blockIndex B (B.reversePermutation (B.reverse.index i x)) =
      (i : Fin B.length).rev :=
    (congrArg (blockIndex B) (B.reversePermutation_index (i : Fin B.length) x)).trans
      (blockIndex_index B (i : Fin B.length).rev x)
  have h2 : (blockIndex B.reverse (B.reverse.index i x)).rev = i.rev :=
    congrArg Fin.rev (blockIndex_index B.reverse i x)
  exact (congrArg Fin.val h1).trans (congrArg Fin.val h2).symm

end Langlands.CuspidalSupport

namespace Langlands.Aubert

open GeneralLinear Parabolic CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Actual normalized upper Jacquet restriction intertwines the unadjusted
Aubert operators after the specified reversed-Levi transport. This is the
second equality of Aubert's Theorem 1.7(2), with all ranks retained. -/
def JacquetCompatibilityStatement : Prop := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact ∀ (n : ℕ) (B : BlockShape n),
    (normalizedJacquetK0.{uF, uV} F T B).comp
        (alternatingOperator.{uF, uV} F T n) =
      (leviTransportK0.{uF, uV} F.Carrier B.reverse B B.reversePermutation
        (conjugatesLevi_reversePermutation F.Carrier B)).toLinearMap.comp
          ((alternatingOperatorOnLevi.{uF, uV} F T B.reverse).comp
            (normalizedJacquetK0.{uF, uV} F T B.reverse))

end Langlands.Aubert
