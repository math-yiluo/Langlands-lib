import Langlands.Representation.CuspidalSupport.AssociationForwardStatement

/-! The adjacent block-swap factor-matching step in BZ77 sections 2.16–2.17. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV uW

/-- A minimal conjugating permutation that exchanges two neighbouring blocks
carries irreducible cuspidal data to normalized inductions with the same
Jordan–Hölder factors, including multiplicities. -/
def AdjacentBlockSwapCuspidalInductionFactorsTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ), 0 < n →
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (B C : BlockShape n) (w : Equiv.Perm (Fin n))
      (hw : ConjugatesLevi (F := F.Carrier) B C w) (j : ℕ), j + 1 < B.length →
      (∀ a, (Geometric.blockIndex C (w a) : ℕ) =
        Equiv.swap j (j + 1) (Geometric.blockIndex B a : ℕ)) →
      Geometric.IsMinimalRepresentative B C w →
      ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
        (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
        σ.IsIrreducible → IsLeviCuspidal B σ.representation →
        τ.IsIrreducible → IsLeviCuspidal C τ.representation →
        Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
        HaveSameJordanHolderFactors
          (Rep.of (T.normalizedParabolicInduced B σ.representation))
          (Rep.of (T.normalizedParabolicInduced C τ.representation))

end Langlands.CuspidalSupport
