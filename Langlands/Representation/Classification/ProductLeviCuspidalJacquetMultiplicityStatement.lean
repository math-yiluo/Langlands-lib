import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Parabolic.OppositeRefinementFunctors

/-!
# Opposite cuspidal Jacquet multiplicities inside a product Levi

A derived product-Levi specialization of the cuspidal Weyl-factor formulas
of Silberger 1979, Theorem 5.4.1.1, and BZ77, Corollary 2.13(c) and §2.15(3).
This is a proposition definition, not a proof.
-/

namespace Langlands

open GeneralLinear Geometric CuspidalSupport

universe uF uV uW

/-- The full opposite self-Jacquet module of cuspidal induction inside an
actual product Levi has the length and constituent multiplicities counted
by actual minimal conjugating permutations within that coarse Levi. -/
def ProductLeviCuspidalJacquetMultiplicityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B),
      let C := B.flatten S
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ (C.Levi F.Carrier) V),
        Representation.IsIrreducible σ → IsLeviCuspidal C σ →
          let e := flattenedLeviEquiv F.Carrier B S
          let σr : Rep.{uV} ℂ (refinedLevi F.Carrier B S) :=
            Rep.of (σ.comp e.symm.toMonoidHom)
          letI := T.leviTopologicalGroup B
          let I : Rep.{max uF uV} ℂ (B.Levi F.Carrier) :=
            Rep.of (T.normalizedRefinedInduced B S σr.ρ)
          let J : Rep.{max uF uV} ℂ (refinedLevi F.Carrier B S) :=
            Rep.of (T.normalizedRefinedOppositeJacquet B S I.ρ)
          HasCompositionSeriesLength J
            (Nat.card {w : MinimalConjugatingPermutations (F := F.Carrier) C C //
              w.val.val ∈ blockWeyl B}) ∧
          ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
            (τ : Representation ℂ (C.Levi F.Carrier) W),
            Representation.IsIrreducible τ →
              ∀ m : ℕ,
                HasJordanHolderMultiplicity J (Rep.of (τ.comp e.symm.toMonoidHom)) m ↔
                  m = Nat.card {w : AssociatingPermutations C C σ τ //
                    w.val.val.val ∈ blockWeyl B}

end Langlands
