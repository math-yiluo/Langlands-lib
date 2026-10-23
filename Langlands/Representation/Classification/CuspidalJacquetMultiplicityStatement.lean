import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Filtration.MultiplicityStatement
import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Group.GL.OppositeBlocks

/-!
# Cuspidal Jacquet multiplicities

The full upper and opposite normalized Jacquet modules of cuspidal induction
have composition factors counted by actual minimal Levi-conjugating
permutations. These are proposition definitions, not proofs.
-/

namespace Langlands

open CuspidalSupport

universe uF uV uW

namespace CuspidalJacquetMultiplicity

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}

/-- The actual normalized upper induction, bundled with its carrier and
linear structure so subsequent Jacquet constructions share those terms. -/
noncomputable def induced (B : GeneralLinear.BlockShape n)
    (A : Rep.{uV} ℂ (B.Levi F.Carrier)) :
    Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  Rep.of (T.normalizedParabolicInduced B A.ρ)

/-- The actual normalized upper Jacquet representation, in bundled form. -/
noncomputable def upperJacquet (C : GeneralLinear.BlockShape n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    Rep.{uV} ℂ (C.Levi F.Carrier) :=
  Rep.of (T.normalizedJacquet C A.ρ)

/-- The actual opposite coinvariant action with inverse upper full modulus,
transported to the product Levi and bundled with its linear structure. -/
noncomputable def oppositeJacquet (C : GeneralLinear.BlockShape n)
    (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)) :
    Rep.{uV} ℂ (C.Levi F.Carrier) :=
  let δ := (T.leviModulus C).comp (C.leviEquiv F.Carrier).symm.toMonoidHom
  Rep.of ((Jacquet.normalizedActionOfModulus A.ρ
    (C.oppositeUnipotentSubgroup F.Carrier) (C.leviSubgroup F.Carrier)
    (C.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
    δ⁻¹).comp (C.leviEquiv F.Carrier).toMonoidHom)

end CuspidalJacquetMultiplicity

/-- The GL_n specialization of the cuspidal multiplicities in Silberger
1979, Theorem 5.4.1.1, and BZ77, Corollary 2.13(c) and section 2.15(3).
Both normalized Jacquet modules have their full composition length and
each irreducible constituent's exact multiplicity specified. -/
def GLCuspidalJacquetMultiplicityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n →
      ∀ (B C : GeneralLinear.BlockShape n)
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (B.Levi F.Carrier) V),
        Representation.IsIrreducible ρ → IsLeviCuspidal B ρ →
        LevisAssociated (F := F.Carrier) B C →
          let I := CuspidalJacquetMultiplicity.induced T B (Rep.of ρ)
          let Ju := CuspidalJacquetMultiplicity.upperJacquet T C I
          let Jo := CuspidalJacquetMultiplicity.oppositeJacquet T C I
          let length := Nat.card (MinimalConjugatingPermutations (F := F.Carrier) B C)
          HasCompositionSeriesLength Ju length ∧
          HasCompositionSeriesLength Jo length ∧
          ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
            (τ : Representation ℂ (C.Levi F.Carrier) W),
            Representation.IsIrreducible τ →
              ∀ m : ℕ,
                (HasJordanHolderMultiplicity Ju (Rep.of τ) m ↔
                  m = Nat.card (AssociatingPermutations B C ρ τ)) ∧
                (HasJordanHolderMultiplicity Jo (Rep.of τ) m ↔
                  m = Nat.card (AssociatingPermutations B C ρ τ))

/-- Named entry point for the complete cuspidal length and multiplicity family. -/
def GLCuspidalJacquetMultiplicityPrerequisitesStatement : Prop :=
  GLCuspidalJacquetMultiplicityStatement.{uF, uV, uW}

end Langlands
