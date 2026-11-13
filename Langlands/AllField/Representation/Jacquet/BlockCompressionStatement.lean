import Langlands.Representation.Jacquet.BlockCompressionStatement
import Langlands.AllField.Group.GL.BlockIwahoriDefinitions
/-!
# Normalized block compression and the upper Jacquet quotient

This is a statement about the published compact average, with no new operator
data and no assertion of stabilization or canonical-lift bijectivity.
-/

namespace Langlands.AllField.Jacquet
open Langlands.Jacquet hiding BlockCompressionStatement
open Langlands.AllField.Jacquet

universe uF uV

/-- Normalized compression is multiplicative on the weak block chamber and
intertwines the actual upper Jacquet quotient with its unnormalized Levi action.
This is a derived translation of the laws motivating Casselman III.5.1–III.5.3,
using the published weak-chamber factorization predicate. -/
def BlockCompressionStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) (B : GeneralLinear.BlockShape n),
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F))
      (hK : IsCompact (K : Set (GeneralLinear n F))),
      (Langlands.AllField.GeneralLinear.BlockShape.HasBlockIwahoriFactorization B) T K →
        (∀ a b : Fin B.length → Fˣ,
          (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T a → (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T b →
            compressedAction ρ hρ K hK (B.blockScalar F (a * b)) =
              compressedAction ρ hρ K hK (B.blockScalar F a) *
                compressedAction ρ hρ K hK (B.blockScalar F b)) ∧
        (∀ a : Fin B.length → Fˣ, (Langlands.AllField.GeneralLinear.BlockShape.IsWeaklyContracting B) T a →
          ∀ v : fixedVectors ρ K.toSubgroup,
            mk ρ (B.unipotentSubgroup F)
                (compressedAction ρ hρ K hK (B.blockScalar F a) v : V) =
              action ρ (B.unipotentSubgroup F) (B.leviSubgroup F)
                (B.leviSubgroup_le_normalizer_unipotentSubgroup F)
                (B.blockScalarInLevi F a)
                (mk ρ (B.unipotentSubgroup F) (v : V)))

end Langlands.AllField.Jacquet
