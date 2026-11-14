import Langlands.AllFieldBZ.Group.GL.BlockIwahoriDefinitions
import Langlands.Representation.Jacquet.BlockCompressionStatement

/-!
# All-field port of `Langlands.Representation.Jacquet.BlockCompressionStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Jacquet.BlockCompressionStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Jacquet
open Langlands.Jacquet hiding BlockCompressionStatement
universe uF uV

/-- Normalized compression is multiplicative on the weak block chamber and
intertwines the actual upper Jacquet quotient with its unnormalized Levi action.
This is a derived translation of the laws motivating Casselman III.5.1–III.5.3,
using the published weak-chamber factorization predicate. -/
def BlockCompressionStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) (B : GeneralLinear.BlockShape n),
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hρ : IsSmooth ρ)
      (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization_allFieldBZ T K →
        (∀ a b : Fin B.length → F.Carrierˣ,
          B.IsWeaklyContracting_allFieldBZ T a → B.IsWeaklyContracting_allFieldBZ T b →
            compressedAction ρ hρ K hK (B.blockScalar F.Carrier (a * b)) =
              compressedAction ρ hρ K hK (B.blockScalar F.Carrier a) *
                compressedAction ρ hρ K hK (B.blockScalar F.Carrier b)) ∧
        (∀ a : Fin B.length → F.Carrierˣ, B.IsWeaklyContracting_allFieldBZ T a →
          ∀ v : fixedVectors ρ K.toSubgroup,
            mk ρ (B.unipotentSubgroup F.Carrier)
                (compressedAction ρ hρ K hK (B.blockScalar F.Carrier a) v : V) =
              action ρ (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
                (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
                (B.blockScalarInLevi F.Carrier a)
                (mk ρ (B.unipotentSubgroup F.Carrier) (v : V)))

end Langlands.AllFieldBZ.Jacquet
