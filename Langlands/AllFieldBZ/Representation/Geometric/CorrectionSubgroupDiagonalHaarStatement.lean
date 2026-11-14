import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Group.GL.NormalizedCharacter
import Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarStatement

/-!
# All-field port of `Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
open scoped BigOperators
open scoped NNReal
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement
universe uF

/-- The actual Haar modulus of diagonal conjugation on `U ∩ g⁻¹ Q g` is the
product of residue-normalized absolute values of its allowed roots.
This internal, derived proposition is a statement, not a proof. -/
def CorrectionSubgroupDiagonalHaarStatement : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ) (B C : GeneralLinear.BlockShape n)
    (w : Equiv.Perm (Fin n)),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    let g := GeneralLinear.permutation n F.Carrier w
    let H := intersectionSource
      (B.unipotentSubgroup F.Carrier) (C.parabolic F.Carrier) g
    let hH := General.isClosed_correctionSubgroup
      (B.unipotentSubgroup F.Carrier) (C.parabolic F.Carrier) g
      (B.isClosed_unipotentSubgroup F.Carrier) (C.isClosed_parabolic F.Carrier)
    let A := {ab : Fin n × Fin n //
      blockIndex B ab.1 < blockIndex B ab.2 ∧
        blockIndex C (w ab.1) ≤ blockIndex C (w ab.2)}
    ∀ (t : Fin n → F.Carrierˣ)
      (d : Subgroup.normalizer (H : Set (GeneralLinear n F.Carrier))),
      (d.val : Matrix (Fin n) (Fin n) F.Carrier) =
          Matrix.diagonal (fun i => (t i : F.Carrier)) →
        HaarModulus.closedNormalizerCharacter H hH d =
          ∏ ab : A, T.normalizedAbsUnits (t ab.1.1) / T.normalizedAbsUnits (t ab.1.2)

end Langlands.AllFieldBZ.Geometric
