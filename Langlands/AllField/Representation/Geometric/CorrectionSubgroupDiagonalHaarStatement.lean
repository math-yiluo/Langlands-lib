import Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarStatement
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
/-! The actual diagonal Haar modulus on full GL correction subgroups. -/

open scoped BigOperators NNReal

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement
open Langlands.AllField.Geometric

universe uF

/-- The actual Haar modulus of diagonal conjugation on `U ∩ g⁻¹ Q g` is the
product of residue-normalized absolute values of its allowed roots.
This internal, derived proposition is a statement, not a proof. -/
def CorrectionSubgroupDiagonalHaarStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) (B C : GeneralLinear.BlockShape n)
    (w : Equiv.Perm (Fin n)),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.generalLinearLocallyCompactSpace n
    let g := GeneralLinear.permutation n F w
    let H := intersectionSource
      (B.unipotentSubgroup F) (C.parabolic F) g
    let hH := General.isClosed_correctionSubgroup
      (B.unipotentSubgroup F) (C.parabolic F) g
      (B.isClosed_unipotentSubgroup F) (C.isClosed_parabolic F)
    let A := {ab : Fin n × Fin n //
      blockIndex B ab.1 < blockIndex B ab.2 ∧
        blockIndex C (w ab.1) ≤ blockIndex C (w ab.2)}
    ∀ (t : Fin n → Fˣ)
      (d : Subgroup.normalizer (H : Set (GeneralLinear n F))),
      (d.val : Matrix (Fin n) (Fin n) F) =
          Matrix.diagonal (fun i => (t i : F)) →
        HaarModulus.closedNormalizerCharacter H hH d =
          ∏ ab : A, T.normalizedAbsUnits (t ab.1.1) / T.normalizedAbsUnits (t ab.1.2)

end Langlands.AllField.Geometric
