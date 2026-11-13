import Langlands.Representation.Jacquet.CanonicalLiftStatement
import Langlands.AllField.Group.GL.BlockIwahoriDefinitions
/-!
# Core canonical Jacquet lift statements for actual local-field block groups

These proposition definitions state the representation-theoretic identification
of the generalized kernel and bijectivity of the actual stable-image quotient.
They contain no proofs of these assertions.
-/

namespace Langlands.AllField.Jacquet
open Langlands.Jacquet hiding BlockStableImageJacquetBijectiveClause
open Langlands.AllField.Jacquet

universe uF uV

variable (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The actual Jacquet quotient is bijective from the all-power stable image
 onto its existing fixed-vector codomain for the unnormalized Levi action. -/
def BlockStableImageJacquetBijectiveClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (ρ : Representation ℂ (GeneralLinear n F) V) (hAdmissible : IsAdmissible ρ),
    let hρ := hAdmissible.1
    ∀ (K : OpenSubgroup (GeneralLinear n F))
      (hK : IsCompact (K : Set (GeneralLinear n F))),
      (Langlands.AllField.GeneralLinear.BlockShape.HasBlockIwahoriFactorization B) T K →
      ∀ a : Fin B.length → Fˣ, (Langlands.AllField.GeneralLinear.BlockShape.IsStrictlyContracting B) T a →
        let g := B.blockScalar F a
        Function.Bijective (stableImageJacquetMap ρ hρ K hK g
          (B.unipotentSubgroup F) (B.leviSubgroup F)
          (B.leviSubgroup_le_normalizer_unipotentSubgroup F))

end Langlands.AllField.Jacquet
