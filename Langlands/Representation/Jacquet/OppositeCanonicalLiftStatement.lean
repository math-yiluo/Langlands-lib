import Langlands.Representation.Jacquet.CanonicalLiftDefinitions
import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.Group.GL.OppositeBlocks

/-!
# Core opposite-radical canonical Jacquet lift statements

These proposition definitions mirror `CanonicalLiftStatement` for the actual
opposite radical of a block shape, compressed by the inverse block scalar of
the same strictly contracting tuple. They contain no proofs of these assertions.
-/

namespace Langlands.Jacquet

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The generalized kernel of normalized compression by the inverse block
 scalar is exactly the kernel of the actual opposite Jacquet quotient restricted
 to the compact fixed vectors. -/
def BlockOppositePowerKernelJacquetClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hAdmissible : IsAdmissible ρ),
    let hρ := hAdmissible.1
    ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization T K →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
        let g := (B.blockScalar F.Carrier a)⁻¹
        powerKernelSup ρ hρ K hK g =
          LinearMap.ker (fixedJacquetMap ρ
            (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
            (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
            K.toSubgroup)

/-- The actual opposite Jacquet quotient is bijective from the all-power stable
 image of the inverse-scalar compression onto its existing fixed-vector codomain
 for the unnormalized Levi action. -/
def BlockOppositeStableImageJacquetBijectiveClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hAdmissible : IsAdmissible ρ),
    let hρ := hAdmissible.1
    ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization T K →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
        let g := (B.blockScalar F.Carrier a)⁻¹
        Function.Bijective (stableImageJacquetMap ρ hρ K hK g
          (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
          (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier))

/-- The two core opposite canonical-lift assertions, without compatibility or
 pairing conclusions and without assuming any canonical-lift data. -/
def BlockOppositeCanonicalLiftStatement : Prop :=
  BlockOppositePowerKernelJacquetClause F T B V ∧
  BlockOppositeStableImageJacquetBijectiveClause F T B V

end Langlands.Jacquet
