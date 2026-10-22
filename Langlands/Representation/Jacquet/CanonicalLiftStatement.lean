import Langlands.Representation.Jacquet.CanonicalLiftDefinitions
import Langlands.Group.GL.BlockIwahoriDefinitions

/-!
# Core canonical Jacquet lift statements for actual p-adic block groups

These proposition definitions state the representation-theoretic identification
of the generalized kernel and bijectivity of the actual stable-image quotient.
They contain no proofs of these assertions.
-/

namespace Langlands.Jacquet

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The generalized kernel of normalized compression is exactly the kernel of
 the actual upper Jacquet quotient restricted to the compact fixed vectors. -/
def BlockPowerKernelJacquetClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hAdmissible : IsAdmissible ρ),
    let hρ := hAdmissible.1
    ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization T K →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
        let g := B.blockScalar F.Carrier a
        powerKernelSup ρ hρ K hK g =
          LinearMap.ker (fixedJacquetMap ρ
            (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
            (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier) K.toSubgroup)

/-- The actual Jacquet quotient is bijective from the all-power stable image
 onto its existing fixed-vector codomain for the unnormalized Levi action. -/
def BlockStableImageJacquetBijectiveClause : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hAdmissible : IsAdmissible ρ),
    let hρ := hAdmissible.1
    ∀ (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization T K →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
        let g := B.blockScalar F.Carrier a
        Function.Bijective (stableImageJacquetMap ρ hρ K hK g
          (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
          (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier))

/-- The two core canonical-lift assertions, without compatibility or pairing
 conclusions and without assuming any canonical-lift data. -/
def BlockCanonicalLiftStatement : Prop :=
  BlockPowerKernelJacquetClause F T B V ∧
  BlockStableImageJacquetBijectiveClause F T B V

end Langlands.Jacquet
