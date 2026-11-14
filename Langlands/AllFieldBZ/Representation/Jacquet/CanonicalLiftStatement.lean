import Langlands.AllFieldBZ.Group.GL.BlockIwahoriDefinitions
import Langlands.Representation.Jacquet.CanonicalLiftStatement

/-!
# All-field port of `Langlands.Representation.Jacquet.CanonicalLiftStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Jacquet.CanonicalLiftStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Jacquet
open Langlands.Jacquet hiding BlockPowerKernelJacquetClause BlockStableImageJacquetBijectiveClause
universe uF uV

variable (F : LocalFieldPackage.{uF})
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
      B.HasBlockIwahoriFactorization_allFieldBZ T K →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting_allFieldBZ T a →
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
      B.HasBlockIwahoriFactorization_allFieldBZ T K →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting_allFieldBZ T a →
        let g := B.blockScalar F.Carrier a
        Function.Bijective (stableImageJacquetMap ρ hρ K hK g
          (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
          (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier))

end Langlands.AllFieldBZ.Jacquet
