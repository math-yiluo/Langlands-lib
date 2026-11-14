import Langlands.AllFieldBZ.Group.GL.InverseTransposeIwahoriProof
import Langlands.AllFieldBZ.Representation.Jacquet.CanonicalLiftBijectivityProof
import Langlands.AllFieldBZ.Representation.Jacquet.OppositeCanonicalLiftStatement
import Langlands.Representation.Jacquet.OppositeCanonicalLiftProof

/-!
# All-field port of `Langlands.Representation.Jacquet.OppositeCanonicalLiftProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Jacquet.OppositeCanonicalLiftProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Jacquet
open Langlands.Jacquet hiding BlockCompressionStatement BlockOppositePowerKernelJacquetClause BlockOppositeStableImageJacquetBijectiveClause BlockPowerKernelJacquetClause BlockStableImageJacquetBijectiveClause blockCompressedAction_mk blockCompressedAction_mul blockCompression blockOppositePowerKernelJacquet blockOppositeStableImageJacquetBijective blockPowerKernelJacquet blockPowerKernel_eq_jacquetKernel blockScalar_mul_eq_of_mem_leviSubgroup blockStableImageJacquetBijective exists_blockScalar_pow_iwahoriLower_fixed stableImageJacquetMap_bijective_of_finiteDimensional
universe uF uV

variable (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The exact opposite generalized-kernel clause, by inverse-transpose transport. -/
theorem blockOppositePowerKernelJacquet : BlockOppositePowerKernelJacquetClause F T B V := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hAdmissible
  dsimp only
  intro K hK hfac a ha
  let e := T.generalLinearInverseTranspose n
  let K' := K.comap e.toMonoidHom e.continuous
  have hK' : IsCompact (K' : Set (GeneralLinear n F.Carrier)) :=
    Langlands.GeneralLinear.BlockShape.inverseTranspose_compact_comap_allFieldBZ T n K hK
  have hfac' : B.HasBlockIwahoriFactorization_allFieldBZ T K' :=
    Langlands.GeneralLinear.BlockShape.inverseTranspose_iwahoriFactorization_allFieldBZ T B K hfac
  have hmap : K'.toSubgroup.map e.toMonoidHom = K.toSubgroup :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective K.toSubgroup
  have hAdmissible' := isAdmissible_comp_continuousMulEquiv ρ e hAdmissible
  have hupper := blockPowerKernelJacquet F T B V
    (ρ.comp e.toMonoidHom) hAdmissible' K' hK' hfac' a ha
  have htransport := powerKernelSup_eq_ker_groupTransport e ρ hAdmissible.1
    K' hK' K hK hmap
    (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
    (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
    (B.inverseTranspose_unipotent_map F.Carrier)
    (B.inverseTranspose_levi_map F.Carrier) (B.blockScalar F.Carrier a)
  have hg : e (B.blockScalar F.Carrier a) = (B.blockScalar F.Carrier a)⁻¹ :=
    B.inverseTranspose_blockScalar F.Carrier a
  have hout := htransport.mp hupper
  rw [hg] at hout
  exact hout

/-- The exact opposite stable-image quotient bijectivity clause. -/
theorem blockOppositeStableImageJacquetBijective : BlockOppositeStableImageJacquetBijectiveClause F T B V := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro ρ hAdmissible
  dsimp only
  intro K hK hfac a ha
  let e := T.generalLinearInverseTranspose n
  let K' := K.comap e.toMonoidHom e.continuous
  have hK' : IsCompact (K' : Set (GeneralLinear n F.Carrier)) :=
    Langlands.GeneralLinear.BlockShape.inverseTranspose_compact_comap_allFieldBZ T n K hK
  have hfac' : B.HasBlockIwahoriFactorization_allFieldBZ T K' :=
    Langlands.GeneralLinear.BlockShape.inverseTranspose_iwahoriFactorization_allFieldBZ T B K hfac
  have hmap : K'.toSubgroup.map e.toMonoidHom = K.toSubgroup :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective K.toSubgroup
  have hAdmissible' := isAdmissible_comp_continuousMulEquiv ρ e hAdmissible
  have hupper := blockStableImageJacquetBijective F T B V
    (ρ.comp e.toMonoidHom) hAdmissible' K' hK' hfac' a ha
  have htransport := stableImageJacquetMap_bijective_groupTransport e ρ hAdmissible.1
    K' hK' K hK hmap
    (B.unipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
    (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
    (B.inverseTranspose_unipotent_map F.Carrier)
    (B.inverseTranspose_levi_map F.Carrier) (B.blockScalar F.Carrier a)
  have hg : e (B.blockScalar F.Carrier a) = (B.blockScalar F.Carrier a)⁻¹ :=
    B.inverseTranspose_blockScalar F.Carrier a
  have hout := htransport.mp hupper
  rw [hg] at hout
  exact hout

end Langlands.AllFieldBZ.Jacquet
