import Langlands.Representation.Jacquet.OppositeCanonicalLiftStatement
import Langlands.Representation.Jacquet.CanonicalLiftBijectivityProof
import Langlands.Representation.Jacquet.CanonicalLiftGroupTransportProof
import Langlands.Group.GL.InverseTransposeIwahoriProof

/-! # Core opposite-radical canonical Jacquet lifts -/

namespace Langlands.Jacquet

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
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
    GeneralLinear.BlockShape.inverseTranspose_compact_comap T n K hK
  have hfac' : B.HasBlockIwahoriFactorization T K' :=
    GeneralLinear.BlockShape.inverseTranspose_iwahoriFactorization T B K hfac
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
    GeneralLinear.BlockShape.inverseTranspose_compact_comap T n K hK
  have hfac' : B.HasBlockIwahoriFactorization T K' :=
    GeneralLinear.BlockShape.inverseTranspose_iwahoriFactorization T B K hfac
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

/-- Pointwise bijectivity for the actual opposite Jacquet quotient at the
inverse block scalar of the original upper strictly contracting tuple. -/
theorem blockOppositeStableImageJacquetMap_bijective :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (hAdmissible : IsAdmissible ρ)
      (K : OpenSubgroup (GeneralLinear n F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear n F.Carrier))),
      B.HasBlockIwahoriFactorization T K →
      ∀ a : Fin B.length → F.Carrierˣ, B.IsStrictlyContracting T a →
        Function.Bijective (stableImageJacquetMap ρ hAdmissible.1 K hK
          (B.blockScalar F.Carrier a)⁻¹
          (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
          (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)) :=
  blockOppositeStableImageJacquetBijective F T B V

/-- Both core opposite canonical-lift assertions, with the exact published telescope. -/
theorem blockOppositeCanonicalLift : BlockOppositeCanonicalLiftStatement F T B V :=
  ⟨blockOppositePowerKernelJacquet F T B V,
    blockOppositeStableImageJacquetBijective F T B V⟩

end Langlands.Jacquet
