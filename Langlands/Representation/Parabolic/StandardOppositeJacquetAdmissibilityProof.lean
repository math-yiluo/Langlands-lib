import Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityStatement
import Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof
import Langlands.Representation.Jacquet.OppositeCanonicalLiftProof

noncomputable section

namespace Langlands.Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The actual unnormalized opposite quotient is admissible on the embedded Levi. -/
theorem isAdmissible_oppositeJacquetAction :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V), IsAdmissible ρ →
      IsAdmissible (Jacquet.action ρ (B.oppositeUnipotentSubgroup F.Carrier)
        (B.leviSubgroup F.Carrier)
        (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)) := by
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.generalLinearTopologicalGroup n
  intro ρ hρ
  let σ := Jacquet.action ρ (B.oppositeUnipotentSubgroup F.Carrier)
    (B.leviSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
  refine ⟨Jacquet.isSmooth_action _ _ _ _ hρ.1, ?_⟩
  intro L
  let e := B.leviEquivContinuous F.Carrier
  let L' := L.comap e.toMonoidHom e.continuous
  obtain ⟨K, hK, hfac, hKL⟩ := exists_iwahori_levi_subset F T B L'
  obtain ⟨a, ha⟩ := B.deepChamberNonempty T 1 zero_lt_one
  have has : B.IsStrictlyContracting T a := ha
  let : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := hρ.2 K
  let J := K.toSubgroup.comap (B.leviSubgroup F.Carrier).subtype
  let f := Jacquet.stableImageJacquetMap ρ hρ.1 K hK (B.blockScalar F.Carrier a)⁻¹
    (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
  have hf : Function.Bijective f :=
    Jacquet.blockOppositeStableImageJacquetMap_bijective F T B V
      ρ hρ K hK hfac a has
  let : FiniteDimensional ℂ (fixedVectors σ J) :=
    Module.Finite.of_surjective f hf.2
  have hJL : J ≤ L.toSubgroup := by
    intro m hm
    have hm' := hKL m hm
    change e (e.symm m) ∈ L at hm'
    change m ∈ L
    rwa [ContinuousMulEquiv.apply_symm_apply] at hm'
  have hfixed : fixedVectors σ L.toSubgroup ≤ fixedVectors σ J := by
    intro v hv m
    exact hv ⟨m.val, hJL m.property⟩
  exact Module.Finite.of_injective (Submodule.inclusion hfixed)
    (Submodule.inclusion_injective hfixed)

/-- The standard opposite normalization and actual product-Levi pullback
preserve the preceding admissibility result. -/
theorem isAdmissible_standardOppositeJacquet :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V), IsAdmissible ρ →
      IsAdmissible (CuspidalJacquetMultiplicity.oppositeJacquet T B (Rep.of ρ)).ρ := by
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  intro ρ hρ
  let e := B.leviEquivContinuous F.Carrier
  let δ := (T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom
  have hδ : IsOpen (δ.ker : Set (B.leviSubgroup F.Carrier)) :=
    (T.isOpen_ker_leviModulus B).preimage e.symm.continuous
  have hδinv : IsOpen (δ⁻¹.ker : Set (B.leviSubgroup F.Carrier)) := by
    have heq : δ⁻¹.ker = δ.ker := by
      ext m
      simp only [MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
    rw [heq]
    exact hδ
  apply isAdmissible_comp_continuousMulEquiv _ e
  apply (isAdmissible_twist_iff _ _
    (Jacquet.isOpen_ker_inverseHalfCharacter δ⁻¹ hδinv)).mpr
  exact isAdmissible_oppositeJacquetAction F T B V ρ hρ

/-- The exact standard GL clause, with independent field and carrier universes. -/
theorem standardOppositeJacquetAdmissibility :
    StandardOppositeJacquetAdmissibilityStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n B V _ _ ρ hρ
  exact isAdmissible_standardOppositeJacquet F T B V ρ hρ

end Langlands.Parabolic
