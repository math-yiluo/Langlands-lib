import Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof
import Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftProof
import Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof

noncomputable section
open Filter Topology

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- Admissibility on the actual refined Levi follows from product canonical lifts. -/
theorem isAdmissible_refinedOppositeJacquetAction :
    letI := T.topology
    ∀ (ρ : Representation ℂ (B.Levi F.Carrier) V), IsAdmissible ρ →
      IsAdmissible (refinedOppositeJacquetAction B S ρ) := by
  classical
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.leviTopologicalGroup B
  intro ρ hρ
  refine ⟨isSmooth_refinedOppositeJacquetAction B S hρ.1, ?_⟩
  intro L
  have hL : (L : Set (refinedLevi F.Carrier B S)) ∈
      𝓝 (1 : refinedLevi F.Carrier B S) := L.mem_nhds_one
  rw [nhds_subtype_eq_comap] at hL
  obtain ⟨U, hU, hUL⟩ := mem_comap.mp hL
  obtain ⟨K, hK, hfac, hKU⟩ :=
    CuspidalSupport.exists_leviPiOpenSubgroup_subset T B S hU
  choose a ha using fun i => (S i).deepChamberNonempty T 1 zero_lt_one
  have has : ∀ i, (S i).IsStrictlyContracting T (a i) := ha
  let KP := CuspidalSupport.leviPiOpenSubgroup T B K
  let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK
  let N := refinedOppositeUnipotent F.Carrier B S
  let M := refinedLevi F.Carrier B S
  have hMN : M ≤ Subgroup.normalizer (N : Set (B.Levi F.Carrier)) :=
    fun m hm => (refinedOppositeLeviNormalizer F.Carrier B S ⟨m, hm⟩).property
  let σ := Jacquet.action ρ N M hMN
  let J := KP.toSubgroup.comap M.subtype
  let g : B.Levi F.Carrier := fun i => ((S i).blockScalar F.Carrier (a i))⁻¹
  let : FiniteDimensional ℂ (fixedVectors ρ KP.toSubgroup) := hρ.2 KP
  let f := Jacquet.stableImageJacquetMap ρ hρ.1 KP hKP g N M hMN
  have hf : Function.Bijective f :=
    Jacquet.refinedOppositeStableImageJacquetBijective F T B S V ρ hρ K hK hfac a has
  let : FiniteDimensional ℂ (fixedVectors σ J) :=
    Module.Finite.of_surjective f hf.2
  have hJL : J ≤ L.toSubgroup := by
    intro m hm
    exact hUL (hKU hm)
  have hfixed : fixedVectors (refinedOppositeJacquetAction B S ρ) L.toSubgroup ≤
      fixedVectors σ J := by
    intro v hv m
    exact hv ⟨m.val, hJL m.property⟩
  exact Module.Finite.of_injective (Submodule.inclusion hfixed)
    (Submodule.inclusion_injective hfixed)

/-- The exact positive upper half-modulus twist preserves admissibility. -/
theorem isAdmissible_normalizedRefinedOppositeJacquet :
    letI := T.topology
    ∀ (ρ : Representation ℂ (B.Levi F.Carrier) V), IsAdmissible ρ →
      IsAdmissible (T.normalizedRefinedOppositeJacquet B S ρ) := by
  let := T.topology
  intro ρ hρ
  apply (isAdmissible_twist_iff _ _
    (Jacquet.isOpen_ker_inverseHalfCharacter _
      (T.isOpen_ker_refinedOppositeLeviModulus B S))).mpr
  exact isAdmissible_refinedOppositeJacquetAction F T B S V ρ hρ

/-- Admissibility transports through the actual normalized opposite transitivity map. -/
theorem isAdmissible_normalizedComposedOppositeJacquet :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) V), IsAdmissible ρ →
      IsAdmissible (T.normalizedComposedOppositeJacquet B S ρ) := by
  let := T.topology
  intro ρ hρ
  obtain ⟨E, -⟩ := normalizedOppositeRefinementTransitivity p F T n B S (Rep.of ρ)
  apply isAdmissible_of_equiv E
  exact isAdmissible_normalizedRefinedOppositeJacquet F T B S _ _
    (isAdmissible_standardOppositeJacquet F T B V ρ hρ)

/-- Closed refined opposite admissibility with independent field/carrier universes. -/
theorem refinedOppositeJacquetAdmissibility :
    RefinedOppositeJacquetAdmissibilityStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n B S V _ _ ρ hρ
  exact isAdmissible_normalizedRefinedOppositeJacquet F T B S V ρ hρ

/-- Closed composed opposite admissibility. -/
theorem composedOppositeJacquetAdmissibility :
    ComposedOppositeJacquetAdmissibilityStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n B S V _ _ ρ hρ
  exact isAdmissible_normalizedComposedOppositeJacquet F T B S V ρ hρ

/-- Pullback to the actual flattened product coordinates preserves admissibility. -/
theorem flattenedRefinedOppositeJacquetAdmissibility :
    FlattenedRefinedOppositeJacquetAdmissibilityStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  intro n B S V _ _ ρ hρ
  exact isAdmissible_comp_continuousMulEquiv _
    (flattenedLeviEquivContinuous F.Carrier B S)
    (isAdmissible_normalizedRefinedOppositeJacquet F T B S V ρ hρ)

/-- The composed quotient has the same admissibility in flattened coordinates. -/
theorem flattenedComposedOppositeJacquetAdmissibility :
    FlattenedComposedOppositeJacquetAdmissibilityStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  intro n B S V _ _ ρ hρ
  exact isAdmissible_comp_continuousMulEquiv _
    (flattenedLeviEquivContinuous F.Carrier B S)
    (isAdmissible_normalizedComposedOppositeJacquet F T B S V ρ hρ)

/-- The complete five-clause family for the actual normalized opposite quotients. -/
theorem normalizedOppositeJacquetAdmissibility :
    NormalizedOppositeJacquetAdmissibilityStatement.{uF, uV} :=
  ⟨standardOppositeJacquetAdmissibility, refinedOppositeJacquetAdmissibility,
    composedOppositeJacquetAdmissibility, flattenedRefinedOppositeJacquetAdmissibility,
    flattenedComposedOppositeJacquetAdmissibility⟩

end Langlands.Parabolic
