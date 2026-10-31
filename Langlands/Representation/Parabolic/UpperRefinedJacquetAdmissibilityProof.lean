import Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityProof
import Langlands.Representation.Jacquet.RefinedUpperCanonicalLiftProof
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Parabolic.UpperRefinedJacquetAdmissibilityStatement

/-!
# Admissibility of upper refined Jacquet modules of product Levis

The upper counterpart of `Parabolic.isAdmissible_refinedOppositeJacquetAction`,
obtained from the published upper product canonical lifts
`Jacquet.refinedStableImageJacquetBijective`. It proves
`UpperRefinedJacquetAdmissibilityStatement`.
-/

noncomputable section
open Filter Topology

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- Admissibility of the unnormalized upper refined Jacquet action. -/
theorem isAdmissible_refinedJacquetAction :
    letI := T.topology
    ∀ (ρ : Representation ℂ (B.Levi F.Carrier) V), IsAdmissible ρ →
      IsAdmissible (Jacquet.action ρ (refinedUnipotent F.Carrier B S)
        (refinedLevi F.Carrier B S) (refinedLevi_le_normalizer B S)) := by
  classical
  let := T.topology
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier :=
    IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  let := T.leviTopologicalGroup B
  intro ρ hρ
  refine ⟨Jacquet.isSmooth_action ρ _ _ _ hρ.1, ?_⟩
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
  let N := refinedUnipotent F.Carrier B S
  let M := refinedLevi F.Carrier B S
  have hMN : M ≤ Subgroup.normalizer (N : Set (B.Levi F.Carrier)) :=
    fun m hm => (refinedLeviNormalizer F.Carrier B S ⟨m, hm⟩).property
  let σ := Jacquet.action ρ N M hMN
  let J := KP.toSubgroup.comap M.subtype
  let g : B.Levi F.Carrier := fun i => (S i).blockScalar F.Carrier (a i)
  let : FiniteDimensional ℂ (fixedVectors ρ KP.toSubgroup) := hρ.2 KP
  let f := Jacquet.stableImageJacquetMap ρ hρ.1 KP hKP g N M hMN
  have hf : Function.Bijective f :=
    Jacquet.refinedStableImageJacquetBijective F T B S V ρ hρ K hK hfac a has
  let : FiniteDimensional ℂ (fixedVectors σ J) :=
    Module.Finite.of_surjective f hf.2
  have hJL : J ≤ L.toSubgroup := by
    intro m hm
    exact hUL (hKU hm)
  have hfixed : fixedVectors (Jacquet.action ρ (refinedUnipotent F.Carrier B S)
      (refinedLevi F.Carrier B S) (refinedLevi_le_normalizer B S)) L.toSubgroup ≤
      fixedVectors σ J := by
    intro v hv m
    exact hv ⟨m.val, hJL m.property⟩
  exact Module.Finite.of_injective (Submodule.inclusion hfixed)
    (Submodule.inclusion_injective hfixed)

/-- The actual normalized upper refined Jacquet module of an admissible
product-Levi representation is admissible. -/
theorem isAdmissible_normalizedRefinedJacquet :
    letI := T.topology
    ∀ (ρ : Representation ℂ (B.Levi F.Carrier) V), IsAdmissible ρ →
      IsAdmissible (T.normalizedRefinedJacquet B S ρ) := by
  let := T.topology
  intro ρ hρ
  apply (isAdmissible_twist_iff _ _
    (Jacquet.isOpen_ker_inverseHalfCharacter _
      (T.isOpen_ker_refinedLeviModulus B S))).mpr
  exact isAdmissible_refinedJacquetAction F T B S V ρ hρ

/-- Proof of `UpperRefinedJacquetAdmissibilityStatement`. -/
theorem upperRefinedJacquetAdmissibility :
    UpperRefinedJacquetAdmissibilityStatement.{uF, uV} :=
  fun _ _ F T _ B S V _ _ ρ hρ => isAdmissible_normalizedRefinedJacquet F T B S V ρ hρ

end Langlands.Parabolic
