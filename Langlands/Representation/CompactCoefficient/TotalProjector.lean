import Langlands.Representation.CompactCoefficient.OrthogonalProjectorFamily
import Langlands.Representation.CuspidalSupport.PointwiseProjectorSum
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-!
# Total projectors from finite fixed-level strata

This internal construction retains finite fixed-level strata and the component
projectors as hypotheses. It supplies pointwise finiteness and identifies the
range and kernel of the resulting sum.
-/

noncomputable section

namespace Langlands

section Algebra

variable {R G V ι : Type*} [CommRing R] [Group G]
  [AddCommGroup V] [Module R V] {ρ : Representation R G V}
  (e : ι → ρ.IntertwiningMap ρ)
  (hfinite : ∀ v : V, Function.HasFiniteSupport (fun i => e i v))
  (hid : ∀ i v, e i (e i v) = e i v)
  (horth : ∀ i j, i ≠ j → ∀ v, e i (e j v) = 0)

include hid horth

/-- The range of the total orthogonal projector is the supremum of the
component ranges. -/
theorem pointwiseFiniteSum_range :
    (pointwiseFiniteSum e hfinite).range = ⨆ i, (e i).range := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    change (∑ᶠ i, e i v) ∈ (⨆ i, (e i).range).toSubmodule
    rw [Subrepresentation.toSubmodule_iSup, finsum_eq_sum _ (hfinite v)]
    exact Submodule.sum_mem _ fun i _ => le_iSup (fun i => (e i).range.toSubmodule) i ⟨v, rfl⟩
  · refine iSup_le fun i => ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨e i v, pointwiseFiniteSum_component e hfinite hid horth i v⟩

/-- The kernel of the total orthogonal projector is the infimum of the
component kernels. -/
theorem pointwiseFiniteSum_ker :
    (pointwiseFiniteSum e hfinite).ker = ⨅ i, (e i).ker := by
  apply le_antisymm
  · intro v hv
    rw [Subrepresentation.mem_iInf]
    intro i
    have h := component_pointwiseFiniteSum e hfinite hid horth i v
    change pointwiseFiniteSum e hfinite v = 0 at hv
    rw [hv, map_zero] at h
    exact h.symm
  · intro v hv
    rw [Subrepresentation.mem_iInf] at hv
    change (∑ᶠ i, e i v) = 0
    exact finsum_eq_zero_of_forall_eq_zero fun i => hv i

end Algebra

namespace CompactCoefficientClass

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
  {A : SmoothRep.{0, uG, uW} ℂ G}

/-- Finite fixed-level strata make any family whose kernels contain the
intrinsic annihilators finite on each smooth vector. -/
theorem finiteSupport_of_finite_fixedStratum
    (P : CompactCoefficientClass.{uG, uV} G →
      A.representation.IntertwiningMap A.representation)
    (hker : ∀ c, annihilatorSubrepresentation c A ≤ (P c).ker)
    (hstrata : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      (fixedStratum.{uG, uV} K.toSubgroup).Finite)
    (v : A) : Function.HasFiniteSupport (fun c => P c v) := by
  obtain ⟨L, hv⟩ := A.isSmooth v
  obtain ⟨K, hK, hKL⟩ := compactOpenSubgroupBasis G (L : Set G)
    (L.isOpen.mem_nhds L.one_mem)
  have hvK : v ∈ fixedVectors A.representation K.toSubgroup := by
    change ∀ k : K, A.representation (k : G) v = v
    intro k
    exact hv ⟨k, hKL k.property⟩
  exact finiteSupport_of_finite_stratum P v (fixedStratum K.toSubgroup) (hstrata K hK)
    (fun c hc => apply_eq_zero_of_annihilator_le_ker c K.toSubgroup hc (P c) (hker c) hvK)

/-- Sum supplied compact-isotypic endomorphisms using finite fixed-level strata.
The definition only needs containment of each annihilator in the corresponding
kernel; projector laws are separate hypotheses of the subsequent results. -/
def totalProjectorOfFiniteStrata
    (P : CompactCoefficientClass.{uG, uV} G →
      A.representation.IntertwiningMap A.representation)
    (hker : ∀ c, annihilatorSubrepresentation c A ≤ (P c).ker)
    (hstrata : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
      (fixedStratum.{uG, uV} K.toSubgroup).Finite) :
    A.representation.IntertwiningMap A.representation :=
  pointwiseFiniteSum P (finiteSupport_of_finite_fixedStratum P hker hstrata)

section Laws

variable
  (P : CompactCoefficientClass.{uG, uV} G →
    A.representation.IntertwiningMap A.representation)
  (hker : ∀ c, annihilatorSubrepresentation c A ≤ (P c).ker)
  (hstrata : ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
    (fixedStratum.{uG, uV} K.toSubgroup).Finite)
  (hid : ∀ c v, P c (P c v) = P c v)
  (horth : ∀ c d, c ≠ d → ∀ v, P c (P d v) = 0)

include hid horth

theorem totalProjectorOfFiniteStrata_idempotent (v : A) :
    totalProjectorOfFiniteStrata P hker hstrata
      (totalProjectorOfFiniteStrata P hker hstrata v) =
      totalProjectorOfFiniteStrata P hker hstrata v :=
  pointwiseFiniteSum_idempotent P _ hid horth v

/-- Exact component ranges identify the total range with the intrinsic total
isotypic subrepresentation. -/
theorem totalProjectorOfFiniteStrata_range
    (hrange : ∀ c, (P c).range = isotypicSubrepresentation c A) :
    (totalProjectorOfFiniteStrata P hker hstrata).range =
      totalIsotypicSubrepresentation.{uG, uV} A := by
  rw [totalProjectorOfFiniteStrata, pointwiseFiniteSum_range P _ hid horth]
  exact iSup_congr hrange

/-- Exact component kernels identify the total kernel with the intrinsic total
annihilator subrepresentation. -/
theorem totalProjectorOfFiniteStrata_ker
    (hkerEq : ∀ c, (P c).ker = annihilatorSubrepresentation c A) :
    (totalProjectorOfFiniteStrata P hker hstrata).ker =
      totalAnnihilatorSubrepresentation.{uG, uV} A := by
  rw [totalProjectorOfFiniteStrata, pointwiseFiniteSum_ker P _ hid horth]
  exact iInf_congr hkerEq

end Laws
end CompactCoefficientClass
end Langlands
