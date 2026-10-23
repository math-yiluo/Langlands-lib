import Langlands.Representation.Smooth.FixedVectors.FiniteTypesStatement
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Langlands.Representation.Smooth.FixedVectors.OrderProof
import Langlands.Representation.Smooth.FixedVectors.LawsProof
import Mathlib.RepresentationTheory.Subrepresentation

noncomputable section

open Topology

namespace Langlands

universe uR uG uV uW uI

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- Restricting the acting group preserves the fixed-vector submodule when the
fixing subgroup lies in the restricted group. -/
theorem fixedVectors_comp_subtype (ρ : Representation R G V)
    (H K : Subgroup G) (hKH : K ≤ H) :
    fixedVectors (ρ.comp H.subtype) (K.comap H.subtype) = fixedVectors ρ K := by
  ext v
  constructor
  · intro hv
    change ∀ k : K, ρ (k : G) v = v
    intro k
    exact hv ⟨⟨k, hKH k.property⟩, k.property⟩
  · intro hv
    change ∀ k : K.comap H.subtype, ρ (k : G) v = v
    intro k
    exact hv ⟨k, k.property⟩

variable [TopologicalSpace G] [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]

/-- A finite family of smooth vectors has a common compact open stabilizer in
any prescribed identity neighborhood. -/
theorem exists_compactOpen_fixing_finite {ι : Type uI} [Finite ι]
    (ρ : Representation R G V) (hρ : IsSmooth ρ) (v : ι → V)
    (U : Set G) (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U ∧
      ∀ i, v i ∈ fixedVectors ρ K.toSubgroup := by
  classical
  choose L hL using fun i => hρ (v i)
  have hN : (U ∩ ⋂ i, (L i : Set G)) ∈ 𝓝 (1 : G) :=
    Filter.inter_mem hU (Filter.iInter_mem.mpr fun i => (L i).mem_nhds_one)
  obtain ⟨K, hK, hKN⟩ := compactOpenSubgroupBasis G _ hN
  refine ⟨K, hK, fun g hg => (hKN hg).1, fun i => ?_⟩
  apply fixedVectors_antitone ρ (show K.toSubgroup ≤ (L i).toSubgroup from ?_) (hL i)
  intro g hg
  exact Set.mem_iInter.mp (hKN hg).2 i

/-- A finite family of nonzero subrepresentations of the restriction to an open
subgroup has nonzero fixed vectors for one ambient compact open subgroup. -/
theorem exists_compactOpen_fixed_finite_types {ι : Type uI} [Finite ι]
    (ρ : Representation R G V) (hρ : IsSmooth ρ) (H : OpenSubgroup G)
    (T : ι → Subrepresentation (ρ.comp H.toSubgroup.subtype))
    (hT : ∀ i, T i ≠ ⊥) (U : Set G) (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U ∧
      K.toSubgroup ≤ H.toSubgroup ∧
      ∀ i, ∃ v : (T i).toSubmodule, v ∈ fixedVectors (T i).toRepresentation
        (K.toSubgroup.comap H.toSubgroup.subtype) ∧ v ≠ 0 := by
  classical
  have hnonzero : ∀ i, ∃ v : V, v ∈ T i ∧ v ≠ 0 := by
    intro i
    apply (Submodule.ne_bot_iff (T i).toSubmodule).mp
    intro heq
    exact hT i (Subrepresentation.toSubmodule_injective heq)
  choose v hvT hv using hnonzero
  obtain ⟨K, hK, hKU, hvK⟩ := exists_compactOpen_fixing_finite ρ hρ v
    (U ∩ (H : Set G)) (Filter.inter_mem hU H.mem_nhds_one)
  refine ⟨K, hK, fun g hg => (hKU hg).1, fun g hg => (hKU hg).2, ?_⟩
  intro i
  refine ⟨⟨v i, hvT i⟩, ?_, fun heq => hv i (congrArg Subtype.val heq)⟩
  change ∀ k : K.toSubgroup.comap H.toSubgroup.subtype,
    (T i).toRepresentation k ⟨v i, hvT i⟩ = ⟨v i, hvT i⟩
  intro k
  apply Subtype.ext
  exact hvK i ⟨k, k.property⟩

omit [TopologicalSpace G] [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G] in
/-- Actual equivalences transport the chosen nonzero fixed vectors from the
finite type family to every simple subrepresentation of a second restriction. -/
theorem fixedVectors_meet_atoms_of_types {ι : Type uI}
    (ρ : Representation R G V) (σ : Representation R G W) (H K : Subgroup G)
    (hKH : K ≤ H) (T : ι → Subrepresentation (ρ.comp H.subtype))
    (hT : ∀ i, ∃ v : (T i).toSubmodule,
      v ∈ fixedVectors (T i).toRepresentation (K.comap H.subtype) ∧ v ≠ 0)
    (htypes : ∀ S : Subrepresentation (σ.comp H.subtype), IsAtom S →
      ∃ i, Nonempty ((T i).toRepresentation.Equiv S.toRepresentation)) :
    ∀ S : Subrepresentation (σ.comp H.subtype), IsAtom S →
      ∃ w : W, w ∈ S ∧ w ∈ fixedVectors σ K ∧ w ≠ 0 := by
  intro S hS
  obtain ⟨i, ⟨e⟩⟩ := htypes S hS
  obtain ⟨v, hvK, hv⟩ := hT i
  have heK := map_mem_fixedVectors e.toIntertwiningMap hvK
  refine ⟨(e v : W), (e v).property, ?_, ?_⟩
  · rw [← fixedVectors_comp_subtype σ H K hKH]
    change ∀ k : K.comap H.subtype, σ (k : G) (e v : W) = (e v : W)
    intro k
    exact congrArg Subtype.val (heK k)
  · intro heq
    apply hv
    apply e.toLinearEquiv.injective
    change e v = e 0
    simpa only [map_zero] using (Subtype.ext heq : e v = 0)

/-- The full finite-type compact-open choice, with the second representation
quantified after the fixing subgroup has been chosen. -/
theorem finiteTypeCompactOpenDetection :
    FiniteTypeCompactOpenDetectionStatement.{uR, uG, uV, uW, uI} := by
  intro R _ G _ _ _ _ V _ _ ρ hρ H ι _ T hT U hU
  obtain ⟨K, hK, hKU, hKH, hTK⟩ :=
    exists_compactOpen_fixed_finite_types ρ hρ H T hT U hU
  refine ⟨K, hK, hKU, hKH, hTK, ?_⟩
  intro W _ _ σ htypes
  exact fixedVectors_meet_atoms_of_types ρ σ H.toSubgroup K.toSubgroup hKH T hTK htypes

end Langlands
