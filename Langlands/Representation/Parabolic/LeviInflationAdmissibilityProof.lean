import Langlands.Representation.Parabolic.AdmissibilityStatement
import Langlands.Representation.Smooth.Transfer.PullbackProof

namespace Langlands

universe uR uG uH uF uV

section Transport

variable {R : Type uR} {G : Type uG} {H : Type uH} {V : Type uV}
    [CommRing R] [Group G] [Group H] [AddCommGroup V] [Module R V]

/-- Fixed vectors of a pullback are the fixed vectors of the image subgroup. -/
theorem fixedVectors_comp_eq_map (ρ : Representation R G V) (q : H →* G)
    (K : Subgroup H) : fixedVectors (ρ.comp q) K = fixedVectors ρ (K.map q) := by
  ext v
  change (∀ k : K, ρ (q k.val) v = v) ↔
    (∀ g : K.map q, ρ g.val v = v)
  constructor
  · intro hv g
    obtain ⟨k, hk, hkg⟩ := g.property
    rw [← hkg]
    exact hv ⟨k, hk⟩
  · intro hv k
    exact hv ⟨q k.val, Subgroup.mem_map_of_mem q k.property⟩

/-- A continuous open surjective homomorphism preserves and reflects
admissibility under pullback, for the all-open-subgroups convention. -/
theorem isAdmissible_comp_iff_of_open_surjective
    [TopologicalSpace G] [TopologicalSpace H]
    (ρ : Representation R G V) (q : H →* G)
    (hcontinuous : Continuous q) (hopen : IsOpenMap q)
    (hsurjective : Function.Surjective q) :
    IsAdmissible (ρ.comp q) ↔ IsAdmissible ρ := by
  have hfixed (K : OpenSubgroup G) :
      fixedVectors (ρ.comp q) (K.comap q hcontinuous).toSubgroup =
        fixedVectors ρ K.toSubgroup := by
    rw [OpenSubgroup.toSubgroup_comap, fixedVectors_comp_eq_map,
      Subgroup.map_comap_eq_self_of_surjective hsurjective]
  constructor
  · intro hρ
    constructor
    · intro v
      obtain ⟨K, hK⟩ := hρ.1 v
      let L : OpenSubgroup G := ⟨K.toSubgroup.map q, hopen _ K.isOpen⟩
      refine ⟨L, ?_⟩
      exact (fixedVectors_comp_eq_map ρ q K.toSubgroup) ▸ hK
    · intro K
      rw [← hfixed K]
      exact hρ.2 (K.comap q hcontinuous)
  · intro hρ
    refine ⟨isSmooth_comp q hcontinuous hρ.1, ?_⟩
    intro K
    let L : OpenSubgroup G := ⟨K.toSubgroup.map q, hopen _ K.isOpen⟩
    rw [fixedVectors_comp_eq_map]
    exact hρ.2 L

end Transport

namespace Parabolic

/-- Admissibility is preserved and reflected by actual Levi inflation. -/
theorem leviInflationAdmissibility
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    LeviInflationAdmissibilityClause F T B V := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro σ
  apply isAdmissible_comp_iff_of_open_surjective σ (B.leviProjection F.Carrier)
  · exact (B.leviProjectionContinuous F.Carrier).continuous
  · exact isOpenMap_snd.comp (B.decompositionHomeomorph F.Carrier).isOpenMap
  · intro m
    exact ⟨B.leviInParabolic F.Carrier m, B.leviProjection_section F.Carrier m⟩

end Parabolic

end Langlands
