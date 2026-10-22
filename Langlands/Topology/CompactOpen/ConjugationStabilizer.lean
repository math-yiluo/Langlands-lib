import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact
import Mathlib.GroupTheory.Subgroup.Centralizer

universe u

namespace Langlands

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private def normalizerStabilizerSubgroup (U : Subgroup G) (K : OpenSubgroup U) :
    Subgroup (Subgroup.normalizer (U : Set G)) :=
  (Subgroup.normalizer (K.toSubgroup.map U.subtype : Set G)).comap
    (Subgroup.normalizer (U : Set G)).subtype

omit [IsTopologicalGroup G] in
private theorem mem_normalizerStabilizerSubgroup_iff (U : Subgroup G)
    (K : OpenSubgroup U) (g : Subgroup.normalizer (U : Set G)) :
    g ∈ normalizerStabilizerSubgroup U K ↔ ∀ u : U, u ∈ K ↔ g • u ∈ K := by
  change (g : G) ∈ (Subgroup.normalizer (K.toSubgroup.map U.subtype : Set G)) ↔ _
  constructor
  · intro hg u
    have hm (v : U) : (v : G) ∈ K.toSubgroup.map U.subtype ↔ v ∈ K := by
      simp only [Subgroup.mem_map, Subgroup.subtype_apply, Subtype.val_inj, exists_eq_right]
      rfl
    exact (hm u).symm.trans ((hg (u : G)).trans (hm (g • u)))
  · intro hg x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨g • u, (hg u).mp hu, rfl⟩
    · rintro ⟨u, hu, he⟩
      have hmem : g⁻¹ • u ∈ K := (hg (g⁻¹ • u)).mpr (by simpa using hu)
      refine ⟨g⁻¹ • u, hmem, ?_⟩
      change (g : G)⁻¹ * (u : G) * ((g : G)⁻¹)⁻¹ = x
      change (u : G) = (g : G) * x * (g : G)⁻¹ at he
      rw [he]
      simp [mul_assoc]

private theorem normalizerStabilizerSubgroup_isOpen (U : Subgroup G)
    (K : OpenSubgroup U) (hK : IsCompact (K : Set U)) :
    IsOpen (normalizerStabilizerSubgroup U K : Set (Subgroup.normalizer (U : Set G))) := by
  have hc : Continuous (fun p : (Subgroup.normalizer (U : Set G)) × U => p.1 • p.2) := by
    apply Continuous.subtype_mk
    exact ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul
        (continuous_subtype_val.comp continuous_fst).inv
  have hopen : IsOpen {p : (Subgroup.normalizer (U : Set G)) × U | p.1 • p.2 ∈ K} :=
    K.isOpen.preimage hc
  have hprod : ({1} : Set (Subgroup.normalizer (U : Set G))) ×ˢ (K : Set U) ⊆
      {p : (Subgroup.normalizer (U : Set G)) × U | p.1 • p.2 ∈ K} := by
    rintro ⟨g, u⟩ ⟨rfl, hu⟩
    simpa using hu
  obtain ⟨V, W, hV, _, h1V, hKW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton hK hopen hprod
  have h1 : (1 : Subgroup.normalizer (U : Set G)) ∈ V := h1V (Set.mem_singleton 1)
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  refine Filter.mem_of_superset
    ((hV.inter (hV.preimage continuous_inv)).mem_nhds (by simpa using And.intro h1 h1)) ?_
  intro g hg
  apply (mem_normalizerStabilizerSubgroup_iff U K g).mpr
  intro u
  constructor
  · intro hu
    exact hVW (a := (g, u)) ⟨hg.1, hKW hu⟩
  · intro hu
    have hinv := hVW (a := (g⁻¹, g • u)) ⟨hg.2, hKW hu⟩
    simpa using hinv

/-- The open subgroup of the actual normalizer of `U` preserving the compact open subgroup `K`. -/
def compactOpenNormalizerStabilizer (U : Subgroup G) (K : OpenSubgroup U)
    (hK : IsCompact (K : Set U)) : OpenSubgroup (Subgroup.normalizer (U : Set G)) where
  toSubgroup := normalizerStabilizerSubgroup U K
  isOpen' := normalizerStabilizerSubgroup_isOpen U K hK

/-- Membership means equality of the ambient image of `K` with its conjugate. -/
theorem mem_compactOpenNormalizerStabilizer_iff (U : Subgroup G) (K : OpenSubgroup U)
    (hK : IsCompact (K : Set U)) (g : Subgroup.normalizer (U : Set G)) :
    g ∈ compactOpenNormalizerStabilizer U K hK ↔
      (K.toSubgroup.map U.subtype).map (MulAut.conj (g : G)).toMonoidHom =
        K.toSubgroup.map U.subtype :=
  Subgroup.mem_normalizer_iff_map_conj_eq

/-- The equivalent pointwise criterion uses the canonical normalizer conjugation action on `U`. -/
theorem mem_compactOpenNormalizerStabilizer_iff_smul (U : Subgroup G)
    (K : OpenSubgroup U) (hK : IsCompact (K : Set U)) (g : Subgroup.normalizer (U : Set G)) :
    g ∈ compactOpenNormalizerStabilizer U K hK ↔ ∀ u : U, u ∈ K ↔ g • u ∈ K :=
  mem_normalizerStabilizerSubgroup_iff U K g

end Langlands
