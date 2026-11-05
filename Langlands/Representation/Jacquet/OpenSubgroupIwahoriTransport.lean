import Langlands.Representation.Induction.OpenAdjunction
import Langlands.Representation.Jacquet.IwahoriStablePairingData
import Langlands.Representation.CompactCoefficient.IwahoriContractionConverse
import Langlands.Representation.CompactCoefficient.GroupTransport

/-! # Iwahori contraction bases inside an open subgroup -/

noncomputable section

open Topology

namespace Langlands.Jacquet

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The image of an open subgroup of an open subgroup in the ambient group. -/
def ambientOpenSubgroup (H : Subgroup G) (hH : IsOpen (H : Set G))
    (L : OpenSubgroup H) : OpenSubgroup G :=
  Langlands.Induction.openSubgroupMap H hH L

omit [IsTopologicalGroup G] in
/-- An ambient Iwahori contraction restricts to an open subgroup containing
its whole level and its specified contracting element. -/
theorem IsIwahoriContraction.comap_of_le
    {K : OpenSubgroup G} {N M Nbar : Subgroup G} (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (hKH : K.toSubgroup ≤ H) (g : H)
    (h : IsIwahoriContraction K N M Nbar g.val) :
    IsIwahoriContraction (K.comap H.subtype continuous_subtype_val)
      (N.comap H.subtype) (M.comap H.subtype) (Nbar.comap H.subtype) g := by
  refine
    { mem_levi := h.mem_levi
      factor := ?_
      upper := fun u hu => h.upper u.val hu
      levi := fun m hm => h.levi m.val hm
      lower := fun l hl => h.lower l.val hl
      exhaust := fun x hx => h.exhaust x.val hx
      contract := ?_ }
  · intro k hk
    obtain ⟨l, hl, m, hm, u, hu, heq⟩ := h.factor k.val hk
    refine ⟨⟨l, hKH hl.1⟩, hl, ⟨m, hKH hm.1⟩, hm, ⟨u, hKH hu.1⟩, hu, ?_⟩
    exact Subtype.ext heq
  · intro L
    obtain ⟨s, hs⟩ := h.contract (ambientOpenSubgroup H hH L)
    refine ⟨s, fun l hl => ?_⟩
    obtain ⟨x, hx, heq⟩ := hs l.val hl
    exact (Subtype.ext heq : x = (g ^ s)⁻¹ * l * g ^ s) ▸ hx

omit [IsTopologicalGroup G] in
/-- Cofinal opposite Iwahori contractions restrict through any open subgroup
containing the specified contracting element. -/
theorem HasOppositeIwahoriContractionBasis.comap_open
    {N M Nbar : Subgroup G} (H : Subgroup G) (hH : IsOpen (H : Set G))
    (g : H) (hbasis : HasOppositeIwahoriContractionBasis N M Nbar g.val) :
    HasOppositeIwahoriContractionBasis (N.comap H.subtype)
      (M.comap H.subtype) (Nbar.comap H.subtype) g := by
  intro O hO h1
  have hO' : IsOpen ((Subtype.val : H → G) '' O) := hH.isOpenMap_subtype_val _ hO
  obtain ⟨K, hK, hKO, hg, hgi⟩ := hbasis _ hO' ⟨1, h1, rfl⟩
  have hKH : K.toSubgroup ≤ H := by
    intro k hk
    obtain ⟨x, _, rfl⟩ := hKO hk
    exact x.property
  let L := K.comap H.subtype continuous_subtype_val
  have hL : IsCompact (L : Set H) := by
    rw [Subtype.isCompact_iff]
    have heq : (Subtype.val : H → G) '' (L : Set H) = K := by
      ext x
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hx
        exact ⟨⟨x, hKH hx⟩, hx, rfl⟩
    rwa [heq]
  refine ⟨L, hL, ?_, hg.comap_of_le H hH hKH g, hgi.comap_of_le H hH hKH g⁻¹⟩
  intro x hx
  obtain ⟨y, hy, heq⟩ := hKO hx
  exact (Subtype.ext heq : y = x) ▸ hy

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Normalization restricts to the actual intersection subgroups. -/
theorem normalizer_comap_subtype (H N M : Subgroup G)
    (hMN : M ≤ Subgroup.normalizer N) :
    M.comap H.subtype ≤ Subgroup.normalizer (N.comap H.subtype) := by
  intro m hm
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  exact Subgroup.mem_normalizer_iff.mp (hMN hm) x.val

/-- Compact smooth-dual coefficients and an escaping opposite Iwahori basis
force the actual Jacquet coinvariants to vanish, with independent universes. -/
theorem subsingleton_coinvariants_of_compact_escaping_basis
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hc : HasCompactSmoothDualCoefficients ρ)
    (N M Nbar : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (g : G) (hbasis : HasOppositeIwahoriContractionBasis N M Nbar g)
    (hescape : CompactCoefficient.EscapesCompactSets (fun r : ℕ => g ^ r)) :
    Subsingleton (Coinvariants ρ N) := by
  let e : (⊤ : Subgroup G) ≃ₜ* G :=
    { toMulEquiv := Subgroup.topEquiv
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  have hc' : HasCompactSmoothDualCoefficients (ρ.comp (⊤ : Subgroup G).subtype) :=
    (hasCompactSmoothDualCoefficients_comp_continuousMulEquiv_iff ρ e).mpr hc
  apply CompactCoefficient.subsingleton_coinvariants_of_compact_restriction
    ρ hρ ⊤ N M Nbar hMN hc'
  intro U
  obtain ⟨K, hK, hKU, hg, _⟩ := hbasis U U.isOpen U.one_mem
  refine ⟨K, hK, hKU, ⟨g, Subgroup.mem_top g⟩, hg, ?_⟩
  apply CompactCoefficient.EscapesCompactSets.of_continuous
    (f := (Subtype.val : (⊤ : Subgroup G) → G)) (hf := continuous_subtype_val)
  exact hescape

end Langlands.Jacquet
