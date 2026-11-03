import Langlands.BruhatTits.SpecialCompact.SmallSubgroupPredicates
import Langlands.BruhatTits.SpecialCompact.ContractionPredicates
import Langlands.Representation.Jacquet.IwahoriContraction

/-! # Assembly of the Jacquet contraction predicate from literal basis clauses -/

universe u

open Set Filter Topology

namespace Langlands.BruhatTits.SpecialCompact

variable {H : Type u} [Group H] [TopologicalSpace H]
  {K0 K M N Nbar : Subgroup H} {B : Set (Subgroup H)}
  {CA CAplus CAstrict : Set H} {CAeps : ℝ → Set H}

/-- The inherited identity-neighborhood basis chooses a member of the same
ambient basis whose literal intersection with `M` lies in a prescribed open
subgroup of `M`. -/
theorem InheritedCompactOpenNormalBasis.exists_intersection_le
    (hB : InheritedCompactOpenNormalBasis K0 M B) (L : OpenSubgroup M) :
    ∃ K ∈ B, K.comap M.subtype ≤ L.toSubgroup := by
  obtain ⟨D, hD, hDL⟩ := hB.2.mem_iff.mp L.mem_nhds_one
  obtain ⟨K, hK, rfl⟩ := hD
  exact ⟨K, hK, hDL⟩

/-- A specified strict element with the required Levi and chamber memberships
supplies all seven existing Jacquet fields. Its existence is separate. -/
theorem isIwahoriContraction_of_contractionAndCofinality
    (hK : IsOpen (K : Set H))
    (hfactor : HasIwahoriIntersectionDecomposition K M N Nbar)
    (hcon : ContractionAndCofinality K M N Nbar CA CAplus CAstrict CAeps)
    {g : H} (hgM : g ∈ M) (hgCA : g ∈ CA)
    (hgplus : g ∈ CAplus) (hgstrict : g ∈ CAstrict) :
    Langlands.Jacquet.IsIwahoriContraction
      (⟨K, hK⟩ : OpenSubgroup H) N M Nbar g := by
  refine ⟨hgM, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨⟨l, m, n⟩, heq⟩ := hfactor.2 ⟨k, hk⟩
    exact ⟨l, l.property, m, m.property, n, n.property,
      (congrArg Subtype.val heq).symm⟩
  · intro n hn
    exact (hcon.2.1 g hgplus).1 ⟨n, hn, rfl⟩
  · intro m hm
    have hm' : m ∈ ambientConjugate g ((K ⊓ M : Subgroup H) : Set H) := by
      rw [hcon.1 g hgCA]
      exact hm
    obtain ⟨y, hy, heq⟩ := hm'
    have h : g⁻¹ * m * g = y := by
      rw [← heq]
      group
    rw [h]
    exact hy
  · intro l hl
    simpa only [inv_inv, SetLike.mem_coe] using
      (hcon.2.1 g hgplus).2 ⟨l, hl, rfl⟩
  · intro x hx
    have hx' : x ∈ (N : Set H) := hx
    rw [(hcon.2.2.1 g hgstrict).1] at hx'
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx'
    obtain ⟨y, hy, heq⟩ := hr
    refine ⟨r, ?_⟩
    have h : g ^ r * x * (g ^ r)⁻¹ = y := by
      rw [← heq]
      group
    rw [h]
    exact hy.1
  · intro L
    let Lbar : OpenSubgroup Nbar :=
      L.comap Nbar.subtype continuous_subtype_val
    have hbasis := (hcon.2.2.2.2.1 g hgstrict).2
    obtain ⟨s, _, hs⟩ := hbasis.2.mem_iff.mp Lbar.mem_nhds_one
    refine ⟨s, ?_⟩
    intro l hl
    have hU : (g ^ s)⁻¹ * l * g ^ s ∈ Nbar := by
      have himage : (g⁻¹) ^ s * l * ((g⁻¹) ^ s)⁻¹ ∈
          ambientConjugate ((g⁻¹) ^ s) ((K ⊓ Nbar : Subgroup H) : Set H) :=
        ⟨l, hl, rfl⟩
      simpa only [inv_pow, inv_inv, SetLike.mem_coe] using hbasis.1 s himage
    apply hs (show (⟨(g ^ s)⁻¹ * l * g ^ s, hU⟩ : Nbar) ∈
      {x : Nbar | ∃ y : Nbar, y ∈ Subgroup.comap Nbar.subtype K ∧
        (x : H) = (g⁻¹) ^ s * (y : H) * ((g⁻¹) ^ s)⁻¹} from ?_)
    exact ⟨⟨l, hl.2⟩, hl.1, by simp only [inv_pow, inv_inv]⟩

end Langlands.BruhatTits.SpecialCompact
