import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Separation.Profinite
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Power quotients from an open subgroup
-/

open Function Set Topology

universe u

namespace Langlands

variable {G : Type u} [CommGroup G] (P H : Subgroup G) (m : ℕ)

/-- The map induced by the inclusion of `H` and the quotient by `P`, on
the quotients by `m`th powers. -/
def openSubgroupPowerClassMap :
    (H ⧸ (powMonoidHom (α := H) m).range) →*
      ((G ⧸ P) ⧸ (powMonoidHom (α := G ⧸ P) m).range) :=
  QuotientGroup.map _ _
    ((QuotientGroup.mk' P).comp H.subtype) (by
      rintro _ ⟨h, rfl⟩
      exact ⟨(QuotientGroup.mk' P) h, by simp⟩)

@[simp]
theorem openSubgroupPowerClassMap_mk (h : H) :
    openSubgroupPowerClassMap P H m (QuotientGroup.mk h) =
      QuotientGroup.mk (QuotientGroup.mk (h : G) : G ⧸ P) := rfl

/-- If `P` and `H` generate `G`, the inclusion of `H` surjects onto `G/P`. -/
theorem subgroupClassMap_surjective (hPH : P ⊔ H = ⊤) :
    Surjective ((QuotientGroup.mk' P).comp H.subtype) := by
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg : g ∈ P ⊔ H := hPH ▸ Subgroup.mem_top g
  obtain ⟨p, hp, h, hh, rfl⟩ := Subgroup.mem_sup.mp hg
  refine ⟨⟨h, hh⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, QuotientGroup.mk'_apply,
    QuotientGroup.mk_mul]
  rw [(QuotientGroup.eq_one_iff p).mpr hp, one_mul]

theorem openSubgroupPowerClassMap_surjective (hPH : P ⊔ H = ⊤) :
    Surjective (openSubgroupPowerClassMap P H m) := by
  apply QuotientGroup.map_surjective_of_surjective
  exact QuotientGroup.mk_surjective.comp (subgroupClassMap_surjective P H hPH)

/-- The kernel consists exactly of the power classes of elements of `P ∩ H`. -/
theorem openSubgroupPowerClassMap_ker (hPH : P ⊔ H = ⊤) :
    (openSubgroupPowerClassMap P H m).ker =
      (P.subgroupOf H).map (QuotientGroup.mk' (powMonoidHom (α := H) m).range) := by
  ext x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  change QuotientGroup.mk (QuotientGroup.mk (h : G) : G ⧸ P) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨a, ha⟩ := subgroupClassMap_surjective P H hPH c
    have hpa : (h / a ^ m : H) ∈ P.subgroupOf H := by
      change (h : G) / (a : G) ^ m ∈ P
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' P) ((h : G) / (a : G) ^ m) = 1
      rw [map_div, map_pow]
      change (QuotientGroup.mk' P) (h : G) / _ = 1
      rw [show (QuotientGroup.mk' P) (a : G) = c from ha]
      exact div_eq_one.mpr hc.symm
    refine ⟨h / a ^ m, hpa, ?_⟩
    have hap : (QuotientGroup.mk' (powMonoidHom (α := H) m).range) (a ^ m) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩
    rw [map_div, hap, div_one]
    rfl
  · rintro ⟨a, ha, heq⟩
    have hfa : openSubgroupPowerClassMap P H m
        ((QuotientGroup.mk' (powMonoidHom (α := H) m).range) a) = 1 := by
      change QuotientGroup.mk (QuotientGroup.mk (a : G) : G ⧸ P) = 1
      rw [(QuotientGroup.eq_one_iff (a : G)).mpr ha]
      rfl
    have hfh : openSubgroupPowerClassMap P H m (QuotientGroup.mk h) = 1 := by
      simpa only [heq] using hfa
    exact (QuotientGroup.eq_one_iff _).mp hfh

/-- The image of a finitely generated intersection in a positive power
quotient is finite, since it is finitely generated and torsion. -/
theorem subgroupPowerClassImage_finite_of_fg (hfg : (P.subgroupOf H).FG) (hm : 0 < m) :
    ((P.subgroupOf H).map (QuotientGroup.mk' (powMonoidHom (α := H) m).range) :
      Set (H ⧸ (powMonoidHom (α := H) m).range)).Finite := by
  let R := (P.subgroupOf H).map (QuotientGroup.mk' (powMonoidHom (α := H) m).range)
  have hRfg : R.FG := by
    rw [Subgroup.fg_iff_submonoid_fg] at hfg ⊢
    exact hfg.map _
  have : Group.FG R := (Group.fg_iff_subgroup_fg R).mpr hRfg
  have : Finite R := CommGroup.finite_of_fg_isMulTorsion R
    ((CommGroup.isMulTorsion_quotient_range_powMonoidHom H (Nat.ne_of_gt hm)).subgroup R)
  exact Set.toFinite _

section Topology

variable [TopologicalSpace G]

theorem openSubgroupPowerClassMap_continuous :
    Continuous (openSubgroupPowerClassMap P H m) := by
  apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
  exact QuotientGroup.continuous_mk.comp
    (QuotientGroup.continuous_mk.comp continuous_subtype_val)

variable [IsTopologicalGroup G]

theorem openSubgroupPowerClassMap_isOpenMap (hH : IsOpen (H : Set G)) :
    IsOpenMap (openSubgroupPowerClassMap P H m) := by
  apply IsOpenMap.of_comp QuotientGroup.continuous_mk QuotientGroup.mk_surjective
  exact QuotientGroup.isOpenMap_coe.comp
    (QuotientGroup.isOpenMap_coe.comp hH.isOpenMap_subtype_val)

theorem openSubgroupPowerClassMap_isOpenQuotientMap (hH : IsOpen (H : Set G))
    (hPH : P ⊔ H = ⊤) :
    IsOpenQuotientMap (openSubgroupPowerClassMap P H m) :=
  ⟨openSubgroupPowerClassMap_surjective P H m hPH,
    openSubgroupPowerClassMap_continuous P H m,
    openSubgroupPowerClassMap_isOpenMap P H m hH⟩

end Topology

/-- An open quotient homomorphism with finite kernel carries a compact
Hausdorff totally disconnected group to a space with the same properties. -/
theorem openQuotientHom_profinite_of_finite_kernel
    {A B : Type*} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalGroup B] [T2Space A] [CompactSpace A] [TotallyDisconnectedSpace A]
    (f : A →* B) (hf : IsOpenQuotientMap f) (hker : (f.ker : Set A).Finite) :
    T2Space B ∧ CompactSpace B ∧ TotallyDisconnectedSpace B := by
  have hclosed : IsClosed ({1} : Set B) :=
    hf.isQuotientMap.isClosed_preimage.mp hker.isClosed
  let : T2Space B := IsTopologicalGroup.t2Space_iff_one_closed.mpr hclosed
  let : CompactSpace B := hf.surjective.compactSpace hf.continuous
  have hsep : TotallySeparatedSpace B := by
    apply totallySeparatedSpace_iff_exists_isClopen.mpr
    intro x y hxy
    obtain ⟨a, ha⟩ := hf.surjective x
    have hopen : IsOpen (f ⁻¹' ({y}ᶜ : Set B)) :=
      isClosed_singleton.isOpen_compl.preimage hf.continuous
    have hamem : a ∈ f ⁻¹' ({y}ᶜ : Set B) := by simpa [ha] using hxy
    obtain ⟨V, hV, haV, hVU⟩ := compact_exists_isClopen_in_isOpen hopen hamem
    refine ⟨f '' V, ⟨(hV.isClosed.isCompact.image hf.continuous).isClosed,
      hf.isOpenMap V hV.isOpen⟩, ⟨a, haV, ha⟩, ?_⟩
    rintro ⟨b, hb, hby⟩
    exact hVU hb (by simpa using hby)
  let := hsep
  exact ⟨inferInstance, inferInstance, inferInstance⟩

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space (H ⧸ (powMonoidHom (α := H) m).range)]
variable [CompactSpace (H ⧸ (powMonoidHom (α := H) m).range)]
variable [TotallyDisconnectedSpace (H ⧸ (powMonoidHom (α := H) m).range)]

/-- A finite image of `P ∩ H` allows passing profinite power quotients
from the open subgroup `H` to `G/P`. -/
theorem openSubgroupPowerQuotient_profinite
    (hH : IsOpen (H : Set G)) (hPH : P ⊔ H = ⊤)
    (hfinite : ((P.subgroupOf H).map
      (QuotientGroup.mk' (powMonoidHom (α := H) m).range) :
        Set (H ⧸ (powMonoidHom (α := H) m).range)).Finite) :
    T2Space ((G ⧸ P) ⧸ (powMonoidHom (α := G ⧸ P) m).range) ∧
    CompactSpace ((G ⧸ P) ⧸ (powMonoidHom (α := G ⧸ P) m).range) ∧
    TotallyDisconnectedSpace ((G ⧸ P) ⧸ (powMonoidHom (α := G ⧸ P) m).range) := by
  apply openQuotientHom_profinite_of_finite_kernel (openSubgroupPowerClassMap P H m)
    (openSubgroupPowerClassMap_isOpenQuotientMap P H m hH hPH)
  rwa [openSubgroupPowerClassMap_ker P H m hPH]

/-- Finite generation of the intersection supplies the finite-image hypothesis. -/
theorem openSubgroupPowerQuotient_profinite_of_fg
    (hH : IsOpen (H : Set G)) (hPH : P ⊔ H = ⊤)
    (hfg : (P.subgroupOf H).FG) (hm : 0 < m) :
    T2Space ((G ⧸ P) ⧸ (powMonoidHom (α := G ⧸ P) m).range) ∧
    CompactSpace ((G ⧸ P) ⧸ (powMonoidHom (α := G ⧸ P) m).range) ∧
    TotallyDisconnectedSpace ((G ⧸ P) ⧸ (powMonoidHom (α := G ⧸ P) m).range) :=
  openSubgroupPowerQuotient_profinite P H m hH hPH
    (subgroupPowerClassImage_finite_of_fg P H m hfg hm)

end Topology

end Langlands
