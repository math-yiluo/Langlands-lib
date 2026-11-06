import Langlands.Cohomology.SupercuspidalRestriction.Statement
import Langlands.Analysis.CompactKernelHaarLpProof
import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof

noncomputable section

open Topology

namespace Langlands.Cohomology.SupercuspidalRestriction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Compact sets in the central quotient have compact inverse images in an
open subgroup whose intersection with the center is compact. -/
theorem isCompact_centralQuotient_preimage_openSubgroup
    (H : Subgroup G) (hH : IsOpen (H : Set G))
    (hHZ : IsCompact ((H ⊓ Subgroup.center G : Subgroup G) : Set G))
    {C : Set (G ⧸ Subgroup.center G)} (hC : IsCompact C) :
    IsCompact ((fun h : H => (QuotientGroup.mk h.val : G ⧸ Subgroup.center G)) ⁻¹' C) := by
  have hZ : IsClosed (Subgroup.center G : Set G) := by
    simpa only [Set.centralizer_univ, Subgroup.coe_center] using
      (Set.isClosed_centralizer (Set.univ : Set G))
  let : IsClosed (Subgroup.center G : Set G) := hZ
  let : LocallyCompactSpace H := (H.isClosed_of_isOpen hH).locallyCompactSpace
  let f : H →* (G ⧸ Subgroup.center G) :=
    (QuotientGroup.mk' (Subgroup.center G)).comp H.subtype
  have hfopen : IsOpenMap f :=
    QuotientGroup.isOpenMap_coe.comp hH.isOpenMap_subtype_val
  have hSopen : IsOpen (f.range : Set (G ⧸ Subgroup.center G)) := by
    simpa only [MonoidHom.coe_range] using hfopen.isOpen_range
  let : LocallyCompactSpace f.range := hSopen.locallyCompactSpace
  let q : H →ₜ* f.range :=
    { f.rangeRestrict with
      continuous_toFun := (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _ }
  have hqsurj : Function.Surjective q := f.rangeRestrict_surjective
  have hqopen : IsOpenMap q := by
    exact hSopen.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr hfopen
  have hqker : IsCompact (q.ker : Set H) := by
    apply (IsEmbedding.subtypeVal.isCompact_iff).mpr
    convert hHZ using 1
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h.property, ?_⟩
      exact (QuotientGroup.eq_one_iff h.val).mp (congrArg Subtype.val hh)
    · rintro ⟨hgH, hgZ⟩
      refine ⟨⟨g, hgH⟩, ?_, rfl⟩
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff g).mpr hgZ
  have hproper := compactKernelProperMap H f.range q hqsurj hqopen hqker
  have hCS : IsCompact (Subtype.val ⁻¹' C : Set f.range) :=
    (f.range.isClosed_of_isOpen hSopen).isClosedEmbedding_subtypeVal.isCompact_preimage hC
  exact hproper.isCompact_preimage hCS

/-- Coefficients compact modulo the ambient center restrict to compactly
supported coefficients on an open subgroup with compact central intersection. -/
theorem hasCompactSupport_restrict_matrixCoefficient
    (H : Subgroup G) (hH : IsOpen (H : Set G))
    (hHZ : IsCompact ((H ⊓ Subgroup.center G : Subgroup G) : Set G))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : HasCompactSmoothCoefficientsModCenter ρ)
    (ℓ : Module.Dual ℂ V)
    (hℓ : IsSmoothVector (Representation.dual (ρ.comp H.subtype)) ℓ) (v : V) :
    HasCompactSupport (matrixCoefficient (ρ.comp H.subtype) ℓ v) := by
  have hℓG : IsSmoothVector ρ.dual ℓ :=
    (isSmoothVector_restrict_open_iff ρ.dual (⟨H, hH⟩ : OpenSubgroup G) ℓ).mp hℓ
  obtain ⟨C, hC, hsupport⟩ := hρ ⟨ℓ, hℓG⟩ v
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_centralQuotient_preimage_openSubgroup H hH hHZ hC)
  intro h hh
  exact hsupport h.val hh

end Langlands.Cohomology.SupercuspidalRestriction
