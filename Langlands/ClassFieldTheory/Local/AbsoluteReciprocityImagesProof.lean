import Langlands.ClassFieldTheory.Local.AbsoluteReciprocityStatement
import Langlands.ClassFieldTheory.Local.UpperReciprocityStatement
import Langlands.ClassFieldTheory.Local.WeilReciprocityUniquenessProof
import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof
import Langlands.LocalFactor.Ramification.Herbrand.AbsoluteStatement

/-! # Compact passage from finite to absolute reciprocity images -/

noncomputable section

namespace Langlands.LocalClassField

universe u

section FiniteAbelianImages

variable (K : Type u) [Field K]

/-- The subgroup cut out by all finite abelian restriction images of a subgroup.
For a closed subgroup this recovers the original subgroup. -/
def finiteAbelianSubgroupLocus
    (H : Subgroup (Field.absoluteGaloisGroupAbelianization K)) :
    Subgroup (Field.absoluteGaloisGroupAbelianization K) :=
  ⨅ L : FiniteAbelianExtension K,
    (H.map L.abelianRestriction.toMonoidHom).comap L.abelianRestriction.toMonoidHom

theorem mem_finiteAbelianSubgroupLocus_iff
    (H : Subgroup (Field.absoluteGaloisGroupAbelianization K))
    (a : Field.absoluteGaloisGroupAbelianization K) :
    a ∈ finiteAbelianSubgroupLocus K H ↔
      ∀ L : FiniteAbelianExtension K,
        L.abelianRestriction a ∈ H.map L.abelianRestriction.toMonoidHom := by
  simp [finiteAbelianSubgroupLocus]

/-- A closed subgroup of a Hausdorff nonarchimedean abelian group is the
intersection of the open subgroups containing it. -/
theorem mem_closedSubgroup_of_open_overgroups
    {A : Type u} [CommGroup A] [TopologicalSpace A]
    [NonarchimedeanGroup A] [T2Space A]
    (H : Subgroup A) (hH : IsClosed (H : Set A))
    (a : A) (ha : ∀ U : OpenSubgroup A, H ≤ U.toSubgroup → a ∈ U) :
    a ∈ H := by
  let : IsClosed (H : Set A) := hH
  let := quotientNonarchimedean H
  let q : A →ₜ* A ⧸ H :=
    { toMonoidHom := QuotientGroup.mk' H
      continuous_toFun := QuotientGroup.continuous_mk }
  by_contra hnot
  have hqa : q a ≠ 1 := by
    exact fun h => hnot ((QuotientGroup.eq_one_iff a).mp h)
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean
    ({q a}ᶜ : Set (A ⧸ H)) (isClosed_singleton.isOpen_compl.mem_nhds hqa.symm)
  let U : OpenSubgroup A := V.comap q.toMonoidHom q.continuous
  have hHU : H ≤ U.toSubgroup := by
    intro h hh
    change q h ∈ V
    rw [show q h = 1 from (QuotientGroup.eq_one_iff h).mpr hh]
    exact V.one_mem
  exact hV (ha U hHU) rfl

/-- All finite abelian images determine a closed absolute-Galois subgroup. -/
theorem finiteAbelianSubgroupLocus_eq [PerfectField K]
    (H : Subgroup (Field.absoluteGaloisGroupAbelianization K))
    (hH : IsClosed (H : Set (Field.absoluteGaloisGroupAbelianization K))) :
    finiteAbelianSubgroupLocus K H = H := by
  let := absoluteGaloisNonarchimedean K
  let := abelianizationHausdorff (Field.absoluteGaloisGroup K)
  let := quotientNonarchimedean
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure
  apply le_antisymm
  · intro a ha
    apply mem_closedSubgroup_of_open_overgroups H hH a
    intro U hHU
    obtain ⟨L, hL⟩ :=
      WeilReciprocityUniqueness.exists_finiteAbelianExtension_of_isOpen
        U.toSubgroup U.isOpen
    obtain ⟨b, hb, he⟩ :=
      (mem_finiteAbelianSubgroupLocus_iff K H a).mp ha L
    exact (hL a).mpr (he ▸ (hL b).mp (hHU hb))
  · intro a ha
    exact (mem_finiteAbelianSubgroupLocus_iff K H a).mpr
      (fun L => Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)

/-- Equality of every finite abelian image is equality for closed subgroups. -/
theorem closedSubgroup_eq_of_finiteAbelianImages [PerfectField K]
    (H J : Subgroup (Field.absoluteGaloisGroupAbelianization K))
    (hH : IsClosed (H : Set (Field.absoluteGaloisGroupAbelianization K)))
    (hJ : IsClosed (J : Set (Field.absoluteGaloisGroupAbelianization K)))
    (h : ∀ L : FiniteAbelianExtension K,
      H.map L.abelianRestriction.toMonoidHom =
        J.map L.abelianRestriction.toMonoidHom) :
    H = J := by
  rw [← finiteAbelianSubgroupLocus_eq K H hH,
    ← finiteAbelianSubgroupLocus_eq K J hJ]
  simp only [finiteAbelianSubgroupLocus, h]

end FiniteAbelianImages

section AbsoluteImages

open Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Compactness of the actual absolute upper subgroup makes its literal
abelianization image closed. -/
theorem localAbelianUpperRamificationGroup_isClosed (v : ℝ) :
    IsClosed (localAbelianUpperRamificationGroup F v :
      Set (Field.absoluteGaloisGroupAbelianization F.Carrier)) := by
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  let : CompactSpace (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F.Carrier/F.Carrier))
  let : T2Space (Field.absoluteGaloisGroupAbelianization F.Carrier) :=
    abelianizationHausdorff (Field.absoluteGaloisGroup F.Carrier)
  exact ((absoluteUpperRamificationGroup_isClosed F v).isCompact.image
    (localAbelianGaloisProjection F).continuous).isClosed

/-- Finite restriction of the literal absolute abelian upper group is the
actual finite upper group, assuming the absolute arithmetic image theorem. -/
theorem localAbelianUpperRamificationGroup_map_restriction
    (habsolute : AbsoluteUpperFiniteImage F)
    (L : LocalFiniteAbelianExtension F) (v : ℝ) (hv : -1 ≤ v) :
    (localAbelianUpperRamificationGroup F v).map
        L.abelianRestriction.toMonoidHom =
      canonicalUpperRamificationGroup (absoluteFiniteExtension F L.field)
        F.Carrier v := by
  rw [localAbelianUpperRamificationGroup, Subgroup.map_map]
  change (absoluteUpperRamificationGroup F v).map
    (absoluteFiniteRestriction F L.field).toMonoidHom = _
  exact habsolute L.field v hv

end AbsoluteImages

/-- Finite real unit images and absolute finite quotient compatibility imply
the literal real unit-image equality in the absolute abelianization. -/
theorem absoluteReciprocityRealUnitImages_of_finite
    (hfinite : FiniteReciprocityRealUnitImages.{u})
    (habsolute : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
      Ramification.Padic.AbsoluteUpperFiniteImage F) :
    AbsoluteReciprocityRealUnitImages.{u} := by
  intro p _ F T
  let := T.topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : T2Space (Field.absoluteGaloisGroupAbelianization F.Carrier) :=
    abelianizationHausdorff (Field.absoluteGaloisGroup F.Carrier)
  intro r hr v hv
  apply closedSubgroup_eq_of_finiteAbelianImages F.Carrier
  · exact ((T.isCompact_unitFiltration ⌈v⌉₊).image r.continuous).isClosed
  · exact localAbelianUpperRamificationGroup_isClosed F v
  · intro L
    rw [Subgroup.map_map,
      localAbelianUpperRamificationGroup_map_restriction F (habsolute p F) L v
        (by linarith)]
    exact hfinite p F T r hr L
      (L.asPadicField (p := p)).canonicalTopologicalData v hv

/-- Integer indices are the natural specializations of the real image formula. -/
theorem absoluteReciprocityHigherUnitImages_of_real
    (hreal : AbsoluteReciprocityRealUnitImages.{u}) :
    AbsoluteReciprocityHigherUnitImages.{u} := by
  intro p _ F T
  let := T.topology
  intro r hr n
  simpa using hreal p F T r hr (n : ℝ) (Nat.cast_nonneg n)

/-- The level-zero image formula identifies valuation units with inertia
once the arithmetic zero-level comparison is supplied. -/
theorem absoluteReciprocityInertiaImage_of_higher
    (hhigher : AbsoluteReciprocityHigherUnitImages.{u})
    (hinertia : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
      (T : F.TopologicalData), Ramification.Padic.AbsoluteUpperInertia F T) :
    AbsoluteReciprocityInertiaImage.{u} := by
  intro p _ F T
  let := T.topology
  intro r hr
  have h := hhigher p F T r hr 0
  rw [T.unitFiltration_zero] at h
  simp only [Nat.cast_zero, Ramification.Padic.localAbelianUpperRamificationGroup] at h
  rw [show Ramification.Padic.absoluteUpperRamificationGroup F 0 =
    F.absoluteInertia T from hinertia p F T] at h
  exact h

/-- The compact finite-to-absolute passage for all three subgroup image targets.
The finite reciprocity and absolute arithmetic inputs are retained explicitly. -/
theorem absoluteReciprocityImages_of_finite
    (hfinite : FiniteReciprocityRealUnitImages.{u})
    (habsolute : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p),
      Ramification.Padic.AbsoluteUpperFiniteImage F)
    (hinertia : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
      (T : F.TopologicalData), Ramification.Padic.AbsoluteUpperInertia F T) :
    AbsoluteReciprocityInertiaImage.{u} ∧
      AbsoluteReciprocityHigherUnitImages.{u} ∧
        AbsoluteReciprocityRealUnitImages.{u} := by
  have hreal := absoluteReciprocityRealUnitImages_of_finite hfinite habsolute
  have hhigher := absoluteReciprocityHigherUnitImages_of_real hreal
  exact ⟨absoluteReciprocityInertiaImage_of_higher hhigher hinertia, hhigher, hreal⟩

end Langlands.LocalClassField
