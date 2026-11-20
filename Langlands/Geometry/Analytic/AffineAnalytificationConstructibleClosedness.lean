import Langlands.Geometry.Analytic.AnalytificationCenter
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Langlands.Geometry.Analytic.SeparatedAnalytificationDensity
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet

/-! # Detection of closed constructible sets by affine analytification -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification

open Set Topology PrimeSpectrum

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

private theorem exists_center_eq_mem_closure_basicOpen [IsDomain A]
    {m : PrimeSpectrum A} (hm : m.asIdeal.IsMaximal) {a : A} (ha : a ≠ 0) :
    ∃ x ∈ closure (center K P ⁻¹' (basicOpen a : Set (PrimeSpectrum A))),
      center K P x = m := by
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  obtain ⟨η, hη, hz, hcl⟩ :=
    SeparatedAnalytificationDensity.exists_mulRingSeminorm_mem_closure (K := K)
      m.asIdeal hm.ne_top ha
  have hpoint {ν : MulRingSeminorm A} (hν : ExtendsNorm K ν) :
      ∃ x : Space K P, pointSeminorm K P x = ν := by
    rw [← Set.mem_range, SeminormComparison.range_pointSeminorm]
    exact hν
  obtain ⟨x, hx⟩ := hpoint hη
  refine ⟨x, ?_, PrimeSpectrum.ext ?_⟩
  · rw [(SeminormComparison.isEmbedding_pointSeminorm K P).closure_eq_preimage_closure_image]
    change (fun b => pointSeminorm K P x b) ∈ closure _
    rw [hx]
    apply closure_mono _ hcl
    rintro _ ⟨ν, hν, hνa, rfl⟩
    obtain ⟨y, hy⟩ := hpoint hν
    refine ⟨y, (center_mem_basicOpen K P y a).mpr ?_, ?_⟩
    · simpa only [hy] using hνa
    · exact congrArg DFunLike.coe hy
  · exact (hm.eq_of_le (kernel_isPrime K P x).ne_top
      (fun b hb => (mem_kernel K P x b).mpr (hx ▸ hz b hb))).symm

private theorem mem_zeroLocus_singleton (p : PrimeSpectrum A) (a : A) :
    p ∈ zeroLocus ({a} : Set A) ↔ a ∈ p.asIdeal :=
  (PrimeSpectrum.mem_zeroLocus _ _).trans Set.singleton_subset_iff

private theorem exists_center_eq_mem_closure_of_specialization {s : Set (PrimeSpectrum A)}
    (hs : IsConstructible s) {p m : PrimeSpectrum A} (hp : p ∈ s) (hpm : p ≤ m)
    (hm : m.asIdeal.IsMaximal) :
    ∃ x ∈ closure (center K P ⁻¹' s), center K P x = m := by
  obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  obtain ⟨U, hU, hpU⟩ := Set.mem_iUnion₂.mp hp
  let D := A ⧸ p.asIdeal
  let π : A →ₐ[K] D := Ideal.Quotient.mkₐ K p.asIdeal
  let : IsDomain D := Ideal.Quotient.isDomain p.asIdeal
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let Q := FinitePolynomialPresentation.ofFiniteType K D
  have hπ : Function.Surjective (π : A →+* D) := Ideal.Quotient.mk_surjective
  have hm' : m ∈ Set.range (PrimeSpectrum.comap (π : A →+* D)) := by
    rw [range_comap_of_surjective D _ hπ]
    change RingHom.ker (Ideal.Quotient.mk p.asIdeal) ≤ m.asIdeal
    rwa [Ideal.mk_ker]
  obtain ⟨n, rfl⟩ := hm'
  have hn : n.asIdeal.IsMaximal := by
    apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
    apply (PrimeSpectrum.isClosedEmbedding_comap_of_surjective D _ hπ).isClosed_iff_image_isClosed.mpr
    rw [Set.image_singleton]
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hm
  have ha : π U.f ≠ 0 := by
    intro h
    exact hpU.2 ((mem_zeroLocus_singleton _ _).mpr
      (Ideal.Quotient.eq_zero_iff_mem.mp h))
  obtain ⟨x, hx, hxcenter⟩ := exists_center_eq_mem_closure_basicOpen K Q hn ha
  have him :
      baseMap K P Q π '' (center K Q ⁻¹' (basicOpen (π U.f) : Set (PrimeSpectrum D))) ⊆
        center K P ⁻¹' S.toSet := by
    rintro _ ⟨y, hy, rfl⟩
    change center K P (baseMap K P Q π y) ∈ S.toSet
    rw [center_baseMap]
    apply Set.mem_iUnion₂.mpr ⟨U, hU, ?_⟩
    constructor
    · exact fun a ha => by
        change π a ∈ (center K Q y).asIdeal
        rw [show π a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (hpU.1 ha)]
        exact Ideal.zero_mem _
    · exact fun h => (PrimeSpectrum.mem_basicOpen _ _).mp hy
        (show U.f ∈ (PrimeSpectrum.comap (π : A →+* D) (center K Q y)).asIdeal
          from (mem_zeroLocus_singleton _ _).mp h)
  exact ⟨baseMap K P Q π x, closure_mono him
    (closure_subset_preimage_closure_image (baseMap K P Q π).continuous hx),
    (center_baseMap K P Q π x).trans (congrArg (PrimeSpectrum.comap (π : A →+* D)) hxcenter)⟩

/-- An analytic point in the closure of the inverse image of a constructible set,
with center a specified maximal specialization of one of its points. -/
def constructibleClosurePoint {s : Set (PrimeSpectrum A)}
    (hs : IsConstructible s) {p m : PrimeSpectrum A} (hp : p ∈ s) (hpm : p ≤ m)
    (hm : m.asIdeal.IsMaximal) :
    {x : Space K P // x ∈ closure (center K P ⁻¹' s) ∧ center K P x = m} :=
  let h := exists_center_eq_mem_closure_of_specialization K P hs hp hpm hm
  ⟨h.choose, h.choose_spec⟩

private theorem exists_maximal_specialization_mem_constructible [IsJacobsonRing A]
    {s : Set (PrimeSpectrum A)}
    (hs : IsConstructible s) {q : PrimeSpectrum A} (hq : q ∈ s) :
    ∃ m : PrimeSpectrum A, q ≤ m ∧ m.asIdeal.IsMaximal ∧ m ∈ s := by
  obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  obtain ⟨U, hU, hqU⟩ := Set.mem_iUnion₂.mp hq
  have hqf : U.f ∉ q.asIdeal := fun hf =>
    hqU.2 ((mem_zeroLocus_singleton _ _).mpr hf)
  have hm : ∃ m : Ideal A, q.asIdeal ≤ m ∧ m.IsMaximal ∧ U.f ∉ m := by
    by_contra! h
    apply hqf
    rw [← IsJacobsonRing.out ‹_› q.isPrime.isRadical, Ideal.jacobson, Submodule.mem_sInf]
    exact fun m hm => h m hm.1 hm.2
  obtain ⟨m, hqm, hm, hmf⟩ := hm
  exact ⟨⟨m, hm.isPrime⟩, hqm, hm, Set.mem_iUnion₂.mpr ⟨U, hU,
    fun a ha => hqm (hqU.1 ha), fun h => hmf ((mem_zeroLocus_singleton _ _).mp h)⟩⟩

/-- A constructible subset of the affine scheme is closed when its full inverse
image under the analytification center map is closed. -/
theorem isClosed_of_isConstructible_of_isClosed_center_preimage {s : Set (PrimeSpectrum A)}
    (hs : IsConstructible s) (hc : IsClosed (center K P ⁻¹' s)) : IsClosed s := by
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  apply isClosed_of_stableUnderSpecialization_of_isConstructible _ hs
  intro p q hpq hp
  by_contra hq
  obtain ⟨m, hqm, hm, hms⟩ :=
    exists_maximal_specialization_mem_constructible hs.compl hq
  obtain ⟨x, hx, hxm⟩ := constructibleClosurePoint K P hs hp
    (((PrimeSpectrum.le_iff_specializes _ _).mpr hpq).trans hqm) hm
  exact hms (hxm ▸ hc.closure_subset hx)

end Langlands.Analytic.AffineAnalytification
