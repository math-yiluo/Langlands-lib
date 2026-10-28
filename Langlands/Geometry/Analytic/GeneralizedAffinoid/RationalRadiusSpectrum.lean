import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectrum
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalRadiusRestriction

/-! # Closed spectrum embeddings for smaller rational radii -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation

open GeneralizedTateAlgebra

private theorem range_eq_preimage_of_injective {X Y Z : Type*}
    (q : X → Z) (r : Y → X) (p : Y → Z) (V : Set Z)
    (hq : Function.Injective q) (hcomp : ∀ y, q (r y) = p y)
    (hp : Set.range p = V) :
    Set.range r = q ⁻¹' V := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change q (r y) ∈ V
    rw [hcomp, ← hp]
    exact Set.mem_range_self y
  · intro hx
    have hx' : q x ∈ Set.range p := by
      rw [hp]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    exact ⟨y, hq ((hcomp y).trans hy)⟩

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s t : PositivePolyradius (Fin m))
  (hts : ∀ j, t j ≤ s j)
  (g : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)

/-- The proved spectrum identification, bundled as a homeomorphism onto the
actual weighted rational inequality subspace. -/
def locusHomeomorph (hunit : GeneratesUnitIdeal K A g f) :
    BanachSpectrum (algebra K A s g f) ≃ₜ locus K A s g f :=
  (isClosedEmbedding_spectrumMap K A s g f hunit).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_spectrumMap K A s g f hunit))

@[simp] theorem locusHomeomorph_apply_coe (hunit : GeneratesUnitIdeal K A g f)
    (x : BanachSpectrum (algebra K A s g f)) :
    (locusHomeomorph K A s g f hunit x).val = spectrumMap K A s g f x := rfl

/-- The inverse is the existing point lift constructed in its completed residue field. -/
theorem locusHomeomorph_symm_apply (hunit : GeneratesUnitIdeal K A g f)
    (x : locus K A s g f) :
    (locusHomeomorph K A s g f hunit).symm x =
      pointLift K A s g f hunit x.val x.property := by
  apply spectrumMap_injective K A s g f hunit
  exact (congrArg Subtype.val ((locusHomeomorph K A s g f hunit).apply_symm_apply x)).trans
    (spectrumMap_pointLift K A s g f hunit x.val x.property).symm

/-- The smaller-radius inequalities on the actual fraction coordinates of the
larger-radius quotient spectrum. -/
def fractionLocus : Set (BanachSpectrum (algebra K A s g f)) :=
  {x | ∀ j, x (fraction K A s g f j) ≤ t j}

theorem isClosed_fractionLocus : IsClosed (fractionLocus K A s t g f) := by
  simp only [fractionLocus, Set.ofPred_forall]
  exact isClosed_iInter fun j => isClosed_le
    (BanachSpectrum.evaluation (fraction K A s g f j)).continuous continuous_const

theorem isCompact_fractionLocus : IsCompact (fractionLocus K A s t g f) :=
  (isClosed_fractionLocus K A s t g f).isCompact

/-- At the original radii every quotient point satisfies the fraction bounds. -/
@[simp] theorem fractionLocus_self : fractionLocus K A s s g f = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x j
  exact (x.le_norm _).trans (norm_fraction_le K A s g f j)

/-- Generation makes the denominator value positive, so the base inequalities
are equivalent to the fraction-coordinate bounds. No ordering of the radii is needed. -/
theorem spectrumMap_mem_locus_iff (hunit : GeneratesUnitIdeal K A g f)
    (x : BanachSpectrum (algebra K A s g f)) :
    spectrumMap K A s g f x ∈ locus K A t g f ↔ x ∈ fractionLocus K A s t g f := by
  have hgpos : 0 < x (baseMap K A s g f (presentationMap K A g)) :=
    lt_of_le_of_ne (apply_nonneg x.toMulRingSeminorm _)
      (denominator_ne_zero K A s g f hunit (spectrumMap K A s g f x)
        (spectrumMap_mem_locus K A s g f x)).symm
  have heq (j : Fin m) :
      x (baseMap K A s g f (presentationMap K A g)) * x (fraction K A s g f j) =
        x (baseMap K A s g f (presentationMap K A (f j))) := by
    rw [← map_mul]
    exact congrArg x (fraction_equation K A s g f j)
  constructor
  · intro hx j
    apply (mul_le_mul_iff_right₀ hgpos).mp
    rw [heq, mul_comm _ (t j)]
    exact hx j
  · intro hx j
    change x (baseMap K A s g f (presentationMap K A (f j))) ≤
      t j * x (baseMap K A s g f (presentationMap K A g))
    rw [← heq, mul_comm (t j)]
    exact mul_le_mul_of_nonneg_left (hx j) hgpos.le

/-- The actual spectrum pullback for smaller radii is injective under generation. -/
theorem radiusSpectrumMap_injective (hunit : GeneratesUnitIdeal K A g f) :
    Function.Injective (radiusSpectrumMap K A s t hts g f) := by
  intro x y h
  apply spectrumMap_injective K A t g f hunit
  calc
    spectrumMap K A t g f x =
        spectrumMap K A s g f (radiusSpectrumMap K A s t hts g f x) :=
      (spectrumMap_radiusSpectrumMap K A s t hts g f x).symm
    _ = spectrumMap K A s g f (radiusSpectrumMap K A s t hts g f y) :=
      congrArg (spectrumMap K A s g f) h
    _ = spectrumMap K A t g f y :=
      spectrumMap_radiusSpectrumMap K A s t hts g f y

theorem isClosedEmbedding_radiusSpectrumMap (hunit : GeneratesUnitIdeal K A g f) :
    Topology.IsClosedEmbedding (radiusSpectrumMap K A s t hts g f) :=
  (radiusSpectrumMap K A s t hts g f).continuous.isClosedEmbedding
    (radiusSpectrumMap_injective K A s t hts g f hunit)

/-- The smaller quotient spectrum has exactly the base points satisfying the
smaller inequalities, viewed inside the larger quotient spectrum. -/
theorem range_radiusSpectrumMap_eq_preimage (hunit : GeneratesUnitIdeal K A g f) :
    Set.range (radiusSpectrumMap K A s t hts g f) =
      (spectrumMap K A s g f) ⁻¹' locus K A t g f :=
  range_eq_preimage_of_injective
    (spectrumMap K A s g f) (radiusSpectrumMap K A s t hts g f)
    (spectrumMap K A t g f) (locus K A t g f)
    (spectrumMap_injective K A s g f hunit)
    (spectrumMap_radiusSpectrumMap K A s t hts g f)
    (range_spectrumMap K A t g f hunit)

/-- The exact spectrum image is the closed fraction-coordinate inequality locus. -/
theorem range_radiusSpectrumMap (hunit : GeneratesUnitIdeal K A g f) :
    Set.range (radiusSpectrumMap K A s t hts g f) = fractionLocus K A s t g f := by
  rw [range_radiusSpectrumMap_eq_preimage K A s t hts g f hunit]
  ext x
  exact spectrumMap_mem_locus_iff K A s t g f hunit x

/-- Realize the smaller-radius quotient spectrum as the actual closed
fraction-inequality subspace in the larger-radius quotient spectrum. -/
def radiusSpectrumHomeomorph (hunit : GeneratesUnitIdeal K A g f) :
    BanachSpectrum (algebra K A t g f) ≃ₜ fractionLocus K A s t g f :=
  (isClosedEmbedding_radiusSpectrumMap K A s t hts g f hunit).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_radiusSpectrumMap K A s t hts g f hunit))

@[simp] theorem radiusSpectrumHomeomorph_apply_coe (hunit : GeneratesUnitIdeal K A g f)
    (x : BanachSpectrum (algebra K A t g f)) :
    (radiusSpectrumHomeomorph K A s t hts g f hunit x).val =
      radiusSpectrumMap K A s t hts g f x := rfl

@[simp] theorem radiusSpectrumMap_radiusSpectrumHomeomorph_symm
    (hunit : GeneratesUnitIdeal K A g f) (x : fractionLocus K A s t g f) :
    radiusSpectrumMap K A s t hts g f
      ((radiusSpectrumHomeomorph K A s t hts g f hunit).symm x) = x.val :=
  congrArg Subtype.val ((radiusSpectrumHomeomorph K A s t hts g f hunit).apply_symm_apply x)

/-- The continuous inclusion between the nested base inequality subspaces. -/
def radiusLocusInclusion : C(locus K A t g f, locus K A s g f) where
  toFun x := ⟨x.val, locus_mono K A s t hts g f x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp] theorem radiusLocusInclusion_apply_coe (x : locus K A t g f) :
    (radiusLocusInclusion K A s t hts g f x).val = x.val := rfl

theorem isClosedEmbedding_radiusLocusInclusion :
    Topology.IsClosedEmbedding (radiusLocusInclusion K A s t hts g f) := by
  let : CompactSpace (locus K A t g f) :=
    isCompact_iff_compactSpace.mp (isCompact_locus K A t g f)
  exact (radiusLocusInclusion K A s t hts g f).continuous.isClosedEmbedding
    (fun x y h => Subtype.ext (congrArg (fun z : locus K A s g f => z.val) h))

/-- Under the actual spectrum identifications, radius pullback is the ordinary
inclusion of the nested rational inequality subspaces. -/
theorem locusHomeomorph_radiusSpectrumMap (hunit : GeneratesUnitIdeal K A g f)
    (x : BanachSpectrum (algebra K A t g f)) :
    locusHomeomorph K A s g f hunit (radiusSpectrumMap K A s t hts g f x) =
      radiusLocusInclusion K A s t hts g f (locusHomeomorph K A t g f hunit x) := by
  apply Subtype.ext
  exact spectrumMap_radiusSpectrumMap K A s t hts g f x

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation
