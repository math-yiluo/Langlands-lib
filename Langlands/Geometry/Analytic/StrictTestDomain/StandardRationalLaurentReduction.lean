import Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalCover
import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentCover
import Langlands.Geometry.Analytic.StrictTestDomain.RationalRelativeComparison

/-! # Scalar Laurent reduction of a standard rational cover -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.StandardRationalLaurentReduction

open RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K} {n : ℕ}

/-- The actual scalar Laurent function chosen from the last tuple entry. -/
def scalarFunction (f : Fin (n + 1) → P) (c : K) : P :=
  algebraMap K P c⁻¹ * f (Fin.last n)

/-- The actual upper rational input. -/
def upper (f : Fin (n + 1) → P) (c : K) : RationalData K P :=
  laurentUpper (scalarFunction f c)

/-- The actual lower rational input. -/
def lower (f : Fin (n + 1) → P) (c : K) : RationalData K P :=
  laurentLower (scalarFunction f c)

/-- The overlap uses the existing rational intersection. -/
def overlap (f : Fin (n + 1) → P) (c : K) : RationalData K P :=
  (upper f c).inter (lower f c)

/-- Remove exactly the last entry after mapping to the actual upper quotient. -/
def shortened (f : Fin (n + 1) → P) (c : K) :
    Fin n → (upper f c).algebra :=
  fun j => (upper f c).baseMap (f j.castSucc)

variable (f : Fin (n + 1) → P) (c : K)

omit [CompleteSpace K] in
theorem scalarFunction_apply (x : BanachSpectrum P) :
    x (scalarFunction f c) = ‖c‖⁻¹ * x (f (Fin.last n)) := by
  change x.toMulRingSeminorm (algebraMap K P c⁻¹ * f (Fin.last n)) = _
  rw [map_mul]
  rw [BanachSpectrum.algebraMap_apply, norm_inv]

omit [CompleteSpace K] in
theorem mem_upper_iff (hc : c ≠ 0) (x : BanachSpectrum P) :
    x ∈ (upper f c).locus ↔ x (f (Fin.last n)) ≤ ‖c‖ := by
  rw [upper, mem_locus_laurentUpper, scalarFunction_apply,
    inv_mul_le_iff₀ (norm_pos_iff.mpr hc), mul_one]

theorem upper_last_le (hc : c ≠ 0) (x : BanachSpectrum (upper f c).algebra) :
    x ((upper f c).baseMap (f (Fin.last n))) ≤ ‖c‖ :=
  (mem_upper_iff f c hc _).mp ((upper f c).baseMap_hasImageIn x)

variable (hc : c ≠ 0)
  (hthreshold : ∀ x : BanachSpectrum P, ∃ j, ‖c‖ < x (f j))

include hc hthreshold in
/-- The shortened tuple still has an entry strictly above the same scalar
threshold at every actual point of the upper quotient. -/
theorem shortened_threshold (x : BanachSpectrum (upper f c).algebra) :
    ∃ j, ‖c‖ < x (shortened f c j) := by
  obtain ⟨k, hk⟩ := hthreshold (BanachSpectrum.comap (upper f c).baseMap.toBoundedRingHom x)
  have hne : k ≠ Fin.last n := by
    intro he
    subst k
    exact (not_lt_of_ge (upper_last_le f c hc x)) hk
  obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hne
  exact ⟨j, hk⟩

include hc hthreshold in
theorem shortened_no_common_zero :
    ∀ x : BanachSpectrum (upper f c).algebra,
      ∃ j, x (shortened f c j) ≠ 0 := by
  intro x
  obtain ⟨j, hj⟩ := shortened_threshold f c hc hthreshold x
  exact ⟨j, ne_of_gt ((norm_nonneg c).trans_lt hj)⟩

variable (hf : ∀ x : BanachSpectrum P, ∃ j, x (f j) ≠ 0)

include hc hthreshold in
theorem last_pullback_locus_empty :
    ((standardRational f hf (Fin.last n)).pullback (upper f c).baseMap).locus = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨j, hj⟩ := shortened_threshold f c hc hthreshold x
  have hle : x (shortened f c j) ≤
      x ((upper f c).baseMap (f (Fin.last n))) := hx j.castSucc
  exact (not_lt_of_ge (hle.trans (upper_last_le f c hc x))) hj

include hc hthreshold in
theorem last_pullback_subsingleton :
    Subsingleton
      ((standardRational f hf (Fin.last n)).pullback (upper f c).baseMap).algebra :=
  subsingleton_algebra_of_locus_empty _
    (last_pullback_locus_empty f c hc hthreshold hf)

/-- The shortened standard datum over the actual upper quotient. -/
def shortStandard (j : Fin n) : RationalData K (upper f c).algebra :=
  standardRational (shortened f c) (shortened_no_common_zero f c hc hthreshold) j

include hc hthreshold in
theorem shortStandard_locus (j : Fin n) :
    ((standardRational f hf j.castSucc).pullback (upper f c).baseMap).locus =
      (shortStandard f c hc hthreshold j).locus := by
  ext x
  constructor
  · intro hx k
    exact hx k.castSucc
  · intro hx k
    change x ((upper f c).baseMap (f k)) ≤ x (shortened f c j)
    refine Fin.lastCases ?_ (fun i => hx i) k
    obtain ⟨i, hi⟩ := shortened_threshold f c hc hthreshold x
    exact (upper_last_le f c hc x).trans (hi.le.trans (hx i))

section EqualLoci

variable {B : PresentedStrictAffinoidAlgebra K} {d e : RationalData K B}

/-- The actual bounded map between two rational quotients with equal loci. -/
def locusMap (h : d.locus = e.locus) : BoundedAlgHom K d.algebra e.algebra :=
  (⟨h.symm.subset⟩ : Inclusion e d).restriction

@[simp]
theorem locusMap_comp_baseMap (h : d.locus = e.locus) :
    (locusMap h).comp d.baseMap = e.baseMap :=
  Inclusion.restriction_comp_baseMap _

@[simp]
theorem locusMap_symm_comp (h : d.locus = e.locus) :
    (locusMap h.symm).comp (locusMap h) = BoundedAlgHom.id K d.algebra := by
  apply d.hom_ext
  rw [BoundedAlgHom.comp_assoc, locusMap_comp_baseMap,
    locusMap_comp_baseMap, BoundedAlgHom.id_comp]

/-- Equality of loci gives inverse bounded maps, using representability. -/
def locusEquiv (h : d.locus = e.locus) : BoundedAlgEquiv K d.algebra e.algebra :=
  BoundedAlgEquiv.ofHomInv (locusMap h) (locusMap h.symm)
    (fun a => congrArg (fun φ => φ a) (locusMap_symm_comp h))
    (fun a => congrArg (fun φ => φ a) (locusMap_symm_comp h.symm))

theorem locusMap_restriction {d' e' : RationalData K B}
    (hd : d.locus = d'.locus) (he : e.locus = e'.locus)
    (i : Inclusion d e) (i' : Inclusion d' e') :
    (locusMap hd).comp i.restriction =
      i'.restriction.comp (locusMap he) := by
  apply e.hom_ext
  rw [BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap,
    locusMap_comp_baseMap, BoundedAlgHom.comp_assoc, locusMap_comp_baseMap,
    Inclusion.restriction_comp_baseMap]

theorem inter_locus_eq {d' e' : RationalData K B}
    (hd : d.locus = d'.locus) (he : e.locus = e'.locus) :
    (d.inter e).locus = (d'.inter e').locus := by
  rw [locus_inter, locus_inter, hd, he]

end EqualLoci

/-- Each retained original standard datum pulled back to the upper quotient. -/
abbrev upperStandard (j : Fin (n + 1)) : RationalData K (upper f c).algebra :=
  (standardRational f hf j).pullback (upper f c).baseMap

/-- The bounded comparison from a retained pulled-back quotient to the
shortened standard quotient. -/
def toShort (j : Fin n) :
    BoundedAlgHom K (upperStandard f c hf j.castSucc).algebra
      (shortStandard f c hc hthreshold j).algebra :=
  locusMap (shortStandard_locus f c hc hthreshold hf j)

/-- The bounded inverse, between the same actual quotients. -/
def fromShort (j : Fin n) :
    BoundedAlgHom K (shortStandard f c hc hthreshold j).algebra
      (upperStandard f c hf j.castSucc).algebra :=
  locusMap (shortStandard_locus f c hc hthreshold hf j).symm

theorem toShort_comp_baseMap (j : Fin n) :
    (toShort f c hc hthreshold hf j).comp
        (upperStandard f c hf j.castSucc).baseMap =
      (shortStandard f c hc hthreshold j).baseMap :=
  locusMap_comp_baseMap _

theorem fromShort_comp_baseMap (j : Fin n) :
    (fromShort f c hc hthreshold hf j).comp
        (shortStandard f c hc hthreshold j).baseMap =
      (upperStandard f c hf j.castSucc).baseMap :=
  locusMap_comp_baseMap _

@[simp]
theorem fromShort_comp_toShort (j : Fin n) :
    (fromShort f c hc hthreshold hf j).comp (toShort f c hc hthreshold hf j) =
      BoundedAlgHom.id K (upperStandard f c hf j.castSucc).algebra :=
  locusMap_symm_comp _

@[simp]
theorem toShort_comp_fromShort (j : Fin n) :
    (toShort f c hc hthreshold hf j).comp (fromShort f c hc hthreshold hf j) =
      BoundedAlgHom.id K (shortStandard f c hc hthreshold j).algebra :=
  locusMap_symm_comp (shortStandard_locus f c hc hthreshold hf j).symm

def shortEquiv (j : Fin n) :
    BoundedAlgEquiv K (upperStandard f c hf j.castSucc).algebra
      (shortStandard f c hc hthreshold j).algebra :=
  locusEquiv (shortStandard_locus f c hc hthreshold hf j)

/-- The coefficient square from the original standard quotient to the
shortened quotient is the composite of the existing bounded comparison. -/
def upperComparison (j : Fin n) :
    BoundedAlgHom K (standardRational f hf j.castSucc).algebra
      (shortStandard f c hc hthreshold j).algebra :=
  (toShort f c hc hthreshold hf j).comp
    ((standardRational f hf j.castSucc).comparison (upper f c).baseMap)

theorem upperComparison_comp_baseMap (j : Fin n) :
    (upperComparison f c hc hthreshold hf j).comp
        (standardRational f hf j.castSucc).baseMap =
      (shortStandard f c hc hthreshold j).baseMap.comp (upper f c).baseMap := by
  rw [upperComparison, BoundedAlgHom.comp_assoc, comparison_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, toShort_comp_baseMap]

/-- The intersection comparison between the retained upper cover and its
shortened cover, with the actual chosen intersection presentations. -/
def overlapToShort (j k : Fin n) :
    BoundedAlgHom K
      ((upperStandard f c hf j.castSucc).inter
        (upperStandard f c hf k.castSucc)).algebra
      ((shortStandard f c hc hthreshold j).inter
        (shortStandard f c hc hthreshold k)).algebra :=
  locusMap (inter_locus_eq (shortStandard_locus f c hc hthreshold hf j)
    (shortStandard_locus f c hc hthreshold hf k))

def overlapFromShort (j k : Fin n) :
    BoundedAlgHom K
      ((shortStandard f c hc hthreshold j).inter
        (shortStandard f c hc hthreshold k)).algebra
      ((upperStandard f c hf j.castSucc).inter
        (upperStandard f c hf k.castSucc)).algebra :=
  locusMap (inter_locus_eq (shortStandard_locus f c hc hthreshold hf j)
    (shortStandard_locus f c hc hthreshold hf k)).symm

theorem overlapToShort_comp_left (j k : Fin n) :
    (overlapToShort f c hc hthreshold hf j k).comp
        (interLeft (upperStandard f c hf j.castSucc)
          (upperStandard f c hf k.castSucc)).restriction =
      (interLeft (shortStandard f c hc hthreshold j)
        (shortStandard f c hc hthreshold k)).restriction.comp
          (toShort f c hc hthreshold hf j) :=
  locusMap_restriction _ _ _ _

theorem overlapToShort_comp_right (j k : Fin n) :
    (overlapToShort f c hc hthreshold hf j k).comp
        (interRight (upperStandard f c hf j.castSucc)
          (upperStandard f c hf k.castSucc)).restriction =
      (interRight (shortStandard f c hc hthreshold j)
        (shortStandard f c hc hthreshold k)).restriction.comp
          (toShort f c hc hthreshold hf k) :=
  locusMap_restriction _ _ _ _

theorem overlapFromShort_comp_left (j k : Fin n) :
    (overlapFromShort f c hc hthreshold hf j k).comp
        (interLeft (shortStandard f c hc hthreshold j)
          (shortStandard f c hc hthreshold k)).restriction =
      (interLeft (upperStandard f c hf j.castSucc)
        (upperStandard f c hf k.castSucc)).restriction.comp
          (fromShort f c hc hthreshold hf j) :=
  locusMap_restriction _ _ _ _

theorem overlapFromShort_comp_right (j k : Fin n) :
    (overlapFromShort f c hc hthreshold hf j k).comp
        (interRight (shortStandard f c hc hthreshold j)
          (shortStandard f c hc hthreshold k)).restriction =
      (interRight (upperStandard f c hf j.castSucc)
        (upperStandard f c hf k.castSucc)).restriction.comp
          (fromShort f c hc hthreshold hf k) :=
  locusMap_restriction _ _ _ _

@[simp]
theorem overlapFromShort_comp_overlapToShort (j k : Fin n) :
    (overlapFromShort f c hc hthreshold hf j k).comp
        (overlapToShort f c hc hthreshold hf j k) =
      BoundedAlgHom.id K
        ((upperStandard f c hf j.castSucc).inter
          (upperStandard f c hf k.castSucc)).algebra :=
  locusMap_symm_comp _

@[simp]
theorem overlapToShort_comp_overlapFromShort (j k : Fin n) :
    (overlapToShort f c hc hthreshold hf j k).comp
        (overlapFromShort f c hc hthreshold hf j k) =
      BoundedAlgHom.id K
        ((shortStandard f c hc hthreshold j).inter
          (shortStandard f c hc hthreshold k)).algebra :=
  locusMap_symm_comp
    (inter_locus_eq (shortStandard_locus f c hc hthreshold hf j)
      (shortStandard_locus f c hc hthreshold hf k)).symm

/-- Map the original pairwise overlap to the shortened actual overlap. -/
def upperOverlapComparison (j k : Fin n) :
    BoundedAlgHom K
      ((standardRational f hf j.castSucc).inter
        (standardRational f hf k.castSucc)).algebra
      ((shortStandard f c hc hthreshold j).inter
        (shortStandard f c hc hthreshold k)).algebra :=
  (overlapToShort f c hc hthreshold hf j k).comp
    (intersectionComparison (standardRational f hf j.castSucc)
      (standardRational f hf k.castSucc) (upper f c).baseMap)

theorem upperOverlapComparison_comp_left (j k : Fin n) :
    (upperOverlapComparison f c hc hthreshold hf j k).comp
        (interLeft (standardRational f hf j.castSucc)
          (standardRational f hf k.castSucc)).restriction =
      (interLeft (shortStandard f c hc hthreshold j)
        (shortStandard f c hc hthreshold k)).restriction.comp
          (upperComparison f c hc hthreshold hf j) := by
  rw [upperOverlapComparison, BoundedAlgHom.comp_assoc,
    intersectionComparison_comp_left, ← BoundedAlgHom.comp_assoc,
    overlapToShort_comp_left, BoundedAlgHom.comp_assoc, upperComparison]

theorem upperOverlapComparison_comp_right (j k : Fin n) :
    (upperOverlapComparison f c hc hthreshold hf j k).comp
        (interRight (standardRational f hf j.castSucc)
          (standardRational f hf k.castSucc)).restriction =
      (interRight (shortStandard f c hc hthreshold j)
        (shortStandard f c hc hthreshold k)).restriction.comp
          (upperComparison f c hc hthreshold hf k) := by
  rw [upperOverlapComparison, BoundedAlgHom.comp_assoc,
    intersectionComparison_comp_right, ← BoundedAlgHom.comp_assoc,
    overlapToShort_comp_right, BoundedAlgHom.comp_assoc, upperComparison]

/-- Compatible original sections restrict to compatible shortened sections. -/
theorem upperComparison_compatible (s : ∀ j, (standardRational f hf j).algebra)
    (hs : ∀ j k, (interLeft (standardRational f hf j)
      (standardRational f hf k)).restriction (s j) =
        (interRight (standardRational f hf j)
          (standardRational f hf k)).restriction (s k)) :
    ∀ j k, (interLeft (shortStandard f c hc hthreshold j)
      (shortStandard f c hc hthreshold k)).restriction
        (upperComparison f c hc hthreshold hf j (s j.castSucc)) =
      (interRight (shortStandard f c hc hthreshold j)
        (shortStandard f c hc hthreshold k)).restriction
          (upperComparison f c hc hthreshold hf k (s k.castSucc)) := by
  intro j k
  have hl := congrArg (fun φ => φ (s j.castSucc))
    (upperOverlapComparison_comp_left f c hc hthreshold hf j k)
  have hr := congrArg (fun φ => φ (s k.castSucc))
    (upperOverlapComparison_comp_right f c hc hthreshold hf j k)
  exact hl.symm.trans ((congrArg (upperOverlapComparison f c hc hthreshold hf j k)
    (hs j.castSucc k.castSucc)).trans hr)

/-- The lift conditions for the whole pulled-back cover are exactly those
for the shortened cover; the omitted component is the zero quotient. -/
theorem upper_lift_iff
    (s : ∀ j, (upperStandard f c hf j).algebra) (a : (upper f c).algebra) :
    (∀ j, (upperStandard f c hf j).baseMap a = s j) ↔
      ∀ j, (shortStandard f c hc hthreshold j).baseMap a =
        toShort f c hc hthreshold hf j (s j.castSucc) := by
  constructor
  · intro ha j
    have h := congrArg (toShort f c hc hthreshold hf j) (ha j.castSucc)
    exact (congrArg (fun φ => φ a)
      (toShort_comp_baseMap f c hc hthreshold hf j)).symm.trans h
  · intro ha j
    refine Fin.lastCases ?_ ?_ j
    · let := last_pullback_subsingleton f c hc hthreshold hf
      exact Subsingleton.elim _ _
    · intro k
      apply (shortEquiv f c hc hthreshold hf k).injective
      exact (congrArg (fun φ => φ a)
        (toShort_comp_baseMap f c hc hthreshold hf k)).trans (ha k)

/-- This is transport of unique lifts, with no assertion that either lift
exists independently of the other. -/
theorem existsUnique_upper_lift_iff
    (s : ∀ j, (upperStandard f c hf j).algebra) :
    (∃! a : (upper f c).algebra, ∀ j,
      (upperStandard f c hf j).baseMap a = s j) ↔
    ∃! a : (upper f c).algebra, ∀ j,
      (shortStandard f c hc hthreshold j).baseMap a =
        toShort f c hc hthreshold hf j (s j.castSucc) := by
  simp_rw [upper_lift_iff f c hc hthreshold hf s]

/-- The chosen last entry is a unit in the actual lower quotient. -/
theorem lower_last_isUnit :
    IsUnit ((lower f c).baseMap (f (Fin.last n))) := by
  have hg : IsUnit ((lower f c).baseMap (scalarFunction f c)) :=
    RationalLocalization.isUnit_baseMap_denominator K P (lower f c).arity
      (lower f c).denominator (lower f c).numerator (lower f c).generatesUnitIdeal
  change IsUnit ((lower f c).baseMap (algebraMap K P c⁻¹ * f (Fin.last n))) at hg
  rw [map_mul] at hg
  exact isUnit_of_mul_isUnit_right hg

/-- The chosen last entry is a unit on the actual overlap as well. -/
theorem overlap_last_isUnit :
    IsUnit ((overlap f c).baseMap (f (Fin.last n))) := by
  have h := (lower_last_isUnit f c).map
    (interRight (upper f c) (lower f c)).restriction.toAlgHom.toMonoidHom
  have he := congrArg (fun φ => φ (f (Fin.last n)))
    (interRight (upper f c) (lower f c)).restriction_comp_baseMap
  exact he ▸ h

/-- All previously invertible entries remain invertible under every actual
rational base map, including the lower and overlap base maps. -/
theorem mapped_entry_isUnit (d : RationalData K P) (j : Fin (n + 1))
    (hj : IsUnit (f j)) : IsUnit (d.baseMap (f j)) :=
  hj.map d.baseMap.toAlgHom.toMonoidHom

/-- Lower standard inputs are exactly the pullbacks, on the actual quotient. -/
theorem lower_standard_pullback (j : Fin (n + 1)) :
    (standardRational f hf j).pullback (lower f c).baseMap =
      standardRational (fun k => (lower f c).baseMap (f k))
        (tuple_no_common_zero_pullback f hf (lower f c).baseMap) j := rfl

/-- Overlap standard inputs are exactly the pullbacks, on the actual quotient. -/
theorem overlap_standard_pullback (j : Fin (n + 1)) :
    (standardRational f hf j).pullback (overlap f c).baseMap =
      standardRational (fun k => (overlap f c).baseMap (f k))
        (tuple_no_common_zero_pullback f hf (overlap f c).baseMap) j := rfl

end Langlands.Analytic.StrictTestDomain.StandardRationalLaurentReduction
