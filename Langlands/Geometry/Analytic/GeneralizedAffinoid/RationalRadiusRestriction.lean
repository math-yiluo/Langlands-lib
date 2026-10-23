import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalPresentation
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.RadiusRestriction

/-! # Radius restriction of weighted rational quotients -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s t : PositivePolyradius (Fin m))
  (hts : ∀ j, t j ≤ s j)
  (g : GeneralizedTateAlgebra A.polyradius K)
  (f : Fin m → GeneralizedTateAlgebra A.polyradius K)

private def restrictSeries :
    BoundedAlgHom K (GeneralizedTateAlgebra (A.polyradius.append s) K)
      (GeneralizedTateAlgebra (A.polyradius.append t) K) :=
  boundedRestrictRadius (A.polyradius.append s) (A.polyradius.append t)
    (A.polyradius.append_mono A.polyradius s t (fun _ => le_rfl) hts) K

private theorem restrictSeries_appendLeft (h : GeneralizedTateAlgebra A.polyradius K) :
    restrictSeries K A s t hts (appendLeft A.polyradius s K h) =
      appendLeft A.polyradius t K h :=
  congrArg (fun φ => φ h) (boundedRestrictRadius_appendLeft K A.polyradius s t hts)

private theorem restrictSeries_X (i : Fin (A.arity + m)) :
    restrictSeries K A s t hts (X (A.polyradius.append s) K i) =
      X (A.polyradius.append t) K i :=
  restrictRadius_X (A.polyradius.append s) (A.polyradius.append t)
    (A.polyradius.append_mono A.polyradius s t (fun _ => le_rfl) hts) K i

private theorem norm_restrictSeries_le
    (h : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    ‖restrictSeries K A s t hts h‖ ≤ ‖h‖ :=
  norm_restrictRadius_le (A.polyradius.append s) (A.polyradius.append t)
    (A.polyradius.append_mono A.polyradius s t (fun _ => le_rfl) hts) K h

private theorem radius_relations_vanish :
    ∀ h ∈ Adjoin.relations K A s (equations K A s g f),
      ((presentationMap K (algebra K A t g f)).comp
        (restrictSeries K A s t hts)) h = 0 := by
  intro h hh
  rcases hh with ⟨a, ha, rfl⟩ | ⟨j, rfl⟩
  · change presentationMap K (algebra K A t g f)
      (restrictSeries K A s t hts (appendLeft A.polyradius s K a)) = 0
    rw [restrictSeries_appendLeft]
    rw [← baseMap_presentationMap, (presentationMap_eq_zero_iff K A a).mpr ha]
    exact map_zero (baseMap K A t g f).toAlgHom
  · change presentationMap K (algebra K A t g f)
      ((restrictSeries K A s t hts).toAlgHom
        (appendLeft A.polyradius s K g *
          X (A.polyradius.append s) K (Fin.natAdd A.arity j) -
            appendLeft A.polyradius s K (f j))) = 0
    rw [map_sub, map_mul]
    change presentationMap K (algebra K A t g f)
      (restrictSeries K A s t hts (appendLeft A.polyradius s K g) *
        restrictSeries K A s t hts (X (A.polyradius.append s) K (Fin.natAdd A.arity j)) -
          restrictSeries K A s t hts (appendLeft A.polyradius s K (f j))) = 0
    rw [restrictSeries_appendLeft, restrictSeries_appendLeft, restrictSeries_X]
    exact Adjoin.presentationMap_equation K A t (equations K A t g f)
      (Set.mem_range_self j)

/-- Shrinking only the newly adjoined radii induces a bounded map of the actual
closed rational quotients, with the base presentation and representatives fixed. -/
def radiusMap : BoundedAlgHom K (algebra K A s g f) (algebra K A t g f) :=
  descendRelations K (A.arity + m) (A.polyradius.append s)
    (Adjoin.relations K A s (equations K A s g f)) (algebra K A t g f)
    ((presentationMap K (algebra K A t g f)).comp (restrictSeries K A s t hts))
    (radius_relations_vanish K A s t hts g f)

@[simp] theorem radiusMap_presentationMap
    (h : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    radiusMap K A s t hts g f (presentationMap K (algebra K A s g f) h) =
      presentationMap K (algebra K A t g f)
        (restrictRadius (A.polyradius.append s) (A.polyradius.append t)
          (A.polyradius.append_mono A.polyradius s t (fun _ => le_rfl) hts) K h) := rfl

/-- The map contracts the actual quotient norm. -/
theorem norm_radiusMap_le (a : algebra K A s g f) :
    ‖radiusMap K A s t hts g f a‖ ≤ ‖a‖ := by
  have h := norm_descendRelations_le K (A.arity + m) (A.polyradius.append s)
    (Adjoin.relations K A s (equations K A s g f)) (algebra K A t g f)
    ((presentationMap K (algebra K A t g f)).comp (restrictSeries K A s t hts))
    (radius_relations_vanish K A s t hts g f) 1 zero_lt_one
    (fun h => by
      change ‖presentationMap K (algebra K A t g f) (restrictSeries K A s t hts h)‖ ≤
        1 * ‖h‖
      rw [one_mul]
      exact (norm_presentationMap_le K (algebra K A t g f) _).trans
        (norm_restrictSeries_le K A s t hts h)) a
  change ‖radiusMap K A s t hts g f a‖ ≤ 1 * ‖a‖ at h
  simpa only [one_mul] using h

@[simp] theorem radiusMap_baseMap (a : A) :
    radiusMap K A s t hts g f (baseMap K A s g f a) = baseMap K A t g f a := by
  obtain ⟨h, rfl⟩ := presentationMap_surjective K A a
  change presentationMap K (algebra K A t g f)
    (restrictSeries K A s t hts (appendLeft A.polyradius s K h)) =
      presentationMap K (algebra K A t g f) (appendLeft A.polyradius t K h)
  rw [restrictSeries_appendLeft]

@[simp] theorem radiusMap_fraction (j : Fin m) :
    radiusMap K A s t hts g f (fraction K A s g f j) = fraction K A t g f j := by
  change presentationMap K (algebra K A t g f)
    (restrictSeries K A s t hts (X (A.polyradius.append s) K (Fin.natAdd A.arity j))) =
      presentationMap K (algebra K A t g f) (X (A.polyradius.append t) K _)
  rw [restrictSeries_X]

@[simp] theorem radiusMap_self :
    radiusMap K A s s (fun _ => le_rfl) g f = BoundedAlgHom.id K (algebra K A s g f) := by
  apply hom_ext_presentation
  intro h
  change GeneralizedTateAlgebra (A.polyradius.append s) K at h
  rw [radiusMap_presentationMap K A s s (fun _ => le_rfl) g f h, restrictRadius_self]
  rfl

/-- Successive radius restrictions agree with direct restriction. -/
theorem radiusMap_trans (v : PositivePolyradius (Fin m)) (hvt : ∀ j, v j ≤ t j) :
    (radiusMap K A t v hvt g f).comp (radiusMap K A s t hts g f) =
      radiusMap K A s v (fun j => (hvt j).trans (hts j)) g f := by
  apply hom_ext_presentation
  intro h
  change GeneralizedTateAlgebra (A.polyradius.append s) K at h
  change radiusMap K A t v hvt g f
    (radiusMap K A s t hts g f (presentationMap K (algebra K A s g f) h)) = _
  rw [radiusMap_presentationMap K A s t hts g f h,
    radiusMap_presentationMap K A t v hvt g f,
    radiusMap_presentationMap K A s v (fun j => (hvt j).trans (hts j)) g f h,
    restrictRadius_trans]

/-- The corresponding continuous spectrum map has the contravariant direction. -/
def radiusSpectrumMap :
    C(BanachSpectrum (algebra K A t g f), BanachSpectrum (algebra K A s g f)) :=
  BanachSpectrum.comapContinuous (radiusMap K A s t hts g f).toBoundedRingHom

@[simp] theorem spectrumMap_radiusSpectrumMap (x : BanachSpectrum (algebra K A t g f)) :
    spectrumMap K A s g f (radiusSpectrumMap K A s t hts g f x) =
      spectrumMap K A t g f x := by
  apply BanachSpectrum.ext
  intro a
  change x (radiusMap K A s t hts g f (baseMap K A s g f a)) =
    x (baseMap K A t g f a)
  rw [radiusMap_baseMap]

include hts in
/-- Smaller radii give nested weighted rational inequality loci. -/
theorem locus_mono : locus K A t g f ⊆ locus K A s g f := by
  intro x hx j
  exact (hx j).trans (mul_le_mul_of_nonneg_right (hts j)
    (apply_nonneg x.toMulRingSeminorm _))

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation
