import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeUnitAnnulusOverlapStatement

/-! # Closed principal presentation of the actual binary overlap -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : PresentedAffinoidAlgebra K) (f : A)

/-- The published coefficient evaluation is the existing overlap projection. -/
theorem toOverlapSeries_eq_quotientMap :
    toOverlapSeries K A f =
      RelativeRelations.quotientMap K A (PositivePolyradius.unit (Fin 2))
        (BinaryLaurent.overlapEquations K A f) := by
  apply relative_hom_ext (PositivePolyradius.unit (Fin 2))
  · intro a
    exact toOverlapSeries_constant K A f a
  · intro i
    rw [toOverlapSeries_X]
    fin_cases i <;> rfl

/-- The canonical map is the overlap projection on annulus representatives. -/
theorem toOverlap_quotientMap_eq
    (h : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin 2)) A) :
    toOverlap K A f (quotientMap K A h) =
      RelativeRelations.quotientMap K A (PositivePolyradius.unit (Fin 2))
        (BinaryLaurent.overlapEquations K A f) h := by
  change toOverlapSeries K A f h = _
  rw [toOverlapSeries_eq_quotientMap]

/-- Every actual overlap element has an annulus preimage. -/
theorem toOverlap_surjective : Function.Surjective (toOverlap K A f) := by
  intro o
  obtain ⟨h, rfl⟩ := RelativeRelations.quotientMap_surjective K A
    (PositivePolyradius.unit (Fin 2)) (BinaryLaurent.overlapEquations K A f) o
  exact ⟨quotientMap K A h, toOverlap_quotientMap_eq K A f h⟩

/-- The closed principal relation is the exact kernel for the original carriers. -/
theorem ker_toOverlap :
    RingHom.ker (toOverlap K A f).toAlgHom =
      (Ideal.span ({annulusX K A - baseMap K A f} : Set (Algebra K A))).closure := by
  apply le_antisymm
  · intro z hz
    let J : Ideal (Algebra K A) :=
      (Ideal.span ({annulusX K A - baseMap K A f} : Set (Algebra K A))).closure
    let : IsClosed (J : Set (Algebra K A)) := isClosed_closure
    let q : BoundedAlgHom K (Algebra K A) ((Algebra K A) ⧸ J) :=
      BoundedAlgHom.quotientMap K J
    let φ := q.comp (quotientMap K A)
    have hg : q (annulusX K A - baseMap K A f) = 0 := by
      change Ideal.Quotient.mk J (annulusX K A - baseMap K A f) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact subset_closure (Ideal.subset_span (Set.mem_singleton _))
    have hX : q (annulusX K A) = q (baseMap K A f) := by
      change q.toAlgHom (annulusX K A - baseMap K A f) = 0 at hg
      rwa [map_sub, sub_eq_zero] at hg
    have hE : ∀ h ∈ BinaryLaurent.overlapEquations K A f, φ h = 0 := by
      intro h hh
      rw [BinaryLaurent.overlapEquations, Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rcases hh with rfl | rfl
      · change q.toAlgHom ((quotientMap K A).toAlgHom
          (X (PositivePolyradius.unit (Fin 2)) A 0 -
            constantAlgHom (PositivePolyradius.unit (Fin 2)) K A f)) = 0
        rw [map_sub, map_sub]
        exact sub_eq_zero.mpr hX
      · change q.toAlgHom ((quotientMap K A).toAlgHom
          (constantAlgHom (PositivePolyradius.unit (Fin 2)) K A f *
            X (PositivePolyradius.unit (Fin 2)) A 1 - 1)) = 0
        rw [map_sub, map_mul, map_one, map_sub, map_mul, map_one]
        change q (baseMap K A f) * q (annulusY K A) - 1 = 0
        rw [← hX, ← map_mul, annulusX_mul_annulusY, map_one, sub_self]
    let χ := RelativeRelations.descend K A (PositivePolyradius.unit (Fin 2))
      (BinaryLaurent.overlapEquations K A f) ((Algebra K A) ⧸ J) φ hE
    have hχ : χ (toOverlap K A f z) = q z := by
      obtain ⟨h, rfl⟩ := quotientMap_surjective K A z
      rw [toOverlap_quotientMap_eq]
      rfl
    change toOverlap K A f z = 0 at hz
    rw [hz, map_zero] at hχ
    change z ∈ J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hχ.symm
  · intro z hz
    change toOverlap K A f z = 0
    exact (toOverlap K A f).annihilates_closure
      (Ideal.span ({annulusX K A - baseMap K A f} : Set (Algebra K A)))
      (Ideal.span_le.mpr (by
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst a
        change (toOverlap K A f).toAlgHom (annulusX K A - baseMap K A f) = 0
        rw [map_sub, toOverlap_annulusX, toOverlap_baseMap,
          BinaryLaurent.overlapX_eq, sub_self]) :
        Ideal.span ({annulusX K A - baseMap K A f} : Set (Algebra K A)) ≤
          RingHom.ker (toOverlap K A f).toAlgHom) z hz

/-- Overlap elements lift with arbitrarily small excess for the given quotient norms. -/
theorem exists_toOverlap_norm_lt (o : BinaryLaurent.Overlap K A f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : Algebra K A, toOverlap K A f z = o ∧ ‖z‖ < ‖o‖ + ε := by
  obtain ⟨h, hh, hnorm⟩ := RelativeRelations.exists_representative_norm_lt K A
    (PositivePolyradius.unit (Fin 2)) (BinaryLaurent.overlapEquations K A f) o hε
  exact ⟨quotientMap K A h, (toOverlap_quotientMap_eq K A f h).trans hh,
    (norm_quotientMap_le K A h).trans_lt hnorm⟩

/-- The actual overlap is the closed principal quotient of the actual unit annulus. -/
theorem overlap_presentation : OverlapPresentationStatement.{u} := by
  intro K _ _ _ A f
  exact ⟨toOverlap_surjective K A f, ker_toOverlap K A f,
    fun o _ hε => exists_toOverlap_norm_lt K A f o hε⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.RelativeUnitAnnulus
