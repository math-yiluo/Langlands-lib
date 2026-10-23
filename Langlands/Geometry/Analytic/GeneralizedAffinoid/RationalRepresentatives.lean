import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalPresentation
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Independence of weighted rational quotients from series representatives -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (g g' : GeneralizedTateAlgebra A.polyradius K)
  (f f' : Fin m → GeneralizedTateAlgebra A.polyradius K)
  (hg : presentationMap K A g = presentationMap K A g')
  (hf : ∀ j, presentationMap K A (f j) = presentationMap K A (f' j))

include hg hf

private theorem representative_relations_vanish :
    ∀ h ∈ Adjoin.relations K A s (equations K A s g f),
      presentationMap K (algebra K A s g' f') h = 0 := by
  intro h hh
  rcases hh with ⟨a, ha, rfl⟩ | ⟨j, rfl⟩
  · change baseMap K A s g' f' (presentationMap K A a) = 0
    rw [(presentationMap_eq_zero_iff K A a).mpr ha]
    exact map_zero (baseMap K A s g' f').toAlgHom
  · change (Ideal.Quotient.mk
      (Ideal.span (Adjoin.relations K A s (equations K A s g' f'))).closure)
      (appendLeft A.polyradius s K g *
        X (A.polyradius.append s) K (Fin.natAdd A.arity j) -
          appendLeft A.polyradius s K (f j)) = 0
    rw [map_sub, map_mul]
    change baseMap K A s g' f' (presentationMap K A g) * fraction K A s g' f' j -
      baseMap K A s g' f' (presentationMap K A (f j)) = 0
    rw [hg, hf j, fraction_equation, sub_self]

/-- Change only the denominator and numerator representatives, keeping every
projected enlarged series unchanged. -/
def representativeMap :
    BoundedAlgHom K (algebra K A s g f) (algebra K A s g' f') :=
  descendRelations K (A.arity + m) (A.polyradius.append s)
    (Adjoin.relations K A s (equations K A s g f)) (algebra K A s g' f')
    (presentationMap K (algebra K A s g' f'))
    (representative_relations_vanish K A s g g' f f' hg hf)

@[simp] theorem representativeMap_presentationMap
    (h : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    representativeMap K A s g g' f f' hg hf
      (presentationMap K (algebra K A s g f) h) =
        presentationMap K (algebra K A s g' f') h := rfl

/-- The comparison is contractive for the actual quotient norms. -/
theorem norm_representativeMap_le (a : algebra K A s g f) :
    ‖representativeMap K A s g g' f f' hg hf a‖ ≤ ‖a‖ := by
  have h := norm_descendRelations_le K (A.arity + m) (A.polyradius.append s)
    (Adjoin.relations K A s (equations K A s g f)) (algebra K A s g' f')
    (presentationMap K (algebra K A s g' f'))
    (representative_relations_vanish K A s g g' f f' hg hf) 1 zero_lt_one
    (fun h => by
      rw [one_mul]
      exact norm_presentationMap_le K (algebra K A s g' f') h) a
  change ‖representativeMap K A s g g' f f' hg hf a‖ ≤ 1 * ‖a‖ at h
  simpa only [one_mul] using h

@[simp] theorem representativeMap_baseMap (a : A) :
    representativeMap K A s g g' f f' hg hf (baseMap K A s g f a) =
      baseMap K A s g' f' a := by
  obtain ⟨h, rfl⟩ := presentationMap_surjective K A a
  rfl

@[simp] theorem representativeMap_fraction (j : Fin m) :
    representativeMap K A s g g' f f' hg hf (fraction K A s g f j) =
      fraction K A s g' f' j := rfl

@[simp] theorem representativeMap_inverse (a : algebra K A s g f) :
    representativeMap K A s g' g f' f hg.symm (fun j => (hf j).symm)
      (representativeMap K A s g g' f f' hg hf a) = a := by
  obtain ⟨h, rfl⟩ := presentationMap_surjective K (algebra K A s g f) a
  rfl

/-- The canonical bounded algebra equivalence for equal representative classes. -/
def representativeEquiv :
    BoundedAlgEquiv K (algebra K A s g f) (algebra K A s g' f') :=
  BoundedAlgEquiv.ofHomInv
    (representativeMap K A s g g' f f' hg hf)
    (representativeMap K A s g' g f' f hg.symm (fun j => (hf j).symm))
    (representativeMap_inverse K A s g g' f f' hg hf)
    (representativeMap_inverse K A s g' g f' f hg.symm (fun j => (hf j).symm))

@[simp] theorem representativeEquiv_presentationMap
    (h : GeneralizedTateAlgebra (A.polyradius.append s) K) :
    representativeEquiv K A s g g' f f' hg hf
      (presentationMap K (algebra K A s g f) h) =
        presentationMap K (algebra K A s g' f') h := rfl

@[simp] theorem representativeEquiv_baseMap (a : A) :
    representativeEquiv K A s g g' f f' hg hf (baseMap K A s g f a) =
      baseMap K A s g' f' a :=
  representativeMap_baseMap K A s g g' f f' hg hf a

@[simp] theorem representativeEquiv_fraction (j : Fin m) :
    representativeEquiv K A s g g' f f' hg hf (fraction K A s g f j) =
      fraction K A s g' f' j := rfl

/-- Both comparison maps are contractions, hence the quotient norms agree exactly. -/
theorem norm_representativeEquiv (a : algebra K A s g f) :
    ‖representativeEquiv K A s g g' f f' hg hf a‖ = ‖a‖ := by
  apply le_antisymm (norm_representativeMap_le K A s g g' f f' hg hf a)
  have h := norm_representativeMap_le K A s g' g f' f hg.symm
    (fun j => (hf j).symm) (representativeMap K A s g g' f f' hg hf a)
  simpa only [representativeMap_inverse] using h

theorem isometry_representativeEquiv :
    Isometry (representativeEquiv K A s g g' f f' hg hf) :=
  AddMonoidHomClass.isometry_of_norm
    (representativeEquiv K A s g g' f f' hg hf).toAlgEquiv
    (norm_representativeEquiv K A s g g' f f' hg hf)

/-- The spectrum comparison is the actual contravariant pullback. -/
def representativeSpectrumHomeomorph :
    BanachSpectrum (algebra K A s g' f') ≃ₜ BanachSpectrum (algebra K A s g f) :=
  (representativeEquiv K A s g g' f f' hg hf).spectrumHomeomorph

@[simp] theorem spectrumMap_representativeSpectrumHomeomorph
    (x : BanachSpectrum (algebra K A s g' f')) :
    spectrumMap K A s g f (representativeSpectrumHomeomorph K A s g g' f f' hg hf x) =
      spectrumMap K A s g' f' x := by
  apply BanachSpectrum.ext
  intro a
  change x (representativeEquiv K A s g g' f f' hg hf (baseMap K A s g f a)) =
    x (baseMap K A s g' f' a)
  rw [representativeEquiv_baseMap]

/-- Unit-ideal generation depends only on the denominator and numerator classes. -/
theorem generatesUnitIdeal_congr :
    GeneratesUnitIdeal K A g f ↔ GeneratesUnitIdeal K A g' f' := by
  simp only [GeneratesUnitIdeal, hg, hf]

/-- The weighted inequality locus depends only on the same classes. -/
theorem locus_congr : locus K A s g f = locus K A s g' f' := by
  simp only [locus, hg, hf]

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalPresentation
