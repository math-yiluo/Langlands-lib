import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCategory
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalComparison
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! # The actual whole rational chart and its terminal property -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K)

/-- The empty numerator tuple with denominator one is actual rational data
whose inequality locus is the whole base spectrum. -/
def whole : RationalChart K A where
  arity := 0
  radii := PositivePolyradius.unit (Fin 0)
  denominator := 1
  numerators := Fin.elim0
  generates := by
    apply (Ideal.eq_top_iff_one _).mpr
    change (1 : A) ∈ Ideal.span (insert (presentationMap K A 1) _)
    rw [map_one]
    exact Ideal.subset_span (Set.mem_insert _ _)

@[simp] theorem locus_whole : (whole K A).locus = Set.univ := by
  ext x
  simp [locus, RationalPresentation.locus, whole]

private theorem whole_monomialBound (d : Fin 0 →₀ ℕ) :
    ‖StrictTateAlgebra.monomialValue (Fin 0) A Fin.elim0 d‖ ≤
      (PositivePolyradius.unit (Fin 0)).weight d :=
  monomialValue_norm_le_weight _ A (norm_one_le K A) Fin.elim0 (fun j => Fin.elim0 j) d

variable [CompleteSpace K]

/-- Evaluate the intrinsic empty-variable quotient in the actual base algebra,
after the published isometric scalar-to-relative comparison. -/
def wholeRetraction : BoundedAlgHom K (whole K A).algebra A :=
  (RelativeRationalPresentation.evaluate K A (whole K A).radii
    (presentationMap K A (whole K A).denominator)
    (fun j => presentationMap K A ((whole K A).numerators j))
    A (BoundedAlgHom.id K A) Fin.elim0 (fun _ => le_rfl)
    (whole_monomialBound K A) (fun j => Fin.elim0 j)).comp
      (RationalPresentation.relativeEquiv K A (whole K A).radii
        (whole K A).denominator (whole K A).numerators).toBoundedAlgHom

@[simp] theorem wholeRetraction_baseMap (a : A) :
    wholeRetraction K A ((whole K A).baseMap a) = a := by
  change RelativeRationalPresentation.evaluate K A (whole K A).radii
    (presentationMap K A (whole K A).denominator)
    (fun j => presentationMap K A ((whole K A).numerators j))
    A (BoundedAlgHom.id K A) Fin.elim0 (fun _ => le_rfl)
    (whole_monomialBound K A) (fun j => Fin.elim0 j)
    (RationalPresentation.relativeEquiv K A (whole K A).radii
      (whole K A).denominator (whole K A).numerators
      (RationalPresentation.baseMap K A (whole K A).radii
        (whole K A).denominator (whole K A).numerators a)) = a
  rw [RationalPresentation.relativeEquiv_baseMap]
  exact RelativeRationalPresentation.evaluate_baseMap K A (whole K A).radii
    (presentationMap K A (whole K A).denominator)
    (fun j => presentationMap K A ((whole K A).numerators j))
    A (BoundedAlgHom.id K A) Fin.elim0 (fun _ => le_rfl)
    (whole_monomialBound K A) (fun j => Fin.elim0 j) a

theorem wholeRetraction_comp_baseMap :
    (wholeRetraction K A).comp (whole K A).baseMap = BoundedAlgHom.id K A :=
  BoundedAlgHom.ext (wholeRetraction_baseMap K A)

/-- Both actual quotient norms are respected by the constructed retraction. -/
theorem norm_wholeRetraction_le (a : (whole K A).algebra) :
    ‖wholeRetraction K A a‖ ≤ ‖a‖ :=
  (RelativeRationalPresentation.norm_evaluate_le K A (whole K A).radii
    (presentationMap K A (whole K A).denominator)
    (fun j => presentationMap K A ((whole K A).numerators j))
    A (BoundedAlgHom.id K A) Fin.elim0 (fun _ => le_rfl)
    (whole_monomialBound K A) (fun j => Fin.elim0 j) _).trans_eq
      (RationalPresentation.norm_relativeEquiv K A (whole K A).radii
        (whole K A).denominator (whole K A).numerators a)

/-- Uniqueness of bounded maps over the base proves the other inverse equation. -/
theorem wholeBaseMap_comp_retraction :
    (whole K A).baseMap.comp (wholeRetraction K A) =
      BoundedAlgHom.id K (whole K A).algebra := by
  apply RationalPresentation.hom_ext_base K A (whole K A).radii
    (whole K A).denominator (whole K A).numerators (whole K A).algebra
    (whole K A).generates
  apply BoundedAlgHom.ext
  intro a
  change (whole K A).baseMap (wholeRetraction K A ((whole K A).baseMap a)) =
    (whole K A).baseMap a
  rw [wholeRetraction_baseMap]

@[simp] theorem wholeBaseMap_retraction (a : (whole K A).algebra) :
    (whole K A).baseMap (wholeRetraction K A a) = a :=
  congrArg (fun φ : BoundedAlgHom K (whole K A).algebra (whole K A).algebra => φ a)
    (wholeBaseMap_comp_retraction K A)

theorem norm_wholeBaseMap (a : A) : ‖(whole K A).baseMap a‖ = ‖a‖ := by
  apply le_antisymm
    (RationalPresentation.norm_baseMap_le K A (whole K A).radii
      (whole K A).denominator (whole K A).numerators a)
  have h := norm_wholeRetraction_le K A ((whole K A).baseMap a)
  rwa [wholeRetraction_baseMap] at h

theorem norm_wholeRetraction (a : (whole K A).algebra) :
    ‖wholeRetraction K A a‖ = ‖a‖ := by
  rw [← norm_wholeBaseMap K A (wholeRetraction K A a), wholeBaseMap_retraction]

/-- An actual bounded algebra equivalence identifies the base with the
closed quotient underlying the empty-variable whole chart. -/
def wholeEquiv : BoundedAlgEquiv K A (whole K A).algebra :=
  BoundedAlgEquiv.ofHomInv (whole K A).baseMap (wholeRetraction K A)
    (wholeRetraction_baseMap K A) (wholeBaseMap_retraction K A)

@[simp] theorem wholeEquiv_apply (a : A) :
    wholeEquiv K A a = (whole K A).baseMap a := rfl

@[simp] theorem wholeEquiv_symm_apply (a : (whole K A).algebra) :
    (wholeEquiv K A).symm a = wholeRetraction K A a := rfl

theorem norm_wholeEquiv (a : A) : ‖wholeEquiv K A a‖ = ‖a‖ :=
  norm_wholeBaseMap K A a

theorem isometry_wholeEquiv : Isometry (wholeEquiv K A) :=
  AddMonoidHomClass.isometry_of_norm (wholeEquiv K A).toAlgEquiv (norm_wholeEquiv K A)

/-- The actual whole-chart spectrum is homeomorphic to the base spectrum. -/
def wholeSpectrumHomeomorph : BanachSpectrum (whole K A).algebra ≃ₜ BanachSpectrum A :=
  (wholeEquiv K A).spectrumHomeomorph

@[simp] theorem wholeSpectrumHomeomorph_apply (x : BanachSpectrum (whole K A).algebra) :
    wholeSpectrumHomeomorph K A x = (whole K A).spectrumMap x := rfl

@[simp] theorem wholeSpectrumHomeomorph_symm_apply (x : BanachSpectrum A)
    (a : (whole K A).algebra) :
    (wholeSpectrumHomeomorph K A).symm x a = x (wholeRetraction K A a) := rfl

/-- Every chart has an actual restriction from the whole-chart algebra,
constructed by its structural map composed with the retraction. -/
def toWhole (d : RationalChart K A) : d ⟶ whole K A where
  restriction := d.baseMap.comp (wholeRetraction K A)
  comp_baseMap := by
    rw [BoundedAlgHom.comp_assoc, wholeRetraction_comp_baseMap, BoundedAlgHom.comp_id]

@[simp] theorem toWhole_restriction (d : RationalChart K A) (a : (whole K A).algebra) :
    (toWhole K A d).restriction a = d.baseMap (wholeRetraction K A a) := rfl

theorem norm_toWhole_restriction_le (d : RationalChart K A) (a : (whole K A).algebra) :
    ‖(toWhole K A d).restriction a‖ ≤ ‖a‖ :=
  (RationalPresentation.norm_baseMap_le K A d.radii d.denominator d.numerators _).trans
    (norm_wholeRetraction_le K A a)

/-- Under the constructed whole-spectrum homeomorphism, the arrow is the
original structural spectrum map of the source chart. -/
theorem toWhole_spectrumMap (d : RationalChart K A) (x : BanachSpectrum d.algebra) :
    wholeSpectrumHomeomorph K A ((toWhole K A d).spectrumMap x) = d.spectrumMap x :=
  (toWhole K A d).spectrumMap_over_base x

/-- The explicit empty-variable chart is terminal among actual bounded
restrictions over the fixed base algebra. -/
def wholeIsTerminal : IsTerminal (whole K A) :=
  IsTerminal.ofUniqueHom (toWhole K A) (fun d f =>
    (inferInstance : Subsingleton (Restriction d (whole K A))).elim f (toWhole K A d))

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
