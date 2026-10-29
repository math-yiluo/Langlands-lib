import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCategory
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalIntersection
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-! # Explicit common refinements and topological pullbacks of rational charts -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}

/-- The all-products rational presentation, retaining every mixed numerator
and its product radius, gives a chosen common refinement. -/
def inter (d e : RationalChart K A) : RationalChart K A where
  arity := (d.arity + 1) * (e.arity + 1)
  radii := RationalPresentation.RationalIntersection.productRadii d.radii e.radii
  denominator := d.denominator * e.denominator
  numerators := RationalPresentation.RationalIntersection.numerators K A
    d.denominator e.denominator d.numerators e.numerators
  generates := RationalPresentation.RationalIntersection.generatesUnitIdeal K A
    d.denominator e.denominator d.numerators e.numerators d.generates e.generates

@[simp] theorem locus_inter (d e : RationalChart K A) :
    (d.inter e).locus = d.locus ∩ e.locus :=
  RationalPresentation.RationalIntersection.locus_eq_inter K A d.radii e.radii
    d.denominator e.denominator d.numerators e.numerators d.generates e.generates

variable [CompleteSpace K]

/-- The first common-refinement arrow uses the constructed bounded map. -/
def interLeft (d e : RationalChart K A) : d.inter e ⟶ d where
  restriction := RationalPresentation.RationalIntersection.leftMap K A d.radii e.radii
    d.denominator e.denominator d.numerators e.numerators d.generates e.generates
  comp_baseMap := RationalPresentation.RationalIntersection.leftMap_comp_baseMap K A
    d.radii e.radii d.denominator e.denominator d.numerators e.numerators
    d.generates e.generates

/-- The second common-refinement arrow uses the constructed bounded map. -/
def interRight (d e : RationalChart K A) : d.inter e ⟶ e where
  restriction := RationalPresentation.RationalIntersection.rightMap K A d.radii e.radii
    d.denominator e.denominator d.numerators e.numerators d.generates e.generates
  comp_baseMap := RationalPresentation.RationalIntersection.rightMap_comp_baseMap K A
    d.radii e.radii d.denominator e.denominator d.numerators e.numerators
    d.generates e.generates

theorem norm_interLeft_le (d e : RationalChart K A) (a : d.algebra) :
    ‖(interLeft d e).restriction a‖ ≤ ‖a‖ :=
  RationalPresentation.RationalIntersection.norm_leftMap_le K A d.radii e.radii
    d.denominator e.denominator d.numerators e.numerators d.generates e.generates a

theorem norm_interRight_le (d e : RationalChart K A) (a : e.algebra) :
    ‖(interRight d e).restriction a‖ ≤ ‖a‖ :=
  RationalPresentation.RationalIntersection.norm_rightMap_le K A d.radii e.radii
    d.denominator e.denominator d.numerators e.numerators d.generates e.generates a

/-- The two actual seminorm pullbacks have the same image in the base. -/
theorem inter_spectrum_condition (d e : RationalChart K A)
    (x : BanachSpectrum (d.inter e).algebra) :
    d.spectrumMap ((interLeft d e).spectrumMap x) =
      e.spectrumMap ((interRight d e).spectrumMap x) :=
  ((interLeft d e).spectrumMap_over_base x).trans
    ((interRight d e).spectrumMap_over_base x).symm

/-- Lift compatible continuous maps through the proved intersection locus
and the constructed spectrum/locus homeomorphism. -/
def spectrumInterLift (d e : RationalChart K A)
    {X : Type v} [TopologicalSpace X]
    (p : C(X, BanachSpectrum d.algebra)) (q : C(X, BanachSpectrum e.algebra))
    (hpq : ∀ x, d.spectrumMap (p x) = e.spectrumMap (q x)) :
    C(X, BanachSpectrum (d.inter e).algebra) := by
  have hmem : ∀ x, d.spectrumMap (p x) ∈ (d.inter e).locus := by
    intro x
    rw [locus_inter]
    refine ⟨(d.locusHomeomorph (p x)).property, ?_⟩
    rw [hpq x]
    exact (e.locusHomeomorph (q x)).property
  exact ⟨fun x => (d.inter e).locusHomeomorph.symm ⟨d.spectrumMap (p x), hmem x⟩,
    (d.inter e).locusHomeomorph.symm.continuous.comp
      ((d.spectrumMap.continuous.comp p.continuous).subtype_mk hmem)⟩

omit [CompleteSpace K] in
@[simp] theorem spectrumMap_spectrumInterLift (d e : RationalChart K A)
    {X : Type v} [TopologicalSpace X]
    (p : C(X, BanachSpectrum d.algebra)) (q : C(X, BanachSpectrum e.algebra))
    (hpq : ∀ x, d.spectrumMap (p x) = e.spectrumMap (q x)) (x : X) :
    (d.inter e).spectrumMap (spectrumInterLift d e p q hpq x) =
      d.spectrumMap (p x) :=
  congrArg Subtype.val ((d.inter e).locusHomeomorph.apply_symm_apply _)

@[simp] theorem interLeft_spectrumInterLift (d e : RationalChart K A)
    {X : Type v} [TopologicalSpace X]
    (p : C(X, BanachSpectrum d.algebra)) (q : C(X, BanachSpectrum e.algebra))
    (hpq : ∀ x, d.spectrumMap (p x) = e.spectrumMap (q x)) (x : X) :
    (interLeft d e).spectrumMap (spectrumInterLift d e p q hpq x) = p x := by
  apply d.locusHomeomorph.injective
  apply Subtype.ext
  change d.spectrumMap _ = d.spectrumMap (p x)
  rw [(interLeft d e).spectrumMap_over_base, spectrumMap_spectrumInterLift]

@[simp] theorem interRight_spectrumInterLift (d e : RationalChart K A)
    {X : Type v} [TopologicalSpace X]
    (p : C(X, BanachSpectrum d.algebra)) (q : C(X, BanachSpectrum e.algebra))
    (hpq : ∀ x, d.spectrumMap (p x) = e.spectrumMap (q x)) (x : X) :
    (interRight d e).spectrumMap (spectrumInterLift d e p q hpq x) = q x := by
  apply e.locusHomeomorph.injective
  apply Subtype.ext
  change e.spectrumMap _ = e.spectrumMap (q x)
  rw [(interRight d e).spectrumMap_over_base, spectrumMap_spectrumInterLift]
  exact hpq x

/-- The first projection already determines a map to the intersection,
since its spectrum is embedded in the base spectrum. -/
theorem spectrumInterLift_unique (d e : RationalChart K A)
    {X : Type v} [TopologicalSpace X]
    (p : C(X, BanachSpectrum d.algebra)) (q : C(X, BanachSpectrum e.algebra))
    (hpq : ∀ x, d.spectrumMap (p x) = e.spectrumMap (q x))
    (r : C(X, BanachSpectrum (d.inter e).algebra))
    (hr : ∀ x, (interLeft d e).spectrumMap (r x) = p x) :
    r = spectrumInterLift d e p q hpq := by
  apply ContinuousMap.ext
  intro x
  apply (d.inter e).locusHomeomorph.injective
  apply Subtype.ext
  change (d.inter e).spectrumMap (r x) =
    (d.inter e).spectrumMap (spectrumInterLift d e p q hpq x)
  rw [spectrumMap_spectrumInterLift,
    ← (interLeft d e).spectrumMap_over_base, hr]

/-- The spectrum of the explicit quotient is a cone over the two actual
structural spectrum maps. -/
def spectrumInterCone (d e : RationalChart K A) :
    PullbackCone (TopCat.ofHom d.spectrumMap) (TopCat.ofHom e.spectrumMap) :=
  PullbackCone.mk (TopCat.ofHom (interLeft d e).spectrumMap)
    (TopCat.ofHom (interRight d e).spectrumMap) (by
      apply TopCat.ext
      intro x
      exact inter_spectrum_condition d e x)

/-- This is a topological pullback of actual spectra; it does not assert a
bounded algebra pushout or a product in the rational-chart category. -/
def spectrumInterConeIsLimit (d e : RationalChart K A) :
    IsLimit (spectrumInterCone d e) :=
  PullbackCone.IsLimit.mk _
    (fun S => TopCat.ofHom (spectrumInterLift d e S.fst.hom S.snd.hom
      (fun x => ConcreteCategory.congr_hom S.condition x)))
    (fun S => by
      apply TopCat.ext
      intro x
      exact interLeft_spectrumInterLift d e S.fst.hom S.snd.hom
        (fun y => ConcreteCategory.congr_hom S.condition y) x)
    (fun S => by
      apply TopCat.ext
      intro x
      exact interRight_spectrumInterLift d e S.fst.hom S.snd.hom
        (fun y => ConcreteCategory.congr_hom S.condition y) x)
    (fun S m hm _ => by
      apply TopCat.ext
      intro x
      exact congrArg (fun f : C(S.pt, BanachSpectrum (d.inter e).algebra) => f x)
        (spectrumInterLift_unique d e S.fst.hom S.snd.hom
          (fun y => ConcreteCategory.congr_hom S.condition y) m.hom
          (fun y => ConcreteCategory.congr_hom hm y)))

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
