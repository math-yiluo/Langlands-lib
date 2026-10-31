import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCategory
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalBaseChange

/-! # Coefficient pullback of actual positive-radius rational charts -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A B : PresentedAffinoidAlgebra K}

/-- Choose a scalar series representative of an actual coefficient class. -/
def coefficientRepresentative (B : PresentedAffinoidAlgebra K) (b : B) :
    GeneralizedTateAlgebra B.polyradius K :=
  Classical.choose (presentationMap_surjective K B b)

@[simp] theorem presentationMap_coefficientRepresentative
    (B : PresentedAffinoidAlgebra K) (b : B) :
    presentationMap K B (coefficientRepresentative B b) = b :=
  Classical.choose_spec (presentationMap_surjective K B b)

/-- Pull back chosen rational data along an arbitrary bounded coefficient map.
Only scalar representatives are chosen; generation is proved after mapping. -/
def pullback (φ : BoundedAlgHom K A B) (d : RationalChart K A) :
    RationalChart K B where
  arity := d.arity
  radii := d.radii
  denominator := coefficientRepresentative B (φ (presentationMap K A d.denominator))
  numerators j := coefficientRepresentative B (φ (presentationMap K A (d.numerators j)))
  generates := RationalPresentation.BaseChange.generatesUnitIdeal
    (presentationMap_coefficientRepresentative B _).symm
    (fun _ => (presentationMap_coefficientRepresentative B _).symm) d.generates

@[simp] theorem pullback_arity (φ : BoundedAlgHom K A B) (d : RationalChart K A) :
    (pullback φ d).arity = d.arity := rfl

@[simp] theorem pullback_radii (φ : BoundedAlgHom K A B) (d : RationalChart K A) :
    (pullback φ d).radii = d.radii := rfl

@[simp] theorem pullback_denominator_class
    (φ : BoundedAlgHom K A B) (d : RationalChart K A) :
    presentationMap K B (pullback φ d).denominator =
      φ (presentationMap K A d.denominator) :=
  presentationMap_coefficientRepresentative B _

@[simp] theorem pullback_numerator_class
    (φ : BoundedAlgHom K A B) (d : RationalChart K A) (j : Fin d.arity) :
    presentationMap K B ((pullback φ d).numerators j) =
      φ (presentationMap K A (d.numerators j)) :=
  presentationMap_coefficientRepresentative B _

/-- The chosen chart has exactly the inverse-image rational inequalities. -/
theorem pullback_locus (φ : BoundedAlgHom K A B) (d : RationalChart K A) :
    (pullback φ d).locus =
      (BanachSpectrum.comap φ.toBoundedRingHom) ⁻¹' d.locus :=
  RationalPresentation.BaseChange.locus_eq_preimage
    (pullback_denominator_class φ d).symm
    (fun j => (pullback_numerator_class φ d j).symm)

variable [CompleteSpace K]

/-- The actual bounded map of the scalar rational quotients. -/
def pullbackMap (φ : BoundedAlgHom K A B) (d : RationalChart K A) :
    BoundedAlgHom K d.algebra (pullback φ d).algebra :=
  RationalPresentation.presentationTransport K d.radii d.denominator d.numerators
    (pullback φ d).denominator (pullback φ d).numerators φ
    (pullback_denominator_class φ d).symm
    (fun j => (pullback_numerator_class φ d j).symm)

@[simp] theorem pullbackMap_baseMap
    (φ : BoundedAlgHom K A B) (d : RationalChart K A) (a : A) :
    pullbackMap φ d (d.baseMap a) = (pullback φ d).baseMap (φ a) :=
  RationalPresentation.presentationTransport_baseMap K d.radii
    d.denominator d.numerators (pullback φ d).denominator (pullback φ d).numerators φ
    (pullback_denominator_class φ d).symm
    (fun j => (pullback_numerator_class φ d j).symm) a

/-- The coefficient and rational-quotient square commutes. -/
theorem pullbackMap_comp_baseMap
    (φ : BoundedAlgHom K A B) (d : RationalChart K A) :
    (pullbackMap φ d).comp d.baseMap = (pullback φ d).baseMap.comp φ :=
  BoundedAlgHom.ext (pullbackMap_baseMap φ d)

@[simp] theorem pullbackMap_fraction
    (φ : BoundedAlgHom K A B) (d : RationalChart K A) (j : Fin d.arity) :
    pullbackMap φ d
        (RationalPresentation.fraction K A d.radii d.denominator d.numerators j) =
      RationalPresentation.fraction K B (pullback φ d).radii
        (pullback φ d).denominator (pullback φ d).numerators j :=
  RationalPresentation.presentationTransport_fraction K d.radii
    d.denominator d.numerators (pullback φ d).denominator (pullback φ d).numerators φ
    (pullback_denominator_class φ d).symm
    (fun j => (pullback_numerator_class φ d j).symm) j

private theorem pullbackRestriction_compatible
    (φ : BoundedAlgHom K A B) {d e : RationalChart K A} (h : d ⟶ e) :
    ((pullbackMap φ d).comp h.restriction).comp e.baseMap =
      (pullback φ d).baseMap.comp φ := by
  change (pullbackMap φ d).comp (h.restriction.comp e.baseMap) = _
  rw [h.comp_baseMap, pullbackMap_comp_baseMap]

/-- The quotient pushout constructs the actual restriction after coefficient
change, with no image-containment representability assumption. -/
def pullbackRestriction (φ : BoundedAlgHom K A B)
    {d e : RationalChart K A} (h : d ⟶ e) : pullback φ d ⟶ pullback φ e where
  restriction := RationalPresentation.BaseChange.pushoutLift
    (pullback_denominator_class φ e).symm
    (fun j => (pullback_numerator_class φ e j).symm)
    (pullback φ d).algebra ((pullbackMap φ d).comp h.restriction)
    (pullback φ d).baseMap (pullbackRestriction_compatible φ h)
  comp_baseMap := RationalPresentation.BaseChange.pushoutLift_comp_baseMap
    (pullback_denominator_class φ e).symm
    (fun j => (pullback_numerator_class φ e j).symm)
    (pullback φ d).algebra ((pullbackMap φ d).comp h.restriction)
    (pullback φ d).baseMap (pullbackRestriction_compatible φ h)

/-- The restriction after change of coefficients commutes with quotient transport. -/
theorem pullbackRestriction_comp_pullbackMap
    (φ : BoundedAlgHom K A B) {d e : RationalChart K A} (h : d ⟶ e) :
    (pullbackRestriction φ h).restriction.comp (pullbackMap φ e) =
      (pullbackMap φ d).comp h.restriction :=
  RationalPresentation.BaseChange.pushoutLift_comp_transport
    (pullback_denominator_class φ e).symm
    (fun j => (pullback_numerator_class φ e j).symm)
    (pullback φ d).algebra ((pullbackMap φ d).comp h.restriction)
    (pullback φ d).baseMap (pullbackRestriction_compatible φ h)

/-- Actual pullback of the category of chosen rational charts and restrictions. -/
def pullbackFunctor (φ : BoundedAlgHom K A B) :
    RationalChart K A ⥤ RationalChart K B where
  obj := pullback φ
  map := pullbackRestriction φ
  map_id _ := @Subsingleton.elim (Restriction _ _) inferInstance _ _
  map_comp _ _ := @Subsingleton.elim (Restriction _ _) inferInstance _ _

/-- Quotient transport is natural for the actual bounded quotient presheaves. -/
def pullbackPresheafMap (φ : BoundedAlgHom K A B) :
    boundedPresheaf K A ⟶
      (pullbackFunctor φ).op ⋙ boundedPresheaf K B where
  app d := pullbackMap φ d.unop
  naturality d e h := by
    change (pullbackMap φ e.unop).comp h.unop.restriction =
      (pullbackRestriction φ h.unop).restriction.comp (pullbackMap φ d.unop)
    exact (pullbackRestriction_comp_pullbackMap φ h.unop).symm

/-- The actual continuous map of quotient spectra induced by coefficient change. -/
def pullbackSpectrumMap (φ : BoundedAlgHom K A B) (d : RationalChart K A) :
    C(BanachSpectrum (pullback φ d).algebra, BanachSpectrum d.algebra) :=
  BanachSpectrum.comapContinuous (pullbackMap φ d).toBoundedRingHom

/-- Both actual paths to the original coefficient spectrum agree. -/
theorem pullbackSpectrumMap_over_base
    (φ : BoundedAlgHom K A B) (d : RationalChart K A)
    (x : BanachSpectrum (pullback φ d).algebra) :
    d.spectrumMap (pullbackSpectrumMap φ d x) =
      BanachSpectrum.comap φ.toBoundedRingHom ((pullback φ d).spectrumMap x) := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg x (pullbackMap_baseMap φ d a)

/-- The spectrum maps are natural for actual chart restrictions. -/
def pullbackSpectrumNat (φ : BoundedAlgHom K A B) :
    pullbackFunctor φ ⋙ toTopologicalSpace K B ⟶ toTopologicalSpace K A where
  app d := TopCat.ofHom (pullbackSpectrumMap φ d)
  naturality d e h := by
    apply TopCat.ext
    intro x
    change BanachSpectrum (pullback φ d).algebra at x
    apply BanachSpectrum.ext
    intro a
    exact congrArg (fun χ : BoundedAlgHom K e.algebra (pullback φ d).algebra => x (χ a))
      (pullbackRestriction_comp_pullbackMap φ h)

/-- The chosen actual quotient spectrum square is the published concrete cone. -/
def pullbackSpectrumCone (φ : BoundedAlgHom K A B) (d : RationalChart K A) :
    PullbackCone (TopCat.ofHom (BanachSpectrum.comapContinuous φ.toBoundedRingHom))
      (TopCat.ofHom d.spectrumMap) :=
  RationalPresentation.BaseChange.spectrumCone
    (s := d.radii) (pullback_denominator_class φ d).symm
    (fun j => (pullback_numerator_class φ d j).symm)

/-- The actual spectrum of the chosen chart is the topological pullback. -/
def pullbackSpectrumConeIsLimit (φ : BoundedAlgHom K A B) (d : RationalChart K A) :
    IsLimit (pullbackSpectrumCone φ d) :=
  RationalPresentation.BaseChange.spectrumConeIsLimit
    (s := d.radii) (pullback_denominator_class φ d).symm
    (fun j => (pullback_numerator_class φ d j).symm) d.generates

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
