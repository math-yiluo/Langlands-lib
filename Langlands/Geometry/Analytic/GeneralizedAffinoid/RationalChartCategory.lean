import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalRadiusSpectrum
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Banach
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Actual bounded restrictions between positive-radius rational charts -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K)

/-- Chosen finite weighted rational data over an actual affinoid presentation.
Generation is imposed on the actual coefficient classes. -/
structure RationalChart where
  arity : ℕ
  radii : PositivePolyradius (Fin arity)
  denominator : GeneralizedTateAlgebra A.polyradius K
  numerators : Fin arity → GeneralizedTateAlgebra A.polyradius K
  generates : RationalPresentation.GeneratesUnitIdeal K A denominator numerators

namespace RationalChart

variable {K A}

/-- The actual closed rational quotient with its constructed quotient norm. -/
def algebra (d : RationalChart K A) : PresentedAffinoidAlgebra K :=
  RationalPresentation.algebra K A d.radii d.denominator d.numerators

/-- The actual bounded structural map from the fixed base. -/
def baseMap (d : RationalChart K A) : BoundedAlgHom K A d.algebra :=
  RationalPresentation.baseMap K A d.radii d.denominator d.numerators

/-- The closed inequality locus in the base spectrum. -/
def locus (d : RationalChart K A) : Set (BanachSpectrum A) :=
  RationalPresentation.locus K A d.radii d.denominator d.numerators

/-- The constructed structural spectrum map. -/
def spectrumMap (d : RationalChart K A) : C(BanachSpectrum d.algebra, BanachSpectrum A) :=
  RationalPresentation.spectrumMap K A d.radii d.denominator d.numerators

/-- The published spectrum identification for the chosen rational data. -/
def locusHomeomorph (d : RationalChart K A) : BanachSpectrum d.algebra ≃ₜ d.locus :=
  RationalPresentation.locusHomeomorph K A d.radii d.denominator d.numerators d.generates

@[simp] theorem locusHomeomorph_apply_coe (d : RationalChart K A)
    (x : BanachSpectrum d.algebra) :
    (d.locusHomeomorph x).val = d.spectrumMap x := rfl

/-- Arrows have the space direction. Their data are actual bounded algebra maps
in the opposite direction, with a proved equation over the fixed base. -/
structure Restriction (d e : RationalChart K A) where
  restriction : BoundedAlgHom K e.algebra d.algebra
  comp_baseMap : restriction.comp e.baseMap = d.baseMap

namespace Restriction

variable {d e f : RationalChart K A}

@[ext] theorem ext {h k : Restriction d e}
    (heq : h.restriction = k.restriction) : h = k := by
  cases h
  cases k
  cases heq
  rfl

/-- Unit generation proves uniqueness of actual maps over the base. -/
instance : Subsingleton (Restriction d e) := ⟨fun h k => by
  apply ext
  apply RationalPresentation.hom_ext_base K A e.radii e.denominator e.numerators
    d.algebra e.generates
  exact h.comp_baseMap.trans k.comp_baseMap.symm⟩

end Restriction

/-- Only actual bounded maps over the base are arrows; no converse
image-containment representability is assumed. -/
instance : Category (RationalChart K A) where
  Hom d e := Restriction d e
  id d := ⟨BoundedAlgHom.id K d.algebra, by rfl⟩
  comp h k := ⟨h.restriction.comp k.restriction, by
    change h.restriction.comp (k.restriction.comp _) = _
    rw [k.comp_baseMap, h.comp_baseMap]⟩
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

namespace Restriction

variable {d e f : RationalChart K A}

@[simp] theorem restriction_id (d : RationalChart K A) :
    (𝟙 d : d ⟶ d).restriction = BoundedAlgHom.id K d.algebra := rfl

@[simp] theorem restriction_comp (h : d ⟶ e) (k : e ⟶ f) :
    (h ≫ k).restriction = h.restriction.comp k.restriction := rfl

/-- Continuous pullback of bounded multiplicative seminorms. -/
def spectrumMap (h : Restriction d e) :
    C(BanachSpectrum d.algebra, BanachSpectrum e.algebra) :=
  BanachSpectrum.comapContinuous h.restriction.toBoundedRingHom

/-- The actual spectrum maps commute with the fixed-base structural maps. -/
theorem spectrumMap_over_base (h : Restriction d e) (x : BanachSpectrum d.algebra) :
    e.spectrumMap (h.spectrumMap x) = d.spectrumMap x := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun φ : BoundedAlgHom K A d.algebra => x (φ a)) h.comp_baseMap

/-- An actual bounded restriction entails inclusion of the inequality loci. -/
theorem subset (h : Restriction d e) : d.locus ⊆ e.locus := by
  intro x hx
  let y := d.locusHomeomorph.symm ⟨x, hx⟩
  have hy : d.spectrumMap y = x :=
    congrArg Subtype.val (d.locusHomeomorph.apply_symm_apply ⟨x, hx⟩)
  have he := (e.locusHomeomorph (h.spectrumMap y)).property
  change e.spectrumMap (h.spectrumMap y) ∈ e.locus at he
  rwa [h.spectrumMap_over_base, hy] at he

/-- The continuous inclusion of the actual base-locus subspaces. -/
def locusMap (h : Restriction d e) : C(d.locus, e.locus) where
  toFun x := ⟨x.val, h.subset x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp] theorem locusMap_apply_coe (h : Restriction d e) (x : d.locus) :
    (h.locusMap x).val = x.val := rfl

/-- The spectrum map is the ordinary inclusion under the existing
homeomorphisms with the base-locus subspaces. -/
theorem locusHomeomorph_naturality (h : Restriction d e)
    (x : BanachSpectrum d.algebra) :
    e.locusHomeomorph (h.spectrumMap x) = h.locusMap (d.locusHomeomorph x) := by
  apply Subtype.ext
  exact h.spectrumMap_over_base x

/-- Every actual restriction is a closed embedding on spectra. -/
theorem isClosedEmbedding_spectrumMap (h : Restriction d e) :
    Topology.IsClosedEmbedding h.spectrumMap := by
  apply h.spectrumMap.continuous.isClosedEmbedding
  intro x y hxy
  apply d.locusHomeomorph.injective
  apply Subtype.ext
  calc
    d.spectrumMap x = e.spectrumMap (h.spectrumMap x) := (h.spectrumMap_over_base x).symm
    _ = e.spectrumMap (h.spectrumMap y) := congrArg e.spectrumMap hxy
    _ = d.spectrumMap y := h.spectrumMap_over_base y

end Restriction

/-- Change just the displayed positive radii, retaining the actual rational
coefficients and their unit-generation proof. -/
def withRadii (d : RationalChart K A) (t : PositivePolyradius (Fin d.arity)) :
    RationalChart K A where
  arity := d.arity
  radii := t
  denominator := d.denominator
  numerators := d.numerators
  generates := d.generates

/-- The existing constructed radius map gives an actual chart arrow. -/
def radiusRestriction (d : RationalChart K A) (t : PositivePolyradius (Fin d.arity))
    (ht : ∀ j, t j ≤ d.radii j) : d.withRadii t ⟶ d where
  restriction := RationalPresentation.radiusMap K A d.radii t ht d.denominator d.numerators
  comp_baseMap := BoundedAlgHom.ext
    (RationalPresentation.radiusMap_baseMap K A d.radii t ht d.denominator d.numerators)

/-- Explicit bounded fraction solutions construct arrows by the published
weighted evaluation and descent, over a complete coefficient field. -/
def restrictionOfFractions [CompleteSpace K] (d e : RationalChart K A)
    (b : Fin e.arity → d.algebra)
    (hb : GeneralizedTateAlgebra.HasBoundedMonomials e.radii d.algebra b)
    (heq : ∀ j, d.baseMap (presentationMap K A e.denominator) * b j =
      d.baseMap (presentationMap K A (e.numerators j))) : d ⟶ e where
  restriction := RationalPresentation.liftFromBase K A e.radii e.denominator e.numerators
    d.algebra d.baseMap b hb heq
  comp_baseMap := RationalPresentation.liftFromBase_comp_baseMap K A e.radii
    e.denominator e.numerators d.algebra d.baseMap b hb heq

@[simp] theorem restrictionOfFractions_fraction [CompleteSpace K] (d e : RationalChart K A)
    (b : Fin e.arity → d.algebra)
    (hb : GeneralizedTateAlgebra.HasBoundedMonomials e.radii d.algebra b)
    (heq : ∀ j, d.baseMap (presentationMap K A e.denominator) * b j =
      d.baseMap (presentationMap K A (e.numerators j))) (j : Fin e.arity) :
    (restrictionOfFractions d e b hb heq).restriction
      (RationalPresentation.fraction K A e.radii e.denominator e.numerators j) = b j :=
  RationalPresentation.liftFromBase_fraction K A e.radii e.denominator e.numerators
    d.algebra d.baseMap b hb heq j

variable (K A)

/-- Realization by the constructed affinoid presentations and actual maps. -/
def toAffinoidSpace : RationalChart K A ⥤ PresentedAffinoidSpace K where
  obj d := Opposite.op d.algebra
  map h := Quiver.Hom.op h.restriction
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The realization consists of actual multiplicative seminorm spectra. -/
def toTopologicalSpace : RationalChart K A ⥤ TopCat :=
  toAffinoidSpace K A ⋙ affinoidSpectrumFunctor K

/-- The same diagram as actual subspaces of the fixed base spectrum. -/
def locusFunctor : RationalChart K A ⥤ TopCat where
  obj d := TopCat.of d.locus
  map h := TopCat.ofHom h.locusMap
  map_id d := by
    apply TopCat.ext
    intro x
    rfl
  map_comp h k := by
    apply TopCat.ext
    intro x
    rfl

/-- The actual spectrum realization agrees naturally with the subspace
inclusions. This asserts no converse existence of chart arrows. -/
def spectrumLocusIso : toTopologicalSpace K A ≅ locusFunctor K A :=
  NatIso.ofComponents (fun d => TopCat.isoOfHomeo d.locusHomeomorph)
    (fun h => by
      apply TopCat.ext
      intro x
      exact h.locusHomeomorph_naturality x)

/-- The presheaf of actual rational quotient presentations and bounded maps. -/
def boundedPresheaf : (RationalChart K A)ᵒᵖ ⥤ PresentedAffinoidAlgebra K where
  obj d := d.unop.algebra
  map h := h.unop.restriction
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Retain the actual complete normed quotient rings. -/
def banachPresheaf [CompleteSpace K] : (RationalChart K A)ᵒᵖ ⥤ BanachRing :=
  boundedPresheaf K A ⋙ PresentedAffinoidAlgebra.toBanachRing K

/-- The actual commutative K-algebra presheaf, forgetting only the norm and
chosen presentation from the constructed quotient. -/
def algebraPresheaf : (RationalChart K A)ᵒᵖ ⥤ CommAlgCat K where
  obj d := CommAlgCat.of K d.unop.algebra
  map h := CommAlgCat.ofHom h.unop.restriction.toAlgHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The bounded structural maps form a natural transformation from the
constant base presheaf. -/
def baseMapNat : (Functor.const (RationalChart K A)ᵒᵖ).obj A ⟶
    boundedPresheaf K A where
  app d := d.unop.baseMap
  naturality d e h := by
    change e.unop.baseMap = h.unop.restriction.comp d.unop.baseMap
    exact h.unop.comp_baseMap.symm

end RationalChart
end Langlands.Analytic.PresentedAffinoidAlgebra
