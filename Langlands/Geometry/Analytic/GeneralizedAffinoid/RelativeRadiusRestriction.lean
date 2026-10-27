import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRelationsSpectrum
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.RadiusRestriction

/-! # Radius restriction of relative closed-equation quotients -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

namespace GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] {σ : Type v}
  (s t : PositivePolyradius σ) (hts : ∀ j, t j ≤ s j)
  (A : Type w) [NormedCommRing A] [IsUltrametricDist A] [Algebra K A]

/-- Coefficient-preserving radius restriction over a common base field. -/
def restrictRadiusAlgHom :
    BoundedAlgHom K (GeneralizedTateAlgebra s A) (GeneralizedTateAlgebra t A) where
  toAlgHom := (restrictRadius s t hts A).restrictScalars K
  bounded := ⟨1, zero_lt_one, fun f => by
    change ‖restrictRadius s t hts A f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_restrictRadius_le s t hts A f⟩

@[simp] theorem restrictRadiusAlgHom_apply (f : GeneralizedTateAlgebra s A) :
    restrictRadiusAlgHom K s t hts A f = restrictRadius s t hts A f := rfl

theorem norm_restrictRadiusAlgHom_le (f : GeneralizedTateAlgebra s A) :
    ‖restrictRadiusAlgHom K s t hts A f‖ ≤ ‖f‖ :=
  norm_restrictRadius_le s t hts A f

@[simp] theorem restrictRadiusAlgHom_constant (a : A) :
    restrictRadiusAlgHom K s t hts A (constantAlgHom s K A a) =
      constantAlgHom t K A a :=
  (restrictRadius s t hts A).commutes a

@[simp] theorem restrictRadiusAlgHom_X (j : σ) :
    restrictRadiusAlgHom K s t hts A (X s A j) = X t A j :=
  restrictRadius_X s t hts A j

@[simp] theorem restrictRadiusAlgHom_self :
    restrictRadiusAlgHom K s s (fun _ => le_rfl) A =
      BoundedAlgHom.id K (GeneralizedTateAlgebra s A) := by
  apply BoundedAlgHom.ext
  exact restrictRadius_self s A

theorem restrictRadiusAlgHom_trans (q : PositivePolyradius σ)
    (hqt : ∀ j, q j ≤ t j) :
    (restrictRadiusAlgHom K t q hqt A).comp (restrictRadiusAlgHom K s t hts A) =
      restrictRadiusAlgHom K s q (fun j => (hqt j).trans (hts j)) A := by
  apply BoundedAlgHom.ext
  exact restrictRadius_trans s t hts A q hqt

variable {A} {B : Type z} [NormedCommRing B] [IsUltrametricDist B] [Algebra K B]

/-- Retaining coefficients while shrinking radii commutes with coefficient maps. -/
theorem restrictRadiusAlgHom_mapCoefficients (φ : BoundedAlgHom K A B)
    (f : GeneralizedTateAlgebra s A) :
    restrictRadiusAlgHom K s t hts B (mapCoefficientsAlgHom s φ f) =
      mapCoefficientsAlgHom t φ (restrictRadiusAlgHom K s t hts A f) := by
  apply Subtype.ext
  rfl

end GeneralizedTateAlgebra

namespace PresentedAffinoidAlgebra.RelativeRelations

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ}
  (s t : PositivePolyradius (Fin m)) (hts : ∀ j, t j ≤ s j)

/-- Each source equation restricts into the target closed generated ideal. -/
def RadiusMapsRelations (E : Set (GeneralizedTateAlgebra s A))
    (F : Set (GeneralizedTateAlgebra t A)) : Prop :=
  ∀ f ∈ E, restrictRadiusAlgHom K s t hts A f ∈ ideal K A t F

variable {E : Set (GeneralizedTateAlgebra s A)}
  {F : Set (GeneralizedTateAlgebra t A)}

theorem radiusMapsRelations_of_mapsTo
    (h : Set.MapsTo (restrictRadiusAlgHom K s t hts A) E F) :
    RadiusMapsRelations K A s t hts E F :=
  fun _ hf => equation_mem K A t F (h hf)

/-- Compatibility on equations extends to the entire source closed ideal. -/
theorem radiusMapsRelations_ideal (h : RadiusMapsRelations K A s t hts E F) :
    ∀ f ∈ ideal K A s E, restrictRadiusAlgHom K s t hts A f ∈ ideal K A t F := by
  intro f hf
  apply (quotientMap_eq_zero_iff K A t F _).mp
  exact annihilates_ideal K A s E (QuotientAlgebra K A t F)
    ((quotientMap K A t F).comp (restrictRadiusAlgHom K s t hts A))
    (fun g hg => (quotientMap_eq_zero_iff K A t F _).mpr (h g hg)) f hf

theorem radiusMapsRelations_self (E : Set (GeneralizedTateAlgebra s A)) :
    RadiusMapsRelations K A s s (fun _ => le_rfl) E E := by
  intro f hf
  simpa only [restrictRadiusAlgHom_self, BoundedAlgHom.id_apply, ideal] using
    equation_mem K A s E hf

theorem radiusMapsRelations_trans (q : PositivePolyradius (Fin m))
    (hqt : ∀ j, q j ≤ t j) {G : Set (GeneralizedTateAlgebra q A)}
    (hEF : RadiusMapsRelations K A s t hts E F)
    (hFG : RadiusMapsRelations K A t q hqt F G) :
    RadiusMapsRelations K A s q (fun j => (hqt j).trans (hts j)) E G := by
  intro f hf
  have h := radiusMapsRelations_ideal K A t q hqt hFG _ (hEF f hf)
  change restrictRadius t q hqt A (restrictRadius s t hts A f) ∈ ideal K A q G at h
  rwa [restrictRadius_trans] at h

/-- Restriction of actual relative closed-equation quotient algebras. -/
def radiusMap (E : Set (GeneralizedTateAlgebra s A))
    (F : Set (GeneralizedTateAlgebra t A))
    (h : RadiusMapsRelations K A s t hts E F) :
    BoundedAlgHom K (QuotientAlgebra K A s E) (QuotientAlgebra K A t F) :=
  descend K A s E (QuotientAlgebra K A t F)
    ((quotientMap K A t F).comp (restrictRadiusAlgHom K s t hts A))
    (fun f hf => (quotientMap_eq_zero_iff K A t F _).mpr (h f hf))

@[simp] theorem radiusMap_quotientMap (h : RadiusMapsRelations K A s t hts E F)
    (f : GeneralizedTateAlgebra s A) :
    radiusMap K A s t hts E F h (quotientMap K A s E f) =
      quotientMap K A t F (restrictRadiusAlgHom K s t hts A f) := rfl

theorem radiusMap_comp_quotientMap (h : RadiusMapsRelations K A s t hts E F) :
    (radiusMap K A s t hts E F h).comp (quotientMap K A s E) =
      (quotientMap K A t F).comp (restrictRadiusAlgHom K s t hts A) :=
  BoundedAlgHom.ext fun _ => rfl

@[simp] theorem radiusMap_baseMap (h : RadiusMapsRelations K A s t hts E F) (a : A) :
    radiusMap K A s t hts E F h (baseMap K A s E a) = baseMap K A t F a := by
  change quotientMap K A t F
    (restrictRadiusAlgHom K s t hts A (constantAlgHom s K A a)) = _
  rw [restrictRadiusAlgHom_constant]
  rfl

@[simp] theorem radiusMap_newCoordinate (h : RadiusMapsRelations K A s t hts E F)
    (j : Fin m) :
    radiusMap K A s t hts E F h (newCoordinate K A s E j) =
      newCoordinate K A t F j := by
  change quotientMap K A t F (restrictRadiusAlgHom K s t hts A (X s A j)) = _
  rw [restrictRadiusAlgHom_X]
  rfl

/-- The descended map contracts the actual quotient norms. -/
theorem norm_radiusMap_le (h : RadiusMapsRelations K A s t hts E F)
    (a : QuotientAlgebra K A s E) :
    ‖radiusMap K A s t hts E F h a‖ ≤ ‖a‖ := by
  simpa only [one_mul, radiusMap] using
    norm_descend_le K A s E (QuotientAlgebra K A t F)
      ((quotientMap K A t F).comp (restrictRadiusAlgHom K s t hts A))
      (fun f hf => (quotientMap_eq_zero_iff K A t F _).mpr (h f hf)) 1 zero_lt_one
      (fun f => by
        change ‖quotientMap K A t F (restrictRadiusAlgHom K s t hts A f)‖ ≤ 1 * ‖f‖
        rw [one_mul]
        exact (norm_quotientMap_le K A t F _).trans
          (norm_restrictRadiusAlgHom_le K s t hts A f)) a

theorem eq_radiusMap (h : RadiusMapsRelations K A s t hts E F)
    (ψ : BoundedAlgHom K (QuotientAlgebra K A s E) (QuotientAlgebra K A t F))
    (hψ : ∀ f, ψ (quotientMap K A s E f) =
      quotientMap K A t F (restrictRadiusAlgHom K s t hts A f)) :
    ψ = radiusMap K A s t hts E F h :=
  hom_ext K A s E (QuotientAlgebra K A t F) _ _ hψ

@[simp] theorem radiusMap_self (E : Set (GeneralizedTateAlgebra s A)) :
    radiusMap K A s s (fun _ => le_rfl) E E (radiusMapsRelations_self K A s E) =
      BoundedAlgHom.id K (QuotientAlgebra K A s E) := by
  apply hom_ext K A s E (QuotientAlgebra K A s E)
  intro f
  simp only [radiusMap_quotientMap, restrictRadiusAlgHom_self, BoundedAlgHom.id_apply]

theorem radiusMap_trans (q : PositivePolyradius (Fin m))
    (hqt : ∀ j, q j ≤ t j) {G : Set (GeneralizedTateAlgebra q A)}
    (hEF : RadiusMapsRelations K A s t hts E F)
    (hFG : RadiusMapsRelations K A t q hqt F G) :
    (radiusMap K A t q hqt F G hFG).comp (radiusMap K A s t hts E F hEF) =
      radiusMap K A s q (fun j => (hqt j).trans (hts j)) E G
        (radiusMapsRelations_trans K A s t hts q hqt hEF hFG) := by
  apply hom_ext K A s E (QuotientAlgebra K A q G)
  intro f
  simp only [BoundedAlgHom.comp_apply, radiusMap_quotientMap, restrictRadiusAlgHom_apply]
  rw [restrictRadius_trans]

/-- Pullback along the descended radius map, with the contravariant direction. -/
def radiusSpectrumMap (E : Set (GeneralizedTateAlgebra s A))
    (F : Set (GeneralizedTateAlgebra t A))
    (h : RadiusMapsRelations K A s t hts E F) :
    C(BanachSpectrum (QuotientAlgebra K A t F), BanachSpectrum (QuotientAlgebra K A s E)) :=
  BanachSpectrum.comapContinuous (radiusMap K A s t hts E F h).toBoundedRingHom

@[simp] theorem radiusSpectrumMap_apply (h : RadiusMapsRelations K A s t hts E F)
    (x : BanachSpectrum (QuotientAlgebra K A t F)) (a : QuotientAlgebra K A s E) :
    radiusSpectrumMap K A s t hts E F h x a = x (radiusMap K A s t hts E F h a) := rfl

@[simp] theorem radiusSpectrumMap_quotientMap (h : RadiusMapsRelations K A s t hts E F)
    (x : BanachSpectrum (QuotientAlgebra K A t F)) (f : GeneralizedTateAlgebra s A) :
    radiusSpectrumMap K A s t hts E F h x (quotientMap K A s E f) =
      x (quotientMap K A t F (restrictRadiusAlgHom K s t hts A f)) := rfl

@[simp] theorem radiusSpectrumMap_baseMap (h : RadiusMapsRelations K A s t hts E F)
    (x : BanachSpectrum (QuotientAlgebra K A t F)) (a : A) :
    radiusSpectrumMap K A s t hts E F h x (baseMap K A s E a) =
      x (baseMap K A t F a) := by
  rw [radiusSpectrumMap_apply, radiusMap_baseMap]

@[simp] theorem radiusSpectrumMap_newCoordinate (h : RadiusMapsRelations K A s t hts E F)
    (x : BanachSpectrum (QuotientAlgebra K A t F)) (j : Fin m) :
    radiusSpectrumMap K A s t hts E F h x (newCoordinate K A s E j) =
      x (newCoordinate K A t F j) := by
  rw [radiusSpectrumMap_apply, radiusMap_newCoordinate]

@[simp] theorem radiusSpectrumMap_self (E : Set (GeneralizedTateAlgebra s A)) :
    radiusSpectrumMap K A s s (fun _ => le_rfl) E E (radiusMapsRelations_self K A s E) =
      ContinuousMap.id (BanachSpectrum (QuotientAlgebra K A s E)) := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  rw [radiusSpectrumMap_apply, radiusMap_self]
  rfl

theorem radiusSpectrumMap_trans (q : PositivePolyradius (Fin m))
    (hqt : ∀ j, q j ≤ t j) {G : Set (GeneralizedTateAlgebra q A)}
    (hEF : RadiusMapsRelations K A s t hts E F)
    (hFG : RadiusMapsRelations K A t q hqt F G) :
    radiusSpectrumMap K A s q (fun j => (hqt j).trans (hts j)) E G
        (radiusMapsRelations_trans K A s t hts q hqt hEF hFG) =
      (radiusSpectrumMap K A s t hts E F hEF).comp
        (radiusSpectrumMap K A t q hqt F G hFG) := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (radiusMap K A s q (fun j => (hqt j).trans (hts j)) E G
    (radiusMapsRelations_trans K A s t hts q hqt hEF hFG) a) =
      x (radiusMap K A t q hqt F G hFG (radiusMap K A s t hts E F hEF a))
  rw [← radiusMap_trans K A s t hts q hqt hEF hFG]
  rfl

/-- Radius pullback on the relative series spectrum preserves compatible equation loci. -/
def equationLocusRadiusMap (E : Set (GeneralizedTateAlgebra s A))
    (F : Set (GeneralizedTateAlgebra t A))
    (h : RadiusMapsRelations K A s t hts E F) :
    C(equationLocus K A t F, equationLocus K A s E) where
  toFun x := ⟨BanachSpectrum.comap (restrictRadiusAlgHom K s t hts A).toBoundedRingHom x.val,
    fun f hf => (mem_equationLocus_iff K A t F x.val).mp x.property (h f hf)⟩
  continuous_toFun := ((BanachSpectrum.comapContinuous
    (restrictRadiusAlgHom K s t hts A).toBoundedRingHom).continuous.comp
      continuous_subtype_val).subtype_mk _

@[simp] theorem equationLocusRadiusMap_apply (h : RadiusMapsRelations K A s t hts E F)
    (x : equationLocus K A t F) (f : GeneralizedTateAlgebra s A) :
    (equationLocusRadiusMap K A s t hts E F h x).val f =
      x.val (restrictRadiusAlgHom K s t hts A f) := rfl

@[simp] theorem equationLocusRadiusMap_constant (h : RadiusMapsRelations K A s t hts E F)
    (x : equationLocus K A t F) (a : A) :
    (equationLocusRadiusMap K A s t hts E F h x).val (constantAlgHom s K A a) =
      x.val (constantAlgHom t K A a) := by
  rw [equationLocusRadiusMap_apply, restrictRadiusAlgHom_constant]

@[simp] theorem equationLocusRadiusMap_X (h : RadiusMapsRelations K A s t hts E F)
    (x : equationLocus K A t F) (j : Fin m) :
    (equationLocusRadiusMap K A s t hts E F h x).val (X s A j) =
      x.val (X t A j) := by
  rw [equationLocusRadiusMap_apply, restrictRadiusAlgHom_X]

@[simp] theorem equationLocusRadiusMap_self (E : Set (GeneralizedTateAlgebra s A)) :
    equationLocusRadiusMap K A s s (fun _ => le_rfl) E E (radiusMapsRelations_self K A s E) =
      ContinuousMap.id (equationLocus K A s E) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro f
  simp only [equationLocusRadiusMap_apply, restrictRadiusAlgHom_self, BoundedAlgHom.id_apply]
  rfl

theorem equationLocusRadiusMap_trans (q : PositivePolyradius (Fin m))
    (hqt : ∀ j, q j ≤ t j) {G : Set (GeneralizedTateAlgebra q A)}
    (hEF : RadiusMapsRelations K A s t hts E F)
    (hFG : RadiusMapsRelations K A t q hqt F G) :
    equationLocusRadiusMap K A s q (fun j => (hqt j).trans (hts j)) E G
        (radiusMapsRelations_trans K A s t hts q hqt hEF hFG) =
      (equationLocusRadiusMap K A s t hts E F hEF).comp
        (equationLocusRadiusMap K A t q hqt F G hFG) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro f
  change x.val (restrictRadius s q (fun j => (hqt j).trans (hts j)) A f) =
    x.val (restrictRadius t q hqt A (restrictRadius s t hts A f))
  rw [restrictRadius_trans]

/-- The quotient-to-equation-locus homeomorphisms commute with radius pullback. -/
theorem spectrumHomeomorph_radius_naturality (h : RadiusMapsRelations K A s t hts E F)
    (x : BanachSpectrum (QuotientAlgebra K A t F)) :
    spectrumHomeomorph K A s E (radiusSpectrumMap K A s t hts E F h x) =
      equationLocusRadiusMap K A s t hts E F h (spectrumHomeomorph K A t F x) :=
  Subtype.ext (BanachSpectrum.ext fun _ => rfl)

section CoefficientNaturality

variable {B : PresentedAffinoidAlgebra K}
  {E' : Set (GeneralizedTateAlgebra s B)} {F' : Set (GeneralizedTateAlgebra t B)}

/-- Descended radius restriction and compatible coefficient transport commute. -/
theorem radiusMap_transport (φ : BoundedAlgHom K A B)
    (hA : RadiusMapsRelations K A s t hts E F)
    (hB : RadiusMapsRelations K B s t hts E' F')
    (hφs : MapsRelations K s φ E E') (hφt : MapsRelations K t φ F F') :
    (radiusMap K B s t hts E' F' hB).comp (transport K s E E' φ hφs) =
      (transport K t F F' φ hφt).comp (radiusMap K A s t hts E F hA) := by
  apply hom_ext K A s E (QuotientAlgebra K B t F')
  intro f
  simp only [BoundedAlgHom.comp_apply, transport_quotientMap, radiusMap_quotientMap]
  rw [restrictRadiusAlgHom_mapCoefficients]

/-- The coefficient/radius square on quotient spectra commutes contravariantly. -/
theorem radiusSpectrumMap_spectrumTransport (φ : BoundedAlgHom K A B)
    (hA : RadiusMapsRelations K A s t hts E F)
    (hB : RadiusMapsRelations K B s t hts E' F')
    (hφs : MapsRelations K s φ E E') (hφt : MapsRelations K t φ F F') :
    (spectrumTransport K s E E' φ hφs).comp (radiusSpectrumMap K B s t hts E' F' hB) =
      (radiusSpectrumMap K A s t hts E F hA).comp (spectrumTransport K t F F' φ hφt) := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (radiusMap K B s t hts E' F' hB (transport K s E E' φ hφs a)) =
    x (transport K t F F' φ hφt (radiusMap K A s t hts E F hA a))
  exact congrArg x (congrArg
    (fun ψ : BoundedAlgHom K (QuotientAlgebra K A s E) (QuotientAlgebra K B t F') => ψ a)
      (radiusMap_transport K A s t hts φ hA hB hφs hφt))

/-- The same square commutes on the common equation loci. -/
theorem equationLocusRadiusMap_equationLocusTransport (φ : BoundedAlgHom K A B)
    (hA : RadiusMapsRelations K A s t hts E F)
    (hB : RadiusMapsRelations K B s t hts E' F')
    (hφs : MapsRelations K s φ E E') (hφt : MapsRelations K t φ F F') :
    (equationLocusTransport K s E E' φ hφs).comp
        (equationLocusRadiusMap K B s t hts E' F' hB) =
      (equationLocusRadiusMap K A s t hts E F hA).comp
        (equationLocusTransport K t F F' φ hφt) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro f
  change x.val (restrictRadiusAlgHom K s t hts B (mapCoefficientsAlgHom s φ f)) =
    x.val (mapCoefficientsAlgHom t φ (restrictRadiusAlgHom K s t hts A f))
  rw [restrictRadiusAlgHom_mapCoefficients]

end CoefficientNaturality

end PresentedAffinoidAlgebra.RelativeRelations

end Langlands.Analytic
