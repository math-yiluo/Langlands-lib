import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRelationsTransport
import Langlands.Geometry.Analytic.Spectrum.Quotient
import Langlands.Geometry.Analytic.Spectrum.JointContinuityProof

/-! # Relative closed-equation quotient spectra and coefficient transport -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRelations

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (A : PresentedAffinoidAlgebra K) {m : ℕ} (s : PositivePolyradius (Fin m))
  (E : Set (GeneralizedTateAlgebra s A))

/-- The common zero set of the supplied relative series equations. -/
def equationLocus : Set (BanachSpectrum (GeneralizedTateAlgebra s A)) :=
  {x | ∀ f ∈ E, x f = 0}

/-- Vanishing on the equations is equivalent to vanishing on their closed ideal. -/
theorem mem_equationLocus_iff (x : BanachSpectrum (GeneralizedTateAlgebra s A)) :
    x ∈ equationLocus K A s E ↔ ideal K A s E ≤ x.kernel := by
  constructor
  · intro hx
    have hspan : Ideal.span E ≤ x.kernel := Ideal.span_le.mpr hx
    have hclosed : IsClosed (x.kernel : Set (GeneralizedTateAlgebra s A)) :=
      isClosed_eq (continuous_const.banachSpectrum_apply continuous_id) continuous_const
    exact closure_minimal hspan hclosed
  · intro hx f hf
    exact hx (equation_mem K A s E hf)

theorem equationLocus_eq_zeroLocus :
    equationLocus K A s E = BanachSpectrum.zeroLocus (ideal K A s E) :=
  Set.ext fun x => mem_equationLocus_iff K A s E x

theorem isClosed_equationLocus : IsClosed (equationLocus K A s E) := by
  rw [equationLocus_eq_zeroLocus]
  exact BanachSpectrum.isClosed_zeroLocus _

theorem isCompact_equationLocus : IsCompact (equationLocus K A s E) :=
  (isClosed_equationLocus K A s E).isCompact

instance : CompactSpace (equationLocus K A s E) :=
  isCompact_iff_compactSpace.mp (isCompact_equationLocus K A s E)

/-- Pullback along the actual relative quotient projection. -/
def spectrumMap :
    C(BanachSpectrum (QuotientAlgebra K A s E),
      BanachSpectrum (GeneralizedTateAlgebra s A)) :=
  BanachSpectrum.comapContinuous (quotientMap K A s E).toBoundedRingHom

@[simp] theorem spectrumMap_apply (x : BanachSpectrum (QuotientAlgebra K A s E))
    (f : GeneralizedTateAlgebra s A) :
    spectrumMap K A s E x f = x (quotientMap K A s E f) := rfl

theorem isClosedEmbedding_spectrumMap : Topology.IsClosedEmbedding (spectrumMap K A s E) :=
  BanachSpectrum.comap_quotient_closedEmbedding (ideal K A s E)

theorem range_spectrumMap : Set.range (spectrumMap K A s E) = equationLocus K A s E := by
  rw [equationLocus_eq_zeroLocus]
  exact BanachSpectrum.range_comap_quotient (ideal K A s E)

theorem spectrumMap_mem_equationLocus (x : BanachSpectrum (QuotientAlgebra K A s E)) :
    spectrumMap K A s E x ∈ equationLocus K A s E := by
  rw [← range_spectrumMap]
  exact ⟨x, rfl⟩

/-- The spectrum of the actual quotient is homeomorphic to the common equation
zero set in the relative series spectrum. The inverse descends the seminorm. -/
def spectrumHomeomorph :
    BanachSpectrum (QuotientAlgebra K A s E) ≃ₜ equationLocus K A s E where
  toFun x := ⟨spectrumMap K A s E x, spectrumMap_mem_equationLocus K A s E x⟩
  invFun x := BanachSpectrum.descend (ideal K A s E) x.val
    ((mem_equationLocus_iff K A s E x.val).mp x.property)
  left_inv x := by
    apply BanachSpectrum.ext
    intro a
    obtain ⟨f, rfl⟩ := quotientMap_surjective K A s E a
    rfl
  right_inv x := Subtype.ext (BanachSpectrum.ext fun _ => rfl)
  continuous_toFun := (spectrumMap K A s E).continuous.subtype_mk _
  continuous_invFun := continuous_induced_rng.mpr <| continuous_pi fun a => by
    obtain ⟨f, rfl⟩ := quotientMap_surjective K A s E a
    exact (BanachSpectrum.evaluation f).continuous.comp continuous_subtype_val

@[simp] theorem spectrumHomeomorph_apply
    (x : BanachSpectrum (QuotientAlgebra K A s E)) (f : GeneralizedTateAlgebra s A) :
    (spectrumHomeomorph K A s E x).val f = x (quotientMap K A s E f) := rfl

@[simp] theorem spectrumHomeomorph_symm_apply
    (x : equationLocus K A s E) (f : GeneralizedTateAlgebra s A) :
    (spectrumHomeomorph K A s E).symm x (quotientMap K A s E f) = x.val f := rfl

section CoefficientTransport

variable {A} {B C : PresentedAffinoidAlgebra K}
  {E} {F : Set (GeneralizedTateAlgebra s B)} {G : Set (GeneralizedTateAlgebra s C)}

/-- The continuous contravariant map induced by actual quotient coefficient transport. -/
def spectrumTransport (E : Set (GeneralizedTateAlgebra s A))
    (F : Set (GeneralizedTateAlgebra s B))
    (φ : BoundedAlgHom K A B) (hφ : MapsRelations K s φ E F) :
    C(BanachSpectrum (QuotientAlgebra K B s F), BanachSpectrum (QuotientAlgebra K A s E)) :=
  BanachSpectrum.comapContinuous (transport K s E F φ hφ).toBoundedRingHom

@[simp] theorem spectrumTransport_apply (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) (x : BanachSpectrum (QuotientAlgebra K B s F))
    (a : QuotientAlgebra K A s E) :
    spectrumTransport K s E F φ hφ x a = x (transport K s E F φ hφ a) := rfl

@[simp] theorem spectrumTransport_quotientMap (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) (x : BanachSpectrum (QuotientAlgebra K B s F))
    (f : GeneralizedTateAlgebra s A) :
    spectrumTransport K s E F φ hφ x (quotientMap K A s E f) =
      x (quotientMap K B s F (mapCoefficientsAlgHom s φ f)) := rfl

@[simp] theorem spectrumTransport_baseMap (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) (x : BanachSpectrum (QuotientAlgebra K B s F)) (a : A) :
    spectrumTransport K s E F φ hφ x (baseMap K A s E a) =
      x (baseMap K B s F (φ a)) := by
  rw [spectrumTransport_apply, transport_baseMap]

@[simp] theorem spectrumTransport_newCoordinate (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) (x : BanachSpectrum (QuotientAlgebra K B s F))
    (j : Fin m) :
    spectrumTransport K s E F φ hφ x (newCoordinate K A s E j) =
      x (newCoordinate K B s F j) := by
  rw [spectrumTransport_apply, transport_newCoordinate]

@[simp] theorem spectrumTransport_id (E : Set (GeneralizedTateAlgebra s A)) :
    spectrumTransport K s E E (BoundedAlgHom.id K A) (mapsRelations_id K s E) =
      ContinuousMap.id (BanachSpectrum (QuotientAlgebra K A s E)) := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  rw [spectrumTransport_apply, transport_id]
  rfl

/-- Pullback reverses composition of coefficient maps. -/
@[simp] theorem spectrumTransport_comp (ψ : BoundedAlgHom K B C) (φ : BoundedAlgHom K A B)
    (hψ : MapsRelations K s ψ F G) (hφ : MapsRelations K s φ E F) :
    spectrumTransport K s E G (ψ.comp φ) (mapsRelations_comp K s ψ φ hψ hφ) =
      (spectrumTransport K s E F φ hφ).comp (spectrumTransport K s F G ψ hψ) := by
  apply ContinuousMap.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  change x (transport K s E G (ψ.comp φ) (mapsRelations_comp K s ψ φ hψ hφ) a) =
    x (transport K s F G ψ hψ (transport K s E F φ hφ a))
  rw [transport_comp K s ψ φ hψ hφ]
  rfl

/-- The coefficientwise spectrum pullback restricts to the common equation loci. -/
def equationLocusTransport (E : Set (GeneralizedTateAlgebra s A))
    (F : Set (GeneralizedTateAlgebra s B))
    (φ : BoundedAlgHom K A B) (hφ : MapsRelations K s φ E F) :
    C(equationLocus K B s F, equationLocus K A s E) where
  toFun x := ⟨BanachSpectrum.comap (mapCoefficientsAlgHom s φ).toBoundedRingHom x.val,
    fun f hf => (mem_equationLocus_iff K B s F x.val).mp x.property (hφ f hf)⟩
  continuous_toFun := ((BanachSpectrum.comapContinuous
    (mapCoefficientsAlgHom s φ).toBoundedRingHom).continuous.comp
      continuous_subtype_val).subtype_mk _

@[simp] theorem equationLocusTransport_apply (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) (x : equationLocus K B s F)
    (f : GeneralizedTateAlgebra s A) :
    (equationLocusTransport K s E F φ hφ x).val f =
      x.val (mapCoefficientsAlgHom s φ f) := rfl

@[simp] theorem equationLocusTransport_constant (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) (x : equationLocus K B s F) (a : A) :
    (equationLocusTransport K s E F φ hφ x).val (constantAlgHom s K A a) =
      x.val (constantAlgHom s K B (φ a)) := by
  rw [equationLocusTransport_apply]
  exact congrArg x.val (mapCoefficients_algebraMap s φ.toBoundedRingHom a)

@[simp] theorem equationLocusTransport_X (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) (x : equationLocus K B s F) (j : Fin m) :
    (equationLocusTransport K s E F φ hφ x).val (X s A j) = x.val (X s B j) := by
  rw [equationLocusTransport_apply, mapCoefficientsAlgHom_apply, mapCoefficients_X]

@[simp] theorem equationLocusTransport_id (E : Set (GeneralizedTateAlgebra s A)) :
    equationLocusTransport K s E E (BoundedAlgHom.id K A) (mapsRelations_id K s E) =
      ContinuousMap.id (equationLocus K A s E) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro f
  simp only [equationLocusTransport_apply, mapCoefficientsAlgHom_id, BoundedAlgHom.id_apply]
  rfl

@[simp] theorem equationLocusTransport_comp (ψ : BoundedAlgHom K B C)
    (φ : BoundedAlgHom K A B) (hψ : MapsRelations K s ψ F G)
    (hφ : MapsRelations K s φ E F) :
    equationLocusTransport K s E G (ψ.comp φ) (mapsRelations_comp K s ψ φ hψ hφ) =
      (equationLocusTransport K s E F φ hφ).comp
        (equationLocusTransport K s F G ψ hψ) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro f
  change x.val (mapCoefficientsAlgHom s (ψ.comp φ) f) =
    x.val (mapCoefficientsAlgHom s ψ (mapCoefficientsAlgHom s φ f))
  rw [mapCoefficientsAlgHom_comp]
  rfl

/-- The quotient-to-locus homeomorphisms commute with coefficient pullback. -/
theorem spectrumHomeomorph_naturality (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) (x : BanachSpectrum (QuotientAlgebra K B s F)) :
    spectrumHomeomorph K A s E (spectrumTransport K s E F φ hφ x) =
      equationLocusTransport K s E F φ hφ (spectrumHomeomorph K B s F x) :=
  Subtype.ext (BanachSpectrum.ext fun _ => rfl)

/-- A supplied compatible bounded base equivalence induces a homeomorphism of
quotient spectra; norm preservation of the base equivalence is unnecessary. -/
def spectrumTransportHomeomorph (E : Set (GeneralizedTateAlgebra s A))
    (F : Set (GeneralizedTateAlgebra s B)) (e : BoundedAlgEquiv K A B)
    (hAB : MapsRelations K s e.toBoundedAlgHom E F)
    (hBA : MapsRelations K s e.symm.toBoundedAlgHom F E) :
    BanachSpectrum (QuotientAlgebra K B s F) ≃ₜ
      BanachSpectrum (QuotientAlgebra K A s E) :=
  (transportEquiv K s E F e hAB hBA).spectrumHomeomorph

@[simp] theorem spectrumTransportHomeomorph_apply (e : BoundedAlgEquiv K A B)
    (hAB : MapsRelations K s e.toBoundedAlgHom E F)
    (hBA : MapsRelations K s e.symm.toBoundedAlgHom F E)
    (x : BanachSpectrum (QuotientAlgebra K B s F)) :
    spectrumTransportHomeomorph K s E F e hAB hBA x =
      spectrumTransport K s E F e.toBoundedAlgHom hAB x := rfl

@[simp] theorem spectrumTransportHomeomorph_symm_apply (e : BoundedAlgEquiv K A B)
    (hAB : MapsRelations K s e.toBoundedAlgHom E F)
    (hBA : MapsRelations K s e.symm.toBoundedAlgHom F E)
    (x : BanachSpectrum (QuotientAlgebra K A s E)) :
    (spectrumTransportHomeomorph K s E F e hAB hBA).symm x =
      spectrumTransport K s F E e.symm.toBoundedAlgHom hBA x := rfl

/-- Conjugating quotient-spectrum transport gives the homeomorphism of equation loci. -/
def equationLocusHomeomorph (E : Set (GeneralizedTateAlgebra s A))
    (F : Set (GeneralizedTateAlgebra s B)) (e : BoundedAlgEquiv K A B)
    (hAB : MapsRelations K s e.toBoundedAlgHom E F)
    (hBA : MapsRelations K s e.symm.toBoundedAlgHom F E) :
    equationLocus K B s F ≃ₜ equationLocus K A s E :=
  (spectrumHomeomorph K B s F).symm.trans
    ((spectrumTransportHomeomorph K s E F e hAB hBA).trans
      (spectrumHomeomorph K A s E))

@[simp] theorem equationLocusHomeomorph_apply (e : BoundedAlgEquiv K A B)
    (hAB : MapsRelations K s e.toBoundedAlgHom E F)
    (hBA : MapsRelations K s e.symm.toBoundedAlgHom F E) (x : equationLocus K B s F) :
    equationLocusHomeomorph K s E F e hAB hBA x =
      equationLocusTransport K s E F e.toBoundedAlgHom hAB x :=
  Subtype.ext (BanachSpectrum.ext fun _ => rfl)

@[simp] theorem equationLocusHomeomorph_symm_apply (e : BoundedAlgEquiv K A B)
    (hAB : MapsRelations K s e.toBoundedAlgHom E F)
    (hBA : MapsRelations K s e.symm.toBoundedAlgHom F E) (x : equationLocus K A s E) :
    (equationLocusHomeomorph K s E F e hAB hBA).symm x =
      equationLocusTransport K s F E e.symm.toBoundedAlgHom hBA x :=
  Subtype.ext (BanachSpectrum.ext fun _ => rfl)

end CoefficientTransport

end Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRelations
