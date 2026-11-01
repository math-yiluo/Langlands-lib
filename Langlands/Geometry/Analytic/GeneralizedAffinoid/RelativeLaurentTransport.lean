import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentGaussContinuity
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeEquationComparison

/-! # Bounded transport of the actual relative Laurent annulus -/

noncomputable section

universe u v

namespace Langlands.Analytic.RelativeLaurentAnnulus

open PresentedAffinoidAlgebra GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (t : ℝ) [Fact (0 < t)] {A B C : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
/-- Maps out of the actual annulus are determined by coefficients and the two new coordinates. -/
theorem hom_ext {D : Type v} [NormedCommRing D] [NormedAlgebra K D]
    (φ ψ : BoundedAlgHom K (algebra K A t) D)
    (hbase : ∀ a, φ (baseMap K A t a) = ψ (baseMap K A t a))
    (hcoord : ∀ j : Fin 2,
      φ (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} j) =
        ψ (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} j)) :
    φ = ψ := by
  have h : φ.comp (presentationMap K (algebra K A t)) =
      ψ.comp (presentationMap K (algebra K A t)) := by
    apply GeneralizedTateAlgebra.hom_ext
    intro i
    change φ (coordinate K (algebra K A t) i) =
      ψ (coordinate K (algebra K A t) i)
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [← Adjoin.baseMap_coordinate K A (LaurentAnnulus.radii t) {relation K A t} j]
      exact hbase (coordinate K A j)
    · intro j
      exact hcoord j
  apply BoundedAlgHom.ext
  intro b
  obtain ⟨f, rfl⟩ := presentationMap_surjective K (algebra K A t) b
  exact congrArg (fun η : BoundedAlgHom K
    (GeneralizedTateAlgebra (algebra K A t).polyradius K) D => η f) h

/-- Evaluate enlarged scalar series after the actual bounded coefficient transport. -/
def seriesTransport (φ : BoundedAlgHom K A B) :
    BoundedAlgHom K (GeneralizedTateAlgebra
      (A.polyradius.append (LaurentAnnulus.radii t)) K) (algebra K B t) :=
  (Adjoin.relativeEquationInverseEvaluation K B (LaurentAnnulus.radii t)
    {relation K B t}).comp
      ((mapCoefficientsAlgHom (LaurentAnnulus.radii t) φ).comp
        (Adjoin.relativeSeriesEvaluation K A (LaurentAnnulus.radii t)))

@[simp] theorem seriesTransport_appendLeft (φ : BoundedAlgHom K A B)
    (f : GeneralizedTateAlgebra A.polyradius K) :
    seriesTransport K t φ (appendLeft A.polyradius (LaurentAnnulus.radii t) K f) =
      baseMap K B t (φ (presentationMap K A f)) := by
  change Adjoin.relativeEquationInverseEvaluation K B (LaurentAnnulus.radii t)
    {relation K B t} (mapCoefficientsAlgHom (LaurentAnnulus.radii t) φ
      (Adjoin.relativeSeriesEvaluation K A (LaurentAnnulus.radii t)
        (appendLeft A.polyradius (LaurentAnnulus.radii t) K f))) = _
  rw [Adjoin.relativeSeriesEvaluation_appendLeft]
  change Adjoin.relativeEquationInverseEvaluation K B (LaurentAnnulus.radii t)
    {relation K B t} (mapCoefficients (LaurentAnnulus.radii t) φ.toBoundedRingHom
      (algebraMap A (GeneralizedTateAlgebra (LaurentAnnulus.radii t) A)
        (presentationMap K A f))) = _
  rw [mapCoefficients_algebraMap]
  exact Adjoin.relativeEquationInverseEvaluation_constant K B (LaurentAnnulus.radii t)
    {relation K B t} _

@[simp] theorem seriesTransport_newX (φ : BoundedAlgHom K A B) (j : Fin 2) :
    seriesTransport K t φ
      (X (A.polyradius.append (LaurentAnnulus.radii t)) K (Fin.natAdd A.arity j)) =
      Adjoin.newCoordinate K B (LaurentAnnulus.radii t) {relation K B t} j := by
  change Adjoin.relativeEquationInverseEvaluation K B (LaurentAnnulus.radii t)
    {relation K B t} (mapCoefficientsAlgHom (LaurentAnnulus.radii t) φ
      (Adjoin.relativeSeriesEvaluation K A (LaurentAnnulus.radii t)
        (X (A.polyradius.append (LaurentAnnulus.radii t)) K (Fin.natAdd A.arity j)))) = _
  rw [Adjoin.relativeSeriesEvaluation_X, Adjoin.relativeSeriesTuple_natAdd]
  change Adjoin.relativeEquationInverseEvaluation K B (LaurentAnnulus.radii t)
    {relation K B t} (mapCoefficients (LaurentAnnulus.radii t) φ.toBoundedRingHom
      (X (LaurentAnnulus.radii t) A j)) = _
  rw [mapCoefficients_X, Adjoin.relativeEquationInverseEvaluation_X]

/-- Both the original ideal and the inverse relation vanish after coefficient transport. -/
theorem seriesTransport_relations (φ : BoundedAlgHom K A B) :
    ∀ f ∈ Adjoin.relations K A (LaurentAnnulus.radii t) {relation K A t},
      seriesTransport K t φ f = 0 := by
  intro f hf
  rcases hf with ⟨g, hg, rfl⟩ | hf
  · rw [seriesTransport_appendLeft, (presentationMap_eq_zero_iff K A g).mpr hg,
      map_zero, map_zero]
  · rw [Set.mem_singleton_iff] at hf
    subst f
    unfold relation
    rw [map_sub, map_mul, map_one, seriesTransport_newX, seriesTransport_newX]
    exact sub_eq_zero.mpr (coordinate_mul K B t)

/-- The actual bounded map of annulus quotients induced by a bounded coefficient map. -/
def transport (φ : BoundedAlgHom K A B) :
    BoundedAlgHom K (algebra K A t) (algebra K B t) :=
  descendRelations K (A.arity + 2) (A.polyradius.append (LaurentAnnulus.radii t))
    (Adjoin.relations K A (LaurentAnnulus.radii t) {relation K A t})
    (algebra K B t) (seriesTransport K t φ) (seriesTransport_relations K t φ)

@[simp] theorem transport_presentationMap (φ : BoundedAlgHom K A B)
    (f : GeneralizedTateAlgebra (A.polyradius.append (LaurentAnnulus.radii t)) K) :
    transport K t φ (presentationMap K (algebra K A t) f) =
      seriesTransport K t φ f := rfl

@[simp] theorem transport_baseMap (φ : BoundedAlgHom K A B) (a : A) :
    transport K t φ (baseMap K A t a) = baseMap K B t (φ a) := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K A a
  exact seriesTransport_appendLeft K t φ f

@[simp] theorem transport_newCoordinate (φ : BoundedAlgHom K A B) (j : Fin 2) :
    transport K t φ
      (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} j) =
      Adjoin.newCoordinate K B (LaurentAnnulus.radii t) {relation K B t} j :=
  seriesTransport_newX K t φ j

theorem transport_comp_baseMap (φ : BoundedAlgHom K A B) :
    (transport K t φ).comp (baseMap K A t) = (baseMap K B t).comp φ :=
  BoundedAlgHom.ext (transport_baseMap K t φ)

@[simp] theorem transport_id :
    transport K t (BoundedAlgHom.id K A) = BoundedAlgHom.id K (algebra K A t) := by
  apply hom_ext K t
  · intro a
    simp only [transport_baseMap, BoundedAlgHom.id_apply]
  · intro j
    simp only [transport_newCoordinate, BoundedAlgHom.id_apply]

@[simp] theorem transport_comp (ψ : BoundedAlgHom K B C) (φ : BoundedAlgHom K A B) :
    transport K t (ψ.comp φ) = (transport K t ψ).comp (transport K t φ) := by
  apply hom_ext K t
  · intro a
    simp only [transport_baseMap, BoundedAlgHom.comp_apply]
  · intro j
    simp only [transport_newCoordinate, BoundedAlgHom.comp_apply]

/-- Every positive coefficient bound gives the same bound on the actual annulus quotient. -/
theorem norm_transport_le (φ : BoundedAlgHom K A B) {c : ℝ} (hc : 0 < c)
    (hφ : ∀ a, ‖φ a‖ ≤ c * ‖a‖) (b : algebra K A t) :
    ‖transport K t φ b‖ ≤ c * ‖b‖ := by
  apply norm_descendRelations_le K (A.arity + 2)
    (A.polyradius.append (LaurentAnnulus.radii t))
    (Adjoin.relations K A (LaurentAnnulus.radii t) {relation K A t})
    (algebra K B t) (seriesTransport K t φ) (seriesTransport_relations K t φ) c hc
  intro f
  exact (Adjoin.norm_relativeEquationInverseEvaluation_le K B (LaurentAnnulus.radii t)
    {relation K B t} _).trans <|
      (norm_mapCoefficientsAlgHom_le (LaurentAnnulus.radii t) φ hc.le hφ _).trans <|
        mul_le_mul_of_nonneg_left
          (Adjoin.norm_relativeSeriesEvaluation_le K A (LaurentAnnulus.radii t) f) hc.le

/-- Transport preserves the actual Laurent unit. -/
theorem transport_coordinateUnit (φ : BoundedAlgHom K A B) :
    Units.map (transport K t φ).toAlgHom.toRingHom.toMonoidHom (coordinateUnit K A t) =
      coordinateUnit K B t := by
  apply Units.ext
  exact transport_newCoordinate K t φ 0

/-- Integer powers of the Laurent variable commute with transport. -/
theorem transport_coordinateUnit_zpow (φ : BoundedAlgHom K A B) (n : ℤ) :
    transport K t φ (↑((coordinateUnit K A t) ^ n) : algebra K A t) =
      (↑((coordinateUnit K B t) ^ n) : algebra K B t) := by
  have h := congrArg (fun b : (algebra K B t)ˣ => (↑(b ^ n) : algebra K B t))
    (transport_coordinateUnit K t φ)
  rw [← map_zpow, Units.coe_map] at h
  exact h

/-- Transport of finite Laurent expressions is coefficientwise transport. -/
theorem transport_polynomialMap (φ : BoundedAlgHom K A B) (p : AddMonoidAlgebra A ℤ) :
    transport K t φ (polynomialMap K A t p) =
      polynomialMap K B t (AddMonoidAlgebra.mapRingHom ℤ φ.toAlgHom.toRingHom p) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | single n a =>
    rw [AddMonoidAlgebra.mapRingHom_single, polynomialMap_single, polynomialMap_single,
      map_mul, transport_baseMap, transport_coordinateUnit_zpow]
    rfl

/-- A finite expression has the norm of its coefficientwise residue Laurent polynomial. -/
theorem sectionPoint_polynomialMap_norm (x : BanachSpectrum A) (p : AddMonoidAlgebra A ℤ) :
    sectionPoint K A t x (polynomialMap K A t p) =
      ‖residuePolynomial K A t x p‖ := by
  rw [sectionPoint_apply]
  calc
    _ = ‖((residuePolynomial K A t x p) :
        CompletedGaussLaurent (BanachSpectrum.CompletedResidueField K x) t)‖ :=
      congrArg (fun z : CompletedGaussLaurent
        (BanachSpectrum.CompletedResidueField K x) t => ‖z‖)
        (evaluation_polynomialMap K A t x p)
    _ = _ := UniformSpace.Completion.norm_coe _

omit [CompleteSpace K] in
/-- Residue Laurent polynomials on either side of transport have equal Gauss norms. -/
theorem norm_residuePolynomial_transport (φ : BoundedAlgHom K A B) (y : BanachSpectrum B)
    (p : AddMonoidAlgebra A ℤ) :
    ‖residuePolynomial K B t y
        (AddMonoidAlgebra.mapRingHom ℤ φ.toAlgHom.toRingHom p)‖ =
      ‖residuePolynomial K A t (BanachSpectrum.comap φ.toBoundedRingHom y) p‖ := by
  have hcoeff (n : ℤ) :
      ‖GaussLaurent.coeff (residuePolynomial K B t y
        (AddMonoidAlgebra.mapRingHom ℤ φ.toAlgHom.toRingHom p)) n‖ =
      ‖GaussLaurent.coeff
        (residuePolynomial K A t (BanachSpectrum.comap φ.toBoundedRingHom y) p) n‖ := by
    rw [residuePolynomial_coeff, norm_completedResidueMap, residuePolynomial_coeff,
      norm_completedResidueMap, AddMonoidAlgebra.coeff_mapRingHom]
    rfl
  apply le_antisymm
  · apply (GaussLaurent.norm_le_iff _ (norm_nonneg _)).mpr
    intro n
    rw [hcoeff]
    exact GaussLaurent.norm_coeff_mul_le _ n
  · apply (GaussLaurent.norm_le_iff _ (norm_nonneg _)).mpr
    intro n
    rw [← hcoeff]
    exact GaussLaurent.norm_coeff_mul_le _ n

/-- Naturality holds on the dense finite Laurent expressions. -/
theorem sectionPoint_transport_polynomialMap (φ : BoundedAlgHom K A B)
    (y : BanachSpectrum B) (p : AddMonoidAlgebra A ℤ) :
    sectionPoint K B t y (transport K t φ (polynomialMap K A t p)) =
      sectionPoint K A t (BanachSpectrum.comap φ.toBoundedRingHom y)
        (polynomialMap K A t p) := by
  rw [transport_polynomialMap, sectionPoint_polynomialMap_norm,
    sectionPoint_polynomialMap_norm]
  exact norm_residuePolynomial_transport K t φ y p

/-- The Gauss section commutes with every bounded coefficient algebra map. -/
theorem comap_transport_sectionPoint (φ : BoundedAlgHom K A B) (y : BanachSpectrum B) :
    BanachSpectrum.comap (transport K t φ).toBoundedRingHom (sectionPoint K B t y) =
      sectionPoint K A t (BanachSpectrum.comap φ.toBoundedRingHom y) := by
  apply BanachSpectrum.ext
  have h := (denseRange_polynomialMap K A t).equalizer
    (g := fun b : algebra K A t => sectionPoint K B t y (transport K t φ b))
    (h := fun b : algebra K A t =>
      sectionPoint K A t (BanachSpectrum.comap φ.toBoundedRingHom y) b)
    (continuous_const.banachSpectrum_apply (transport K t φ).continuous)
    (continuous_const.banachSpectrum_apply continuous_id)
    (funext (sectionPoint_transport_polynomialMap K t φ y))
  exact congr_fun h

/-- Naturality as an equality of continuous maps. -/
theorem comap_transport_comp_gaussSection (φ : BoundedAlgHom K A B) :
    (BanachSpectrum.comapContinuous (transport K t φ).toBoundedRingHom).comp
        (gaussSection K B t) =
      (gaussSection K A t).comp (BanachSpectrum.comapContinuous φ.toBoundedRingHom) := by
  apply ContinuousMap.ext
  exact comap_transport_sectionPoint K t φ

end Langlands.Analytic.RelativeLaurentAnnulus
