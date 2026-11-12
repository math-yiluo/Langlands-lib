import Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointMaps
import Langlands.Global.AdelicSpacePointTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyUniqueness
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasSchemeCompatibilityProof
import Langlands.AlgebraicGeometry.PointTopology.SchemeBaseChangeTopologyProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeCoefficientProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeSeparatedCoefficientProofs

/-!
# Point topologies of schemes viewed as algebraic spaces

For a scheme `U` over a ring `C`, the points of the associated algebraic space carry the
field-valued and coordinate topologies of `Langlands.Global.AdelicSpaceLevelTopology`, and the
points of `U` carry the scheme point topology. This module compares them. Along an open
embedding `R → L` of a local topological ring into a henselian valued field, the field-valued
topology on the `R`-points of the space is the scheme topology on `U(R)`. Consequently the
coordinate topology is the topology induced from the product of the scheme topologies of the
local base changes of `U`.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (RingPoint ringTest ringTestMap ringBaseChange
  ringPointBaseChangeEquiv schemePointTopology IsHenselianValuedField ringTestRestrictScalarsIso
  schemeBaseChangeTopology_proof schemeCoefficientContinuity_proof schemeCoefficientOpen_proof
  schemeSeparatedCoefficientInjectivity_proof)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace SchemeSpacePointComparison

open CoordinatePointTopologyFacts

section BaseChange

variable (C D A : Type u) [CommRing C] [CommRing D] [CommRing A] [Algebra C D] [Algebra C A]
  [Algebra D A] [IsScalarTower C D A] (U : Over (Spec (CommRingCat.of C)))

/-- The point identification of the base change of the space of a scheme agrees with the
point identification of the base-changed scheme. -/
theorem baseChangeRingPointsEquiv_scheme (r : RingPoint D (ringBaseChange C D U) A) :
    baseChangeRingPointsEquiv C D A ((schemeToSpace _).obj U)
        (RingPoints.map (baseChangeSchemeIso (Spec.algebraMap C D) U).hom
          ((schemeRingPointsEquiv D (ringBaseChange C D U) A).symm r)) =
      (schemeRingPointsEquiv C U A).symm ((ringPointBaseChangeEquiv C D A U).symm r) := by
  rfl

/-- The base change identifications of points of a scheme and of its space agree. -/
theorem ringPointBaseChangeEquiv_scheme (p : RingPoints C ((schemeToSpace _).obj U) A) :
    ringPointBaseChangeEquiv C D A U (schemeRingPointsEquiv C U A p) =
      schemeRingPointsEquiv D (ringBaseChange C D U) A
        (RingPoints.map (baseChangeSchemeIso (Spec.algebraMap C D) U).inv
          ((baseChangeRingPointsEquiv C D A ((schemeToSpace _).obj U)).symm p)) := by
  apply (ringPointBaseChangeEquiv C D A U).symm.injective
  rw [Equiv.symm_apply_apply]
  apply (schemeRingPointsEquiv C U A).symm.injective
  rw [Equiv.symm_apply_apply, ← baseChangeRingPointsEquiv_scheme, Equiv.symm_apply_apply]
  have h : ∀ z, RingPoints.map (baseChangeSchemeIso (Spec.algebraMap C D) U).hom
      (RingPoints.map (A := A) (baseChangeSchemeIso (Spec.algebraMap C D) U).inv z) = z :=
    fun z => by rw [← RingPoints.map_comp, Iso.inv_hom_id, RingPoints.map_id]
  exact ((congrArg (baseChangeRingPointsEquiv C D A ((schemeToSpace _).obj U)) (h _)).trans
    (Equiv.apply_symm_apply _ _)).symm

end BaseChange

variable {C : Type u} [CommRing C] (U : Over (Spec (CommRingCat.of C)))

/-- The scheme point identification commutes with change of coefficients. -/
theorem schemeRingPointsEquiv_changeRing {A B : Type u} [CommRing A] [CommRing B] [Algebra C A]
    [Algebra C B] (φ : A →ₐ[C] B) (x : RingPoints C ((schemeToSpace _).obj U) A) :
    schemeRingPointsEquiv C U B (RingPoints.changeRing φ x) =
      (schemeRingPointsEquiv C U A x).changeRing φ :=
  rfl

/-- An equivalence is a homeomorphism when the source topology is induced from the target. -/
theorem isHomeomorph_of_eq_induced {α β : Type*} (tα : TopologicalSpace α)
    (tβ : TopologicalSpace β) (e : α ≃ β) (h : tα = TopologicalSpace.induced e tβ) :
    @IsHomeomorph _ _ tα tβ e :=
  @isHomeomorph_iff_isEmbedding_surjective _ _ tα tβ e |>.mpr ⟨⟨⟨h⟩, e.injective⟩, e.surjective⟩

section Field

variable {L : Type u} [NontriviallyNormedField L] [Algebra C L]

/-- The field-valued point map of the space of a scheme, read through the base-changed scheme. -/
theorem fieldValuedPointMap_id_scheme (q : RingPoint C U L) :
    fieldValuedPointMap C ((schemeToSpace _).obj U) (AlgHom.id C L)
        ((schemeRingPointsEquiv C U L).symm q) =
      RingPoints.map (baseChangeSchemeIso (Spec.algebraMap C L) U).hom
        ((schemeRingPointsEquiv L (ringBaseChange C L U) L).symm
          (ringPointBaseChangeEquiv C L L U q)) := by
  rw [fieldValuedPointMap, Equiv.symm_apply_eq, baseChangeRingPointsEquiv_scheme,
    Equiv.symm_apply_apply]
  change ((schemeToSpace _).obj U).pullback (ringTestMap C (AlgHom.id C L)) _ = _
  rw [Langlands.AlgebraicGeometry.PointTopology.ringTestMap_id]
  exact pullback_id _ _ _

/-- **Fields.** Over a henselian valued field `L`, the field-valued topology on the `L`-points
of the space of a quasi-separated scheme locally of finite type is the scheme topology. -/
theorem isHomeomorph_field (hK : IsHenselianValuedField L) [LocallyOfFiniteType U.hom]
    [QuasiSeparated U.hom] :
    @IsHomeomorph _ _ (fieldValuedPointTopology C ((schemeToSpace _).obj U) (AlgHom.id C L))
      (schemePointTopology C U L) (schemeRingPointsEquiv C U L) := by
  let _ : TopologicalSpace (RingPoint C U L) := schemePointTopology C U L
  let _ : TopologicalSpace (RingPoint L (ringBaseChange C L U) L) :=
    schemePointTopology L (ringBaseChange C L U) L
  let _ : TopologicalSpace (RingPoints L ((schemeToSpace _).obj (ringBaseChange C L U)) L) :=
    etaleChartTopology L _
  let _ : TopologicalSpace (RingPoints L
      ((schemeToSpace _).obj ((Over.pullback (Spec.algebraMap C L)).obj U)) L) :=
    etaleChartTopology L _
  let _ : TopologicalSpace (RingPoints L
      (baseChange (Spec.algebraMap C L) ((schemeToSpace _).obj U)) L) := etaleChartTopology L _
  have h₁ := schemeBaseChangeTopology_proof C L L U
  have : QuasiSeparated (ringBaseChange C L U).hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback U.hom (Spec.algebraMap C L)) (inferInstanceAs (QuasiSeparated U.hom))
  have : LocallyOfFiniteType (ringBaseChange C L U).hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback U.hom (Spec.algebraMap C L))
      (inferInstanceAs (LocallyOfFiniteType U.hom))
  have hUL : IsQuasiSeparatedLocallyFiniteType L
      ((schemeToSpace _).obj (ringBaseChange C L U)) :=
    ⟨isQuasiSeparated_schemeToSpace _,
      (locallyOfFiniteTypeOverBase_schemeToSpace_iff _).mpr inferInstance⟩
  have h₂ := isHomeomorph_schemeRingPointsEquiv hK _ hUL
  have h₂s : IsHomeomorph (schemeRingPointsEquiv L (ringBaseChange C L U) L).symm :=
    (schemeRingPointsEquiv L (ringBaseChange C L U) L).symm.isHomeomorph_iff.mpr
      ⟨(schemeRingPointsEquiv L (ringBaseChange C L U) L).continuous_symm_iff.mpr h₂.isOpenMap,
        h₂.continuous⟩
  have h₃ : IsHomeomorph (RingPoints.map (A := L)
      (baseChangeSchemeIso (Spec.algebraMap C L) U).hom) :=
    isHomeomorph_ringPointsMap_of_iso (baseChangeSchemeIso (Spec.algebraMap C L) U)
  have hΦ := h₃.comp (h₂s.comp h₁)
  apply isHomeomorph_of_eq_induced
  rw [hΦ.isInducing.eq_induced, induced_compose, fieldValuedPointTopology]
  congr 1
  funext p
  have h := fieldValuedPointMap_id_scheme U (schemeRingPointsEquiv C U L p)
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- **Open coefficient embeddings.** Along an open embedding `φ : R → L` of a reduced local
topological ring with open units into a henselian valued field, the field-valued topology on
the `R`-points of the space of a separated scheme locally of finite type is the scheme
topology. -/
theorem isHomeomorph_factor {R : Type u} [CommRing R] [Algebra C R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLocalRing R] [IsOpenUnits R] [_root_.IsReduced R]
    (hK : IsHenselianValuedField L) [LocallyOfFiniteType U.hom] [_root_.AlgebraicGeometry.IsSeparated U.hom]
    (φ : R →ₐ[C] L) (hφ : IsOpenEmbedding φ) :
    @IsHomeomorph _ _ (fieldValuedPointTopology C ((schemeToSpace _).obj U) φ)
      (schemePointTopology C U R) (schemeRingPointsEquiv C U R) := by
  have hL := isHomeomorph_field U hK
  let _ : TopologicalSpace (RingPoint C U R) := schemePointTopology C U R
  let _ : TopologicalSpace (RingPoint C U L) := schemePointTopology C U L
  have hc : IsInducing (RingPoint.changeRing (X := U) φ) :=
    (IsOpenEmbedding.of_continuous_injective_isOpenMap
      (schemeCoefficientContinuity_proof C R L U φ hφ.continuous)
      (schemeSeparatedCoefficientInjectivity_proof C R L U φ hφ.injective)
      (schemeCoefficientOpen_proof C R L U φ hφ)).isInducing
  apply isHomeomorph_of_eq_induced
  calc fieldValuedPointTopology C ((schemeToSpace _).obj U) φ
      = TopologicalSpace.induced (RingPoints.changeRing φ)
          (fieldValuedPointTopology C ((schemeToSpace _).obj U) (AlgHom.id C L)) := by
        rw [fieldValuedPointTopology, fieldValuedPointTopology, induced_compose]
        congr 1
        funext x
        rw [Function.comp_apply, ← fieldValuedPointMap_comp, AlgHom.id_comp]
    _ = TopologicalSpace.induced (RingPoints.changeRing φ)
          (TopologicalSpace.induced (schemeRingPointsEquiv C U L) (schemePointTopology C U L)) := by
        congr 1
        let _ := fieldValuedPointTopology C ((schemeToSpace _).obj U) (AlgHom.id C L)
        exact hL.isInducing.eq_induced
    _ = TopologicalSpace.induced (schemeRingPointsEquiv C U R)
          (TopologicalSpace.induced (RingPoint.changeRing φ) (schemePointTopology C U L)) := by
        rw [induced_compose, induced_compose]
        rfl
    _ = TopologicalSpace.induced (schemeRingPointsEquiv C U R) (schemePointTopology C U R) := by
        rw [← hc.eq_induced]

/-- The same comparison, followed by the base change of `U` to `R`. -/
theorem isHomeomorph_localFactor {R : Type u} [CommRing R] [Algebra C R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLocalRing R] [IsOpenUnits R] [_root_.IsReduced R]
    (hK : IsHenselianValuedField L) [LocallyOfFiniteType U.hom] [_root_.AlgebraicGeometry.IsSeparated U.hom]
    (φ : R →ₐ[C] L) (hφ : IsOpenEmbedding φ) :
    @IsHomeomorph _ _ (fieldValuedPointTopology C ((schemeToSpace _).obj U) φ)
      (schemePointTopology R (ringBaseChange C R U) R)
      (fun p => ringPointBaseChangeEquiv C R R U (schemeRingPointsEquiv C U R p)) :=
  @IsHomeomorph.comp _ _ _ (fieldValuedPointTopology C ((schemeToSpace _).obj U) φ)
    (schemePointTopology C U R) (schemePointTopology R (ringBaseChange C R U) R) _ _
    (schemeBaseChangeTopology_proof C R R U) (isHomeomorph_factor U hK φ hφ)

end Field

section Coordinates

variable {ι : Type*} (R L : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
  [∀ i, TopologicalSpace (R i)] [∀ i, Field (L i)] [∀ i, Algebra C (L i)]
  [∀ i, TopologicalSpace (L i)] {A : Type u} [CommRing A] [Algebra C A]
  (φ : ∀ i, R i →ₐ[C] L i) (π : ∀ i, A →ₐ[C] R i)

/-- The local-model point map of the scheme `U`: restrict to each factor, then base change. -/
def localModelMap : RingPoint C U A → ∀ i, RingPoint (R i) (ringBaseChange C (R i) U) (R i) :=
  fun p i => ringPointBaseChangeEquiv C (R i) (R i) U (p.changeRing (π i))

/-- The product of the scheme topologies of the local base changes. -/
abbrev localModelProductTopology :
    TopologicalSpace (∀ i, RingPoint (R i) (ringBaseChange C (R i) U) (R i)) :=
  @Pi.topologicalSpace _ _ fun i => schemePointTopology (R i) (ringBaseChange C (R i) U) (R i)

/-- **Coordinate topologies.** If every factor comparison is a homeomorphism, the coordinate
topology on the points of the space of `U` is induced from the local models. -/
theorem isHomeomorph_coordinate
    (hfac : ∀ i, @IsHomeomorph _ _ (fieldValuedPointTopology C ((schemeToSpace _).obj U) (φ i))
      (schemePointTopology (R i) (ringBaseChange C (R i) U) (R i))
      (fun p => ringPointBaseChangeEquiv C (R i) (R i) U (schemeRingPointsEquiv C U (R i) p))) :
    @IsHomeomorph _ _ (coordinatePointTopology C ((schemeToSpace _).obj U) R L φ π)
      (TopologicalSpace.induced (localModelMap U R π) (localModelProductTopology U R))
      (schemeRingPointsEquiv C U A) := by
  let _ (i : ι) : TopologicalSpace (RingPoints C ((schemeToSpace _).obj U) (R i)) :=
    fieldValuedPointTopology C ((schemeToSpace _).obj U) (φ i)
  let _ (i : ι) : TopologicalSpace (RingPoint (R i) (ringBaseChange C (R i) U) (R i)) :=
    schemePointTopology (R i) (ringBaseChange C (R i) U) (R i)
  have hΨ : IsEmbedding (Pi.map fun i (p : RingPoints C ((schemeToSpace _).obj U) (R i)) =>
      ringPointBaseChangeEquiv C (R i) (R i) U (schemeRingPointsEquiv C U (R i) p)) :=
    IsEmbedding.piMap fun i => (hfac i).isEmbedding
  apply isHomeomorph_of_eq_induced
  rw [coordinatePointTopology, coordinateProductTopology, induced_compose]
  change TopologicalSpace.induced _ Pi.topologicalSpace = _
  rw [hΨ.eq_induced, induced_compose]
  rfl

omit [∀ i, TopologicalSpace (R i)] in
/-- An isomorphism of algebraic spaces is a homeomorphism for the coordinate topologies. -/
theorem isHomeomorph_coordinate_iso {X Y : AlgebraicSpace (Spec (CommRingCat.of C))}
    (e : X ≅ Y) :
    @IsHomeomorph _ _ (coordinatePointTopology C X R L φ π) (coordinatePointTopology C Y R L φ π)
      (RingPoints.mapEquiv (A := A) e) := by
  have hfac : ∀ i, @IsInducing _ _ (fieldValuedPointTopology C X (φ i))
      (fieldValuedPointTopology C Y (φ i)) (RingPoints.map (A := R i) e.hom) := by
    intro i
    have h := isHomeomorph_ringPointsMap_of_iso
      ((baseChangeFunctor (Spec.algebraMap C (L i))).mapIso e)
    refine @IsInducing.mk _ _ (fieldValuedPointTopology C X (φ i))
      (fieldValuedPointTopology C Y (φ i)) _ ?_
    rw [fieldValuedPointTopology, fieldValuedPointTopology, induced_compose]
    have hcomm : fieldValuedPointMap C Y (φ i) ∘ RingPoints.map e.hom =
        RingPoints.map (baseChangeMap (Spec.algebraMap C (L i)) e.hom) ∘
          fieldValuedPointMap C X (φ i) :=
      funext (CoordinatePointMaps.fieldValuedPointMap_map e.hom (φ i))
    rw [hcomm, ← induced_compose]
    congr 1
    let _ : TopologicalSpace
        (RingPoints (L i) ((baseChangeFunctor (Spec.algebraMap C (L i))).obj X) (L i)) :=
      etaleChartTopology _ _
    let _ : TopologicalSpace
        (RingPoints (L i) ((baseChangeFunctor (Spec.algebraMap C (L i))).obj Y) (L i)) :=
      etaleChartTopology _ _
    exact h.isInducing.eq_induced
  let _ (i : ι) : TopologicalSpace (RingPoints C X (R i)) := fieldValuedPointTopology C X (φ i)
  let _ (i : ι) : TopologicalSpace (RingPoints C Y (R i)) := fieldValuedPointTopology C Y (φ i)
  have hΨ : IsInducing (Pi.map fun i => RingPoints.map (A := R i) e.hom) :=
    IsInducing.piMap hfac
  apply isHomeomorph_of_eq_induced
  rw [coordinatePointTopology, coordinatePointTopology, induced_compose]
  change _ = TopologicalSpace.induced (coordinatePointMap C Y R π ∘ RingPoints.map e.hom) _
  rw [CoordinatePointMaps.coordinatePointMap_map R π e.hom, ← induced_compose]
  change _ = TopologicalSpace.induced _ (TopologicalSpace.induced _ Pi.topologicalSpace)
  rw [← hΨ.eq_induced]
  rfl

end Coordinates

end SchemeSpacePointComparison

end Langlands.AlgebraicGeometry.AlgebraicSpace
