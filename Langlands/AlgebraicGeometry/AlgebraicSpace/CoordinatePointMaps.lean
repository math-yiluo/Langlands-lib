import Langlands.AlgebraicGeometry.AlgebraicSpace.ClosedImmersionPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyFunctorial
import Langlands.Global.AdelicSpaceLevelFactors

/-!
# Morphisms on coordinate point topologies

A morphism `f : X → Y` of algebraic spaces over a ring `C` acts on the field-valued and
coordinate point topologies of the adelic levels. Over a henselian valued field, `f` is
continuous for the field-valued topologies when `Y` is separated of finite type. A closed
immersion is a closed embedding along an injective map to the field, when both spaces are
separated of finite type. On coordinate topologies the same holds factorwise, and for closed
embeddings the coordinate maps of both spaces must be bijective (Proposition 5.2).
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace CoordinatePointMaps

open CoordinatePointTopologyFacts

/-- Base change keeps closed immersions. -/
theorem isClosedImmersion_baseChangeMap {S T : Scheme.{u}} (g : T ⟶ S) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsClosedImmersion (hom f)) : IsClosedImmersion (hom (baseChangeMap g f)) :=
  relative_restrictPresheaf_map (g := g) (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) hf

/-- Base change keeps finite type. -/
theorem finiteTypeOverRing_baseChange {C D : Type u} [CommRing C] [CommRing D]
    (g : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of C))
    {X : AlgebraicSpace (Spec (CommRingCat.of C))} (hft : FiniteTypeOverRing C X) :
    FiniteTypeOverRing D (baseChange g X) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType.{u} ⊓ @QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  exact hft.baseChange

variable {C : Type u} [CommRing C] {X Y : AlgebraicSpace (Spec (CommRingCat.of C))}

section FieldValued

variable {A L : Type u} [CommRing A] [Algebra C A] [Field L] [Algebra C L]

/-- The field-valued point map is natural in morphisms of algebraic spaces. -/
theorem fieldValuedPointMap_map (f : X ⟶ Y) (φ : A →ₐ[C] L) (p : RingPoints C X A) :
    fieldValuedPointMap C Y φ (RingPoints.map f p) =
      RingPoints.map (baseChangeMap (Spec.algebraMap C L) f) (fieldValuedPointMap C X φ p) := by
  apply (baseChangeRingPointsEquiv C L L Y).injective
  rw [baseChangeRingPointsEquiv_map]
  simp only [fieldValuedPointMap, Equiv.apply_symm_apply, RingPoints.changeRing_map]

end FieldValued

section Normed

variable {A K : Type u} [CommRing A] [Algebra C A] [NontriviallyNormedField K] [Algebra C K]

/-- **Continuity on a field-valued factor.** -/
theorem continuous_fieldValued (hK : IsHenselianValuedField K) (hY : IsSeparated Y)
    (hftY : FiniteTypeOverRing C Y) (f : X ⟶ Y) (φ : A →ₐ[C] K) :
    @Continuous _ _ (fieldValuedPointTopology C X φ) (fieldValuedPointTopology C Y φ)
      (RingPoints.map f) := by
  let _ : TopologicalSpace (RingPoints C X A) := fieldValuedPointTopology C X φ
  let _ : TopologicalSpace (RingPoints C Y A) := fieldValuedPointTopology C Y φ
  let _ : TopologicalSpace (RingPoints K (baseChange (Spec.algebraMap C K) X) K) :=
    etaleChartTopology K _
  let _ : TopologicalSpace (RingPoints K (baseChange (Spec.algebraMap C K) Y) K) :=
    etaleChartTopology K _
  rw [(fieldValuedPointMap_isInducing C Y φ).continuous_iff]
  have hcomm : fieldValuedPointMap C Y φ ∘ RingPoints.map f =
      RingPoints.map (baseChangeMap (Spec.algebraMap C K) f) ∘ fieldValuedPointMap C X φ :=
    funext (fieldValuedPointMap_map f φ)
  rw [hcomm]
  exact (continuous_ringPointsMap hK
    (Global.AdelicSpaceLevelFactors.isQuasiSeparatedLocallyFiniteType hY hftY) _).comp
    (fieldValuedPointMap_isInducing C X φ).continuous

/-- **Closed immersions on a field-valued factor**, along an injective map to the field. -/
theorem isClosedEmbedding_fieldValued (hK : IsHenselianValuedField K) (hX : IsSeparated X)
    (hftX : FiniteTypeOverRing C X) (hY : IsSeparated Y) (hftY : FiniteTypeOverRing C Y)
    (f : X ⟶ Y) (hf : IsClosedImmersion (hom f)) (φ : A →ₐ[C] K) (hφ : Function.Injective φ) :
    @IsClosedEmbedding _ _ (fieldValuedPointTopology C X φ) (fieldValuedPointTopology C Y φ)
      (RingPoints.map f) := by
  let _ : TopologicalSpace (RingPoints C X A) := fieldValuedPointTopology C X φ
  let _ : TopologicalSpace (RingPoints C Y A) := fieldValuedPointTopology C Y φ
  let _ : TopologicalSpace (RingPoints K (baseChange (Spec.algebraMap C K) X) K) :=
    etaleChartTopology K _
  let _ : TopologicalSpace (RingPoints K (baseChange (Spec.algebraMap C K) Y) K) :=
    etaleChartTopology K _
  have hc : IsClosedEmbedding
      (RingPoints.map (A := K) (baseChangeMap (Spec.algebraMap C K) f)) :=
    isClosedEmbedding_ringPointsMap hK
      (Global.AdelicSpaceLevelFactors.isQuasiSeparatedLocallyFiniteType hX hftX)
      (Global.AdelicSpaceLevelFactors.isQuasiSeparatedLocallyFiniteType hY hftY) _
      (isClosedImmersion_baseChangeMap _ f hf)
  have hcomm : fieldValuedPointMap C Y φ ∘ RingPoints.map f =
      RingPoints.map (baseChangeMap (Spec.algebraMap C K) f) ∘ fieldValuedPointMap C X φ :=
    funext (fieldValuedPointMap_map f φ)
  have hiX := fieldValuedPointMap_isInducing C X φ
  have hiY := fieldValuedPointMap_isInducing C Y φ
  have hrange : Set.range (RingPoints.map f : RingPoints C X A → RingPoints C Y A) =
      fieldValuedPointMap C Y φ ⁻¹'
        Set.range (RingPoints.map (A := K) (baseChangeMap (Spec.algebraMap C K) f)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨fieldValuedPointMap C X φ x, (fieldValuedPointMap_map f φ x).symm⟩
    · rintro ⟨q, hq⟩
      have h : RingPoints.map f (baseChangeRingPointsEquiv C K K X q) =
          RingPoints.changeRing φ y := by
        rw [← baseChangeRingPointsEquiv_map, hq]
        simp only [fieldValuedPointMap, Equiv.apply_symm_apply]
      obtain ⟨x', -, hx'⟩ := ClosedImmersionPoints.exists_changeRing_eq f hf φ hφ h
      exact ⟨x', hx'⟩
  refine ⟨⟨?_, ClosedImmersionPoints.map_injective f hf⟩, ?_⟩
  · rw [← hiY.of_comp_iff, hcomm]
    exact hc.isInducing.comp hiX
  · rw [hrange]
    exact hc.isClosed_range.preimage hiY.continuous

end Normed

section Coordinates

variable {ι : Type*} (R L : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
  [∀ i, Field (L i)] [∀ i, Algebra C (L i)] [∀ i, TopologicalSpace (L i)]
  {A : Type u} [CommRing A] [Algebra C A] (φ : ∀ i, R i →ₐ[C] L i) (π : ∀ i, A →ₐ[C] R i)

/-- The coordinate map is natural in morphisms of algebraic spaces. -/
theorem coordinatePointMap_map (f : X ⟶ Y) :
    coordinatePointMap C Y R π ∘ RingPoints.map f =
      Pi.map (fun _ => RingPoints.map f) ∘ coordinatePointMap C X R π := by
  funext p i
  exact RingPoints.changeRing_map f (π i) p

/-- **Continuity on coordinate topologies**, from continuity on the factors. -/
theorem continuous_coordinate (f : X ⟶ Y)
    (hf : ∀ i, @Continuous _ _ (fieldValuedPointTopology C X (φ i))
      (fieldValuedPointTopology C Y (φ i)) (RingPoints.map f)) :
    @Continuous _ _ (coordinatePointTopology C X R L φ π) (coordinatePointTopology C Y R L φ π)
      (RingPoints.map f) := by
  let _ : TopologicalSpace (RingPoints C X A) := coordinatePointTopology C X R L φ π
  let _ : TopologicalSpace (RingPoints C Y A) := coordinatePointTopology C Y R L φ π
  let _ (i : ι) : TopologicalSpace (RingPoints C X (R i)) := fieldValuedPointTopology C X (φ i)
  let _ (i : ι) : TopologicalSpace (RingPoints C Y (R i)) := fieldValuedPointTopology C Y (φ i)
  rw [(coordinatePointMap_isInducing C Y R L φ π).continuous_iff, coordinatePointMap_map R π f]
  exact (continuous_pi fun i => (hf i).comp (continuous_apply i)).comp
    (coordinatePointMap_isInducing C X R L φ π).continuous

/-- **Closed embeddings on coordinate topologies**, from closed embeddings on the factors, when
both coordinate maps are bijective. -/
theorem isClosedEmbedding_coordinate (f : X ⟶ Y)
    (hbX : Function.Bijective (coordinatePointMap C X R π))
    (hbY : Function.Bijective (coordinatePointMap C Y R π))
    (hf : ∀ i, @IsClosedEmbedding _ _ (fieldValuedPointTopology C X (φ i))
      (fieldValuedPointTopology C Y (φ i)) (RingPoints.map f)) :
    @IsClosedEmbedding _ _ (coordinatePointTopology C X R L φ π)
      (coordinatePointTopology C Y R L φ π) (RingPoints.map f) := by
  let _ : TopologicalSpace (RingPoints C X A) := coordinatePointTopology C X R L φ π
  let _ : TopologicalSpace (RingPoints C Y A) := coordinatePointTopology C Y R L φ π
  let _ (i : ι) : TopologicalSpace (RingPoints C X (R i)) := fieldValuedPointTopology C X (φ i)
  let _ (i : ι) : TopologicalSpace (RingPoints C Y (R i)) := fieldValuedPointTopology C Y (φ i)
  rw [← (isHomeomorph_coordinatePointMap Y R L φ π hbY).isClosedEmbedding.of_comp_iff,
    coordinatePointMap_map R π f]
  exact (IsClosedEmbedding.piMap hf).comp
    (isHomeomorph_coordinatePointMap X R L φ π hbX).isClosedEmbedding

end Coordinates

end CoordinatePointMaps

end Langlands.AlgebraicGeometry.AlgebraicSpace
