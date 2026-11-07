import Langlands.Global.AdelicSpaceLevelTopology
import Langlands.Global.AdelicSpaceLevelPointsProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeComparison

/-!
# Properties of the coordinate point topology

The topology `coordinatePointTopology` on `X(A)` is induced from the product of the factor
topologies `fieldValuedPointTopology`. This module records:

* it is the infimum of the topologies induced by the composite maps `X(A) → X_{L_i}(L_i)`;
* when the coordinate map `X(A) → ∏ X(R_i)` is bijective it is a homeomorphism, and the
  topology is Hausdorff or locally compact as soon as the factors are (in the locally compact
  case, all but finitely many factors compact);
* the factor topology is homeomorphic to the étale-chart topology along a bijective field
  map, and change of base ring along `C → C'` is compatible with field-valued point maps up
  to the homeomorphism of iterated base change.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace CoordinatePointTopologyFacts

/-- Two infima of topologies agree when every member of each family occurs in the other. -/
theorem iInf_eq_iInf {α : Type*} {ι ι' : Sort*} (τ : ι → TopologicalSpace α)
    (τ' : ι' → TopologicalSpace α) (h₁ : ∀ j, ∃ i, τ i = τ' j) (h₂ : ∀ i, ∃ j, τ' j = τ i) :
    ⨅ i, τ i = ⨅ j, τ' j := by
  refine le_antisymm (le_iInf fun j => ?_) (le_iInf fun i => ?_)
  · obtain ⟨i, hi⟩ := h₁ j
    exact iInf_le_of_le i hi.le
  · obtain ⟨j, hj⟩ := h₂ i
    exact iInf_le_of_le j hj.le

/-- Composing with a homeomorphism does not change an induced topology. -/
theorem induced_comp_isHomeomorph {α β γ : Type*} [tβ : TopologicalSpace β]
    [tγ : TopologicalSpace γ] (f : α → β) {h : β → γ} (hh : IsHomeomorph h) :
    TopologicalSpace.induced (h ∘ f) tγ = TopologicalSpace.induced f tβ := by
  rw [← induced_compose, hh.isInducing.eq_induced]

variable {C : Type u} [CommRing C] (X : AlgebraicSpace (Spec (CommRingCat.of C)))

section Field

variable {A L : Type u} [CommRing A] [Algebra C A] [Field L] [Algebra C L]

/-- The field-valued point map along a composite. -/
theorem fieldValuedPointMap_comp {B : Type u} [CommRing B] [Algebra C B] (φ : B →ₐ[C] L)
    (π : A →ₐ[C] B) (p : RingPoints C X A) :
    fieldValuedPointMap C X (φ.comp π) p = fieldValuedPointMap C X φ (RingPoints.changeRing π p) := by
  simp only [fieldValuedPointMap, ProductPointsDescent.changeRing_changeRing]

/-- Along a bijective algebra map the field-valued point map is bijective. -/
theorem fieldValuedPointMap_bijective (φ : A →ₐ[C] L) (hφ : Function.Bijective φ) :
    Function.Bijective (fieldValuedPointMap C X φ) :=
  (baseChangeRingPointsEquiv C L L X).symm.bijective.comp
    (Global.AdelicSpaceLevelPointsProof.changeRing_bijective (AlgEquiv.ofBijective φ hφ))

variable [TopologicalSpace L]

/-- Along a bijective algebra map the factor topology is the étale-chart topology. -/
theorem isHomeomorph_fieldValuedPointMap (φ : A →ₐ[C] L) (hφ : Function.Bijective φ) :
    @IsHomeomorph _ _ (fieldValuedPointTopology C X φ)
      (etaleChartTopology L (baseChange (Spec.algebraMap C L) X)) (fieldValuedPointMap C X φ) := by
  let : TopologicalSpace (RingPoints C X A) := fieldValuedPointTopology C X φ
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap C L) X) L) :=
    etaleChartTopology L (baseChange (Spec.algebraMap C L) X)
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨⟨fieldValuedPointMap_isInducing C X φ, (fieldValuedPointMap_bijective X φ hφ).1⟩,
      (fieldValuedPointMap_bijective X φ hφ).2⟩

/-- An injective field-valued point map into a Hausdorff space gives a Hausdorff factor. -/
theorem t2Space_fieldValuedPointTopology (φ : A →ₐ[C] L)
    (hinj : Function.Injective (fieldValuedPointMap C X φ))
    (ht2 : @T2Space _ (etaleChartTopology L (baseChange (Spec.algebraMap C L) X))) :
    @T2Space _ (fieldValuedPointTopology C X φ) := by
  let : TopologicalSpace (RingPoints C X A) := fieldValuedPointTopology C X φ
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap C L) X) L) :=
    etaleChartTopology L (baseChange (Spec.algebraMap C L) X)
  exact (IsEmbedding.mk (fieldValuedPointMap_isInducing C X φ) hinj).t2Space

/-- A field-valued point map with quasi-compact image gives a compact factor. -/
theorem compactSpace_fieldValuedPointTopology (φ : A →ₐ[C] L)
    (hc : @IsCompact _ (etaleChartTopology L (baseChange (Spec.algebraMap C L) X))
      (Set.range (fieldValuedPointMap C X φ))) :
    @CompactSpace _ (fieldValuedPointTopology C X φ) := by
  let : TopologicalSpace (RingPoints C X A) := fieldValuedPointTopology C X φ
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap C L) X) L) :=
    etaleChartTopology L (baseChange (Spec.algebraMap C L) X)
  refine ⟨(fieldValuedPointMap_isInducing C X φ).isCompact_iff.mpr ?_⟩
  rw [Set.image_univ]
  exact hc

end Field

section Coordinates

variable {ι : Type*} (R L : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
  [∀ i, Field (L i)] [∀ i, Algebra C (L i)] [∀ i, TopologicalSpace (L i)]
  {A : Type u} [CommRing A] [Algebra C A] (φ : ∀ i, R i →ₐ[C] L i) (π : ∀ i, A →ₐ[C] R i)

/-- The coordinate topology is the infimum of the topologies induced by the composite
field-valued point maps. -/
theorem coordinatePointTopology_eq_iInf :
    coordinatePointTopology C X R L φ π =
      ⨅ i, TopologicalSpace.induced (fieldValuedPointMap C X ((φ i).comp (π i)))
        (etaleChartTopology (L i) (baseChange (Spec.algebraMap C (L i)) X)) := by
  rw [coordinatePointTopology, coordinateProductTopology]
  change TopologicalSpace.induced _ (⨅ i, TopologicalSpace.induced _ _) = _
  rw [induced_iInf]
  congr 1
  funext i
  rw [fieldValuedPointTopology, induced_compose, induced_compose]
  congr 1
  funext p
  exact (fieldValuedPointMap_comp X (φ i) (π i) p).symm

/-- With a bijective coordinate map, the coordinate map is a homeomorphism onto the
product. -/
theorem isHomeomorph_coordinatePointMap (hbij : Function.Bijective (coordinatePointMap C X R π)) :
    @IsHomeomorph _ _ (coordinatePointTopology C X R L φ π) (coordinateProductTopology C X R L φ)
      (coordinatePointMap C X R π) := by
  let : TopologicalSpace (RingPoints C X A) := coordinatePointTopology C X R L φ π
  let : TopologicalSpace (∀ i, RingPoints C X (R i)) := coordinateProductTopology C X R L φ
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨⟨coordinatePointMap_isInducing C X R L φ π, hbij.1⟩, hbij.2⟩

/-- **Hausdorff.** -/
theorem t2Space_coordinatePointTopology (hinj : Function.Injective (coordinatePointMap C X R π))
    (ht2 : ∀ i, @T2Space _ (fieldValuedPointTopology C X (φ i))) :
    @T2Space _ (coordinatePointTopology C X R L φ π) := by
  let : TopologicalSpace (RingPoints C X A) := coordinatePointTopology C X R L φ π
  let (i : ι) : TopologicalSpace (RingPoints C X (R i)) := fieldValuedPointTopology C X (φ i)
  exact (IsEmbedding.mk (coordinatePointMap_isInducing C X R L φ π) hinj).t2Space

/-- **Local compactness**, when all but finitely many factors are compact. -/
theorem locallyCompactSpace_coordinatePointTopology
    (hbij : Function.Bijective (coordinatePointMap C X R π)) (s : Set ι) (hs : s.Finite)
    (hlc : ∀ i, @LocallyCompactSpace _ (fieldValuedPointTopology C X (φ i)))
    (hc : ∀ i, i ∉ s → @CompactSpace _ (fieldValuedPointTopology C X (φ i))) :
    @LocallyCompactSpace _ (coordinatePointTopology C X R L φ π) := by
  classical
  let : TopologicalSpace (RingPoints C X A) := coordinatePointTopology C X R L φ π
  let (i : ι) : TopologicalSpace (RingPoints C X (R i)) := fieldValuedPointTopology C X (φ i)
  have : Finite {i // i ∈ s} := hs.to_subtype
  have : ∀ i, LocallyCompactSpace (RingPoints C X (R i)) := hlc
  have : ∀ i : {i // ¬ i ∈ s}, CompactSpace (RingPoints C X (R i)) := fun i => hc i.1 i.2
  have : LocallyCompactSpace (∀ i, RingPoints C X (R i)) :=
    (Homeomorph.piEquivPiSubtypeProd (· ∈ s) (fun i => RingPoints C X (R i))).isOpenEmbedding
      |>.locallyCompactSpace
  exact (isHomeomorph_coordinatePointMap X R L φ π hbij).isOpenEmbedding.locallyCompactSpace

end Coordinates

section BaseRing

variable {C' : Type u} [CommRing C'] [Algebra C C']
variable {B L : Type u} [CommRing B] [Algebra C' B] [Algebra C B] [IsScalarTower C C' B]
  [Field L] [Algebra C' L] [Algebra C L] [IsScalarTower C C' L]

/-- Field-valued point maps of the base change along `C → C'` are the field-valued point
maps of `X`, up to the iterated base change comparison. -/
theorem towerIso_fieldValuedPointMap (ψ : B →ₐ[C'] L)
    (y : RingPoints C' (baseChange (Spec.algebraMap C C') X) B) :
    RingPoints.map (towerIso C C' L X).hom
        (fieldValuedPointMap C' (baseChange (Spec.algebraMap C C') X) ψ y) =
      fieldValuedPointMap C X (ψ.restrictScalars C) (baseChangeRingPointsEquiv C C' B X y) := by
  apply (baseChangeRingPointsEquiv C L L X).injective
  rw [fieldValuedPointMap, fieldValuedPointMap, Equiv.apply_symm_apply,
    baseChangeRingPointsEquiv_towerIso, Equiv.apply_symm_apply,
    baseChangeRingPointsEquiv_changeRing]

variable [TopologicalSpace L]

/-- The factor topology of the base change is induced from the factor topology of `X`. -/
theorem fieldValuedPointTopology_baseChange (ψ : B →ₐ[C'] L) :
    fieldValuedPointTopology C' (baseChange (Spec.algebraMap C C') X) ψ =
      TopologicalSpace.induced (baseChangeRingPointsEquiv C C' B X)
        (fieldValuedPointTopology C X (ψ.restrictScalars C)) := by
  rw [fieldValuedPointTopology, fieldValuedPointTopology, induced_compose]
  have key : fieldValuedPointMap C X (ψ.restrictScalars C) ∘ baseChangeRingPointsEquiv C C' B X =
      RingPoints.map (towerIso C C' L X).hom ∘
        fieldValuedPointMap C' (baseChange (Spec.algebraMap C C') X) ψ := by
    funext y
    exact (towerIso_fieldValuedPointMap X ψ y).symm
  rw [key]
  exact (@induced_comp_isHomeomorph _ _ _ (etaleChartTopology L _) (etaleChartTopology L _) _ _
    (isHomeomorph_ringPointsMap_of_iso (towerIso C C' L X))).symm

end BaseRing


section Transition

variable {C' : Type u} [CommRing C'] [Algebra C C']
variable {ι : Type*} (R L : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
  [∀ i, Field (L i)] [∀ i, Algebra C (L i)] [∀ i, TopologicalSpace (L i)]
  {A : Type u} [CommRing A] [Algebra C A] (φ : ∀ i, R i →ₐ[C] L i) (π : ∀ i, A →ₐ[C] R i)
variable {ι' : Type*} (R' L' : ι' → Type u) [∀ j, CommRing (R' j)] [∀ j, Algebra C' (R' j)]
  [∀ j, Field (L' j)] [∀ j, Algebra C' (L' j)] [∀ j, Algebra C (L' j)]
  [∀ j, IsScalarTower C C' (L' j)] [∀ j, TopologicalSpace (L' j)]
  {A' : Type u} [CommRing A'] [Algebra C' A'] [Algebra C A'] [IsScalarTower C C' A']
  (φ' : ∀ j, R' j →ₐ[C'] L' j) (π' : ∀ j, A' →ₐ[C'] R' j) (t : A →ₐ[C] A')

/-- The composite maps `A' → L' j`, as maps of `C`-algebras. -/
abbrev restrictedFieldMap (j : ι') : A' →ₐ[C] L' j := ((φ' j).comp (π' j)).restrictScalars C

/-- The topology on the `C`-points `X(A')` matching the coordinate topology of the base
change of `X` to `C'`. -/
@[instance_reducible]
def restrictedTopology : TopologicalSpace (RingPoints C X A') :=
  ⨅ j, TopologicalSpace.induced (fieldValuedPointMap C X (restrictedFieldMap R' L' φ' π' j))
    (etaleChartTopology (L' j) (baseChange (Spec.algebraMap C (L' j)) X))

/-- The coordinate topology of the base change is the restricted topology, along the point
identification of the base change. -/
theorem coordinatePointTopology_baseChange :
    coordinatePointTopology C' (baseChange (Spec.algebraMap C C') X) R' L' φ' π' =
      TopologicalSpace.induced (baseChangeRingPointsEquiv C C' A' X)
        (restrictedTopology X R' L' φ' π') := by
  rw [coordinatePointTopology_eq_iInf, restrictedTopology, induced_iInf]
  congr 1
  funext j
  exact fieldValuedPointTopology_baseChange X ((φ' j).comp (π' j))


/-- Each composite field map is continuous for the restricted topology. -/
theorem continuous_restrictedFieldMap (j : ι') :
    @Continuous _ _ (restrictedTopology X R' L' φ' π')
      (etaleChartTopology (L' j) (baseChange (Spec.algebraMap C (L' j)) X))
      (fieldValuedPointMap C X (restrictedFieldMap R' L' φ' π' j)) := by
  let : TopologicalSpace (RingPoints (L' j) (baseChange (Spec.algebraMap C (L' j)) X) (L' j)) :=
    etaleChartTopology (L' j) (baseChange (Spec.algebraMap C (L' j)) X)
  exact continuous_iInf_dom (i := j) continuous_induced_dom

/-- **Change of level is an open embedding**, given that every composite field map of one
level occurs in the other, that the source is T0, and that the image of `X(A) → X(A')` is
open for the restricted topology. -/
theorem isOpenEmbedding_levelChange
    (h₀ : @T0Space _ (coordinatePointTopology C X R L φ π))
    (h₁ : ∀ j, ∃ i,
      TopologicalSpace.induced (fieldValuedPointMap C X ((φ i).comp (π i)))
          (etaleChartTopology (L i) (baseChange (Spec.algebraMap C (L i)) X)) =
        TopologicalSpace.induced (fieldValuedPointMap C X ((restrictedFieldMap R' L' φ' π' j).comp t))
          (etaleChartTopology (L' j) (baseChange (Spec.algebraMap C (L' j)) X)))
    (h₂ : ∀ i, ∃ j,
      TopologicalSpace.induced (fieldValuedPointMap C X ((restrictedFieldMap R' L' φ' π' j).comp t))
          (etaleChartTopology (L' j) (baseChange (Spec.algebraMap C (L' j)) X)) =
        TopologicalSpace.induced (fieldValuedPointMap C X ((φ i).comp (π i)))
          (etaleChartTopology (L i) (baseChange (Spec.algebraMap C (L i)) X)))
    (hW : IsOpen[restrictedTopology X R' L' φ' π'] (Set.range (RingPoints.changeRing (X := X) t))) :
    @IsOpenEmbedding _ _ (coordinatePointTopology C X R L φ π)
      (coordinatePointTopology C' (baseChange (Spec.algebraMap C C') X) R' L' φ' π')
      (fun x => (baseChangeRingPointsEquiv C C' A' X).symm (RingPoints.changeRing t x)) := by
  let e := baseChangeRingPointsEquiv C C' A' X
  let τ' := restrictedTopology X R' L' φ' π'
  have htgt := coordinatePointTopology_baseChange X R' L' φ' π'
  have hsrc : coordinatePointTopology C X R L φ π =
      TopologicalSpace.induced (RingPoints.changeRing t) τ' := by
    rw [coordinatePointTopology_eq_iInf]
    change _ = TopologicalSpace.induced _ (⨅ j, _)
    rw [induced_iInf]
    refine iInf_eq_iInf _ _ (fun j => ?_) (fun i => ?_)
    · obtain ⟨i, hi⟩ := h₁ j
      refine ⟨i, ?_⟩
      rw [hi, induced_compose]
      congr 1
      funext p
      exact fieldValuedPointMap_comp X _ t p
    · obtain ⟨j, hj⟩ := h₂ i
      refine ⟨j, ?_⟩
      rw [induced_compose, ← hj]
      congr 1
      funext p
      exact (fieldValuedPointMap_comp X _ t p).symm
  let : TopologicalSpace (RingPoints C X A) := coordinatePointTopology C X R L φ π
  let : TopologicalSpace (RingPoints C' (baseChange (Spec.algebraMap C C') X) A') :=
    coordinatePointTopology C' (baseChange (Spec.algebraMap C C') X) R' L' φ' π'
  have hind : IsInducing (fun x => e.symm (RingPoints.changeRing t x)) := by
    refine ⟨?_⟩
    change coordinatePointTopology C X R L φ π = TopologicalSpace.induced
      (e.symm ∘ RingPoints.changeRing t)
      (coordinatePointTopology C' (baseChange (Spec.algebraMap C C') X) R' L' φ' π')
    rw [htgt, induced_compose, hsrc]
    congr 1
    funext x
    exact (e.apply_symm_apply _).symm
  refine ⟨⟨hind, hind.injective⟩, ?_⟩
  have hrange : Set.range (fun x => e.symm (RingPoints.changeRing t x)) =
      e ⁻¹' Set.range (RingPoints.changeRing (X := X) t) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, (e.apply_symm_apply _).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      change e.symm (RingPoints.changeRing t x) = y
      rw [hx, e.symm_apply_apply]
  rw [hrange]
  change IsOpen[coordinatePointTopology C' (baseChange (Spec.algebraMap C C') X) R' L' φ' π'] _
  rw [htgt]
  exact ⟨_, hW, rfl⟩

end Transition

end CoordinatePointTopologyFacts

end Langlands.AlgebraicGeometry.AlgebraicSpace
