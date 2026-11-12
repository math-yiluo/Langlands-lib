import Langlands.Global.AdelicSpaceSmoothLocalOpenReduction
import Langlands.Global.AdelicSpaceLevelTopologyProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalFieldProperPointStatement

/-! # Proper maps on adelic coordinates and stages of algebraic spaces -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

namespace AdelicSpaceProperReduction

/-- A commuting square with homeomorphic horizontal maps transports properness. -/
theorem isProperMap_of_homeomorph
    {P Q P' Q' : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    [TopologicalSpace P'] [TopologicalSpace Q']
    (eP : P ≃ₜ P') (eQ : Q ≃ₜ Q') (f : P → Q) (g : P' → Q')
    (hg : IsProperMap g) (hcomm : ∀ p, eQ (f p) = g (eP p)) :
    IsProperMap f := by
  have hn : f = eQ.symm ∘ g ∘ eP := by
    funext p
    apply eQ.injective
    simpa only [Function.comp_apply, eQ.apply_symm_apply] using hcomm p
  rw [hn]
  exact eQ.symm.isProperMap.comp (hg.comp eP.isProperMap)

variable {C : Type u} [CommRing C]
  {X Y : AlgebraicSpace (Spec (CommRingCat.of C))}

/-- The actual field-valued point identification along a coefficient isomorphism. -/
def fieldFactorPointHomeomorph {A L : Type u} [CommRing A] [Algebra C A]
    [Field L] [Algebra C L] [TopologicalSpace L]
    (X : AlgebraicSpace (Spec (CommRingCat.of C)))
    (φ : A →ₐ[C] L) (hφ : Function.Bijective φ) :
    @Homeomorph (RingPoints C X A)
      (RingPoints L (baseChange (Spec.algebraMap C L) X) L)
      (fieldValuedPointTopology C X φ)
      (etaleChartTopology L (baseChange (Spec.algebraMap C L) X)) :=
  letI := fieldValuedPointTopology C X φ
  letI := etaleChartTopology L (baseChange (Spec.algebraMap C L) X)
  (CoordinatePointTopologyFacts.isHomeomorph_fieldValuedPointMap X φ hφ).homeomorph _

/-- Properness over a field transfers to a factor along a bijective coefficient map. -/
theorem isProperMap_fieldFactor {A L : Type u} [CommRing A] [Algebra C A]
    [Field L] [Algebra C L] [TopologicalSpace L]
    (f : X ⟶ Y) (φ : A →ₐ[C] L) (hφ : Function.Bijective φ)
    (hproper : @IsProperMap _ _
      (etaleChartTopology L (baseChange (Spec.algebraMap C L) X))
      (etaleChartTopology L (baseChange (Spec.algebraMap C L) Y))
      (RingPoints.map (baseChangeMap (Spec.algebraMap C L) f))) :
    @IsProperMap _ _ (fieldValuedPointTopology C X φ)
      (fieldValuedPointTopology C Y φ) (RingPoints.map f) := by
  let : TopologicalSpace (RingPoints C X A) := fieldValuedPointTopology C X φ
  let : TopologicalSpace (RingPoints C Y A) := fieldValuedPointTopology C Y φ
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap C L) X) L) :=
    etaleChartTopology L (baseChange (Spec.algebraMap C L) X)
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap C L) Y) L) :=
    etaleChartTopology L (baseChange (Spec.algebraMap C L) Y)
  exact isProperMap_of_homeomorph
    (fieldFactorPointHomeomorph X φ hφ) (fieldFactorPointHomeomorph Y φ hφ)
    _ _ hproper (SmoothLocalOpenReduction.fieldValuedPointMap_map f φ)

/-- Functoriality over the field gives continuity on every induced factor topology. -/
theorem continuous_factor {A L : Type u} [CommRing A] [Algebra C A]
    [NontriviallyNormedField L] [Algebra C L]
    (hL : Langlands.AlgebraicGeometry.PointTopology.IsHenselianValuedField L)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing C Y)
    (f : X ⟶ Y) (φ : A →ₐ[C] L) :
    @Continuous _ _ (fieldValuedPointTopology C X φ)
      (fieldValuedPointTopology C Y φ) (RingPoints.map f) := by
  let : TopologicalSpace (RingPoints C X A) := fieldValuedPointTopology C X φ
  let : TopologicalSpace (RingPoints C Y A) := fieldValuedPointTopology C Y φ
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap C L) X) L) :=
    etaleChartTopology L (baseChange (Spec.algebraMap C L) X)
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap C L) Y) L) :=
    etaleChartTopology L (baseChange (Spec.algebraMap C L) Y)
  apply (fieldValuedPointMap_isInducing C Y φ).continuous_iff.mpr
  have hn : fieldValuedPointMap C Y φ ∘ RingPoints.map f =
      RingPoints.map (baseChangeMap (Spec.algebraMap C L) f) ∘
        fieldValuedPointMap C X φ :=
    funext (SmoothLocalOpenReduction.fieldValuedPointMap_map f φ)
  rw [hn]
  exact (continuous_ringPointsMap hL
    (AdelicSpaceLevelFactors.isQuasiSeparatedLocallyFiniteType hY hftY) _).comp
    (fieldValuedPointMap_isInducing C X φ).continuous

/-- Compactness of the source factor and Hausdorffness of the target imply properness. -/
theorem isProperMap_compactFactor {A L : Type u} [CommRing A] [Algebra C A]
    [NontriviallyNormedField L] [Algebra C L]
    (hL : Langlands.AlgebraicGeometry.PointTopology.IsHenselianValuedField L)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing C Y)
    (f : X ⟶ Y) (φ : A →ₐ[C] L)
    (hc : @CompactSpace _ (fieldValuedPointTopology C X φ))
    (ht : @T2Space _ (fieldValuedPointTopology C Y φ)) :
    @IsProperMap _ _ (fieldValuedPointTopology C X φ)
      (fieldValuedPointTopology C Y φ) (RingPoints.map f) := by
  let : TopologicalSpace (RingPoints C X A) := fieldValuedPointTopology C X φ
  let : TopologicalSpace (RingPoints C Y A) := fieldValuedPointTopology C Y φ
  have : CompactSpace (RingPoints C X A) := hc
  have : T2Space (RingPoints C Y A) := ht
  exact (continuous_factor hL hY hftY f φ).isProperMap

/-- Proper maps on every factor give a proper map for the coordinate topologies. -/
theorem isProperMap_coordinatePointMap_of_local
    {ι : Type*} (R L : ι → Type u)
    [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
    [∀ i, Field (L i)] [∀ i, Algebra C (L i)] [∀ i, TopologicalSpace (L i)]
    {A : Type u} [CommRing A] [Algebra C A]
    (φ : ∀ i, R i →ₐ[C] L i) (π : ∀ i, A →ₐ[C] R i)
    (f : X ⟶ Y)
    (hX : Function.Bijective (coordinatePointMap C X R π))
    (hY : Function.Bijective (coordinatePointMap C Y R π))
    (hp : ∀ i, @IsProperMap _ _ (fieldValuedPointTopology C X (φ i))
      (fieldValuedPointTopology C Y (φ i)) (RingPoints.map f)) :
    @IsProperMap _ _ (coordinatePointTopology C X R L φ π)
      (coordinatePointTopology C Y R L φ π) (RingPoints.map f) := by
  let := coordinatePointTopology C X R L φ π
  let := coordinatePointTopology C Y R L φ π
  let : ∀ i, TopologicalSpace (RingPoints C X (R i)) :=
    fun i => fieldValuedPointTopology C X (φ i)
  let : ∀ i, TopologicalSpace (RingPoints C Y (R i)) :=
    fun i => fieldValuedPointTopology C Y (φ i)
  exact isProperMap_of_homeomorph
    (coordinatePointHomeomorph R L φ π X hX)
    (coordinatePointHomeomorph R L φ π Y hY)
    _ _ (IsProperMap.pi_map hp) (fun p => funext (coordinatePointMap_map R π f p))

end AdelicSpaceProperReduction

end Langlands.Global
