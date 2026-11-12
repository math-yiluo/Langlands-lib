import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionFiniteProductBasePoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointTopologyFacts

/-! # Tensor Weil comparison with the original factor topologies -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

namespace WeilRestrictionTensorTopology

section FieldBaseChange

variable (B : Type u) [CommRing B] (K : Type u) [Field K] [TopologicalSpace K]
  [Algebra B K] (X : AlgebraicSpace (Spec (CommRingCat.of B)))

/-- The identity field map identifies the original field-valued topology
with the rational-point topology of the base change. -/
def fieldBaseChangePointHomeomorph :
    letI : TopologicalSpace (RingPoints B X K) :=
      fieldValuedPointTopology B X (AlgHom.id B K)
    letI : TopologicalSpace
        (RingPoints K (baseChange (Spec.algebraMap B K) X) K) :=
      etaleChartTopology K (baseChange (Spec.algebraMap B K) X)
    RingPoints B X K ≃ₜ RingPoints K (baseChange (Spec.algebraMap B K) X) K := by
  let : TopologicalSpace (RingPoints B X K) :=
    fieldValuedPointTopology B X (AlgHom.id B K)
  let : TopologicalSpace
      (RingPoints K (baseChange (Spec.algebraMap B K) X) K) :=
    etaleChartTopology K (baseChange (Spec.algebraMap B K) X)
  refine (baseChangeRingPointsEquiv B K K X).symm.toHomeomorphOfIsInducing ?_
  convert fieldValuedPointMap_isInducing B X (AlgHom.id B K) using 1
  funext x
  simp [fieldValuedPointMap, RingPoints.changeRing, pullback_id]

local instance : TopologicalSpace (RingPoints B X K) :=
  fieldValuedPointTopology B X (AlgHom.id B K)

local instance : TopologicalSpace
    (RingPoints K (baseChange (Spec.algebraMap B K) X) K) :=
  etaleChartTopology K (baseChange (Spec.algebraMap B K) X)

@[simp]
theorem fieldBaseChangePointHomeomorph_apply (x : RingPoints B X K) :
    fieldBaseChangePointHomeomorph B K X x =
      (baseChangeRingPointsEquiv B K K X).symm x := rfl

@[simp]
theorem fieldBaseChangePointHomeomorph_symm_apply
    (x : RingPoints K (baseChange (Spec.algebraMap B K) X) K) :
    (fieldBaseChangePointHomeomorph B K X).symm x =
      baseChangeRingPointsEquiv B K K X x := rfl

end FieldBaseChange

section Factors

variable (B : Type u) [CommRing B]
  {ι : Type u} (D : ι → Type u)
  [∀ i, CommRing (D i)] [∀ i, Algebra B (D i)]
  (X : AlgebraicSpace (Spec (CommRingCat.of B)))

/-- The original factor of a base change to a product is the base change
to that factor. -/
def factorBaseChangeIso (i : ι) :
    WeilRestrictionFiniteProduct.factorSpace D
        (baseChange (Spec.algebraMap B (∀ j, D j)) X) i ≅
      baseChange (Spec.algebraMap B (D i)) X :=
  BaseChangeComparison.compIso _ _ _ (finiteProductSpecProjection_comp D B i) X

/-- The factor base-change comparison retains the original coefficient
projection on points. -/
theorem factorBaseChangeIso_points
    (z : RingPoints (∀ j, D j)
      (baseChange (Spec.algebraMap B (∀ j, D j)) X) (∀ j, D j)) (i : ι) :
    baseChangeRingPointsEquiv B (D i) (D i) X
        (RingPoints.map (factorBaseChangeIso B D X i).hom
          ((baseChange (Spec.algebraMap B (∀ j, D j)) X).pullback
            (WeilRestrictionFiniteProduct.factorBaseTestMap D i) z)) =
      RingPoints.changeRing (Pi.evalAlgHom B D i)
        (baseChangeRingPointsEquiv B (∀ j, D j) (∀ j, D j) X z) := by
  simp only [baseChangeRingPointsEquiv_apply]
  change X.pullback _
      (X.pullback _ (X.pullback _ z)) =
    X.pullback _ (X.pullback _ z)
  rw [← pullback_comp, ← pullback_comp, ← pullback_comp]
  apply BaseChangeComparison.pullback_congr_left
  simp [BaseChangeComparison.overIso,
    WeilRestrictionFiniteProduct.factorBaseTestMap, ringTestMap_left]
  rfl

end Factors

section FactorTopology

variable (B : Type u) [CommRing B]
  {ι : Type u} (D : ι → Type u)
  [∀ i, Field (D i)] [∀ i, TopologicalSpace (D i)] [∀ i, Algebra B (D i)]
  (X : AlgebraicSpace (Spec (CommRingCat.of B)))

/-- The factor base-change comparison followed by the original
field-valued point identification. -/
def factorPointHomeomorph (i : ι) :
    letI : TopologicalSpace
        (RingPoints (D i) (WeilRestrictionFiniteProduct.factorSpace D
          (baseChange (Spec.algebraMap B (∀ j, D j)) X) i) (D i)) :=
      etaleChartTopology (D i) (WeilRestrictionFiniteProduct.factorSpace D
        (baseChange (Spec.algebraMap B (∀ j, D j)) X) i)
    letI : TopologicalSpace (RingPoints B X (D i)) :=
      fieldValuedPointTopology B X (AlgHom.id B (D i))
    RingPoints (D i) (WeilRestrictionFiniteProduct.factorSpace D
        (baseChange (Spec.algebraMap B (∀ j, D j)) X) i) (D i) ≃ₜ
      RingPoints B X (D i) := by
  let : TopologicalSpace
      (RingPoints (D i) (WeilRestrictionFiniteProduct.factorSpace D
        (baseChange (Spec.algebraMap B (∀ j, D j)) X) i) (D i)) :=
    etaleChartTopology (D i) (WeilRestrictionFiniteProduct.factorSpace D
      (baseChange (Spec.algebraMap B (∀ j, D j)) X) i)
  let : TopologicalSpace
      (RingPoints (D i) (baseChange (Spec.algebraMap B (D i)) X) (D i)) :=
    etaleChartTopology (D i) (baseChange (Spec.algebraMap B (D i)) X)
  let : TopologicalSpace (RingPoints B X (D i)) :=
    fieldValuedPointTopology B X (AlgHom.id B (D i))
  exact (IsHomeomorph.homeomorph _
    (isHomeomorph_ringPointsMap_of_iso (factorBaseChangeIso B D X i))).trans
      (fieldBaseChangePointHomeomorph B (D i) X).symm

@[simp]
theorem factorPointHomeomorph_apply (i : ι)
    (x : RingPoints (D i) (WeilRestrictionFiniteProduct.factorSpace D
      (baseChange (Spec.algebraMap B (∀ j, D j)) X) i) (D i)) :
    factorPointHomeomorph B D X i x =
      baseChangeRingPointsEquiv B (D i) (D i) X
        (RingPoints.map (factorBaseChangeIso B D X i).hom x) := rfl

end FactorTopology

section TensorTopology

open WeilRestrictionFiniteProduct

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  (C : Type u) [NontriviallyNormedField C] [Algebra R C]
  {ι : Type u} [Finite ι] (D : ι → Type u)
  [∀ i, NontriviallyNormedField (D i)] [∀ i, Algebra C (D i)] [∀ i, ContinuousSMul C (D i)]
  [∀ i, FiniteDimensional C (D i)] [∀ i, IsModuleTopology C (D i)]
  [∀ i, Algebra B (D i)]
  (e : C ⊗[R] B ≃ₐ[C] (∀ i, D i))
  (he : ∀ (b : B) (i : ι), e (1 ⊗ₜ[R] b) i = algebraMap B (D i) b)
  (X : AlgebraicSpace (Spec (CommRingCat.of B)))
  (h : IsAlgebraicSpace _ ((ringWeilRestriction R B).obj X.toSheaf))
  (hf : ∀ i, IsAlgebraicSpace _
    ((ringWeilRestriction C (D i)).obj
      (factorSpace D (baseChange (Spec.algebraMap B (∀ j, D j)) X) i).toSheaf))

/-- The tensor local homeomorphism, with the original coefficient
topologies and explicit geometric hypotheses. -/
def tensorPointHomeomorph
    (hC : IsHenselianValuedField C) (hD : ∀ i, IsHenselianValuedField (D i))
    (hX : ∀ i, IsQuasiSeparatedLocallyFiniteType (D i)
      (factorSpace D (baseChange (Spec.algebraMap B (∀ j, D j)) X) i))
    (hW : IsQuasiSeparatedLocallyFiniteType C
      (ringWeilRestrictionSpace C (∀ j, D j)
        (baseChange (Spec.algebraMap B (∀ j, D j)) X)
        (isAlgebraicSpace_ringWeilRestriction_tensor R B C (∀ j, D j) e
          (fun b => funext (he b)) X h)))
    (hWf : ∀ i, IsQuasiSeparatedLocallyFiniteType C
      (factorWeilSpace C D (baseChange (Spec.algebraMap B (∀ j, D j)) X) hf i)) :
    letI : TopologicalSpace
        (RingPoints R (ringWeilRestrictionSpace R B X h) C) :=
      fieldValuedPointTopology R (ringWeilRestrictionSpace R B X h) (AlgHom.id R C)
    letI : ∀ i, TopologicalSpace (RingPoints B X (D i)) :=
      fun i => fieldValuedPointTopology B X (AlgHom.id B (D i))
    RingPoints R (ringWeilRestrictionSpace R B X h) C ≃ₜ
      (∀ i, RingPoints B X (D i)) := by
  let Y := baseChange (Spec.algebraMap B (∀ j, D j)) X
  let hY := isAlgebraicSpace_ringWeilRestriction_tensor R B C (∀ j, D j) e
    (fun b => funext (he b)) X h
  let : TopologicalSpace
      (RingPoints R (ringWeilRestrictionSpace R B X h) C) :=
    fieldValuedPointTopology R (ringWeilRestrictionSpace R B X h) (AlgHom.id R C)
  let : TopologicalSpace (RingPoints C
      (baseChange (Spec.algebraMap R C) (ringWeilRestrictionSpace R B X h)) C) :=
    etaleChartTopology C
      (baseChange (Spec.algebraMap R C) (ringWeilRestrictionSpace R B X h))
  let : TopologicalSpace (RingPoints C (ringWeilRestrictionSpace C (∀ j, D j) Y hY) C) :=
    etaleChartTopology C (ringWeilRestrictionSpace C (∀ j, D j) Y hY)
  let (i : ι) : TopologicalSpace (RingPoints (D i) (factorSpace D Y i) (D i)) :=
    etaleChartTopology (D i) (factorSpace D Y i)
  let (i : ι) : TopologicalSpace (RingPoints B X (D i)) :=
    fieldValuedPointTopology B X (AlgHom.id B (D i))
  exact (((fieldBaseChangePointHomeomorph R C (ringWeilRestrictionSpace R B X h)).trans
    (IsHomeomorph.homeomorph _
      (isHomeomorph_ringPointsMap_of_iso
        (ringWeilRestrictionTensorBaseChangeIso R B C (∀ j, D j) e
          (fun b => funext (he b)) X h)))).trans
    (finiteProductWeilRestrictionPointHomeomorph C D Y hY hf hC hD hX hW hWf)).trans
    (Homeomorph.piCongrRight fun i => factorPointHomeomorph B D X i)

variable
  (hC : IsHenselianValuedField C) (hD : ∀ i, IsHenselianValuedField (D i))
  (hX : ∀ i, IsQuasiSeparatedLocallyFiniteType (D i)
    (factorSpace D (baseChange (Spec.algebraMap B (∀ j, D j)) X) i))
  (hW : IsQuasiSeparatedLocallyFiniteType C
    (ringWeilRestrictionSpace C (∀ j, D j)
      (baseChange (Spec.algebraMap B (∀ j, D j)) X)
      (isAlgebraicSpace_ringWeilRestriction_tensor R B C (∀ j, D j) e
        (fun b => funext (he b)) X h)))
  (hWf : ∀ i, IsQuasiSeparatedLocallyFiniteType C
    (factorWeilSpace C D (baseChange (Spec.algebraMap B (∀ j, D j)) X) hf i))

/-- Every component of the local homeomorphism is exactly the original
completed tensor factor map. -/
@[simp]
theorem tensorPointHomeomorph_apply
    (x : RingPoints R (ringWeilRestrictionSpace R B X h) C) (i : ι) :
    tensorPointHomeomorph R B C D e he X h hf hC hD hX hW hWf x i =
      completedTensorSpaceWeilRestrictionPointMap R B C D e he X h x i := by
  change factorPointHomeomorph B D X i
    (finiteProductWeilRestrictionPointHomeomorph C D
      (baseChange (Spec.algebraMap B (∀ j, D j)) X)
      (isAlgebraicSpace_ringWeilRestriction_tensor R B C (∀ j, D j) e
        (fun b => funext (he b)) X h) hf hC hD hX hW hWf
      (RingPoints.map (ringWeilRestrictionTensorBaseChangeIso R B C (∀ j, D j) e
        (fun b => funext (he b)) X h).hom
        ((baseChangeRingPointsEquiv R C C (ringWeilRestrictionSpace R B X h)).symm x)) i) = _
  rw [factorPointHomeomorph_apply, finiteProductWeilRestrictionPointHomeomorph_apply,
    basePointsEquiv_factor, factorBaseChangeIso_points,
    completedTensorSpaceWeilRestrictionPointMap_eq,
    ringWeilRestrictionTensorBaseChangeIso_points, Equiv.apply_symm_apply]

include hf hC hD hX hW hWf in
/-- The original completed tensor factor map is a homeomorphism for the
original lower field topology and the product of the original upper
field topologies. -/
theorem isHomeomorph_completedTensorSpaceWeilRestrictionPointMap :
    @IsHomeomorph _ _
      (fieldValuedPointTopology R (ringWeilRestrictionSpace R B X h) (AlgHom.id R C))
      (coordinateProductTopology B X D D (fun i => AlgHom.id B (D i)))
      (completedTensorSpaceWeilRestrictionPointMap R B C D e he X h) := by
  let : TopologicalSpace
      (RingPoints R (ringWeilRestrictionSpace R B X h) C) :=
    fieldValuedPointTopology R (ringWeilRestrictionSpace R B X h) (AlgHom.id R C)
  let (i : ι) : TopologicalSpace (RingPoints B X (D i)) :=
    fieldValuedPointTopology B X (AlgHom.id B (D i))
  have heq : (tensorPointHomeomorph R B C D e he X h hf hC hD hX hW hWf :
      RingPoints R (ringWeilRestrictionSpace R B X h) C → ∀ i, RingPoints B X (D i)) =
      completedTensorSpaceWeilRestrictionPointMap R B C D e he X h := by
    funext x i
    exact tensorPointHomeomorph_apply R B C D e he X h hf hC hD hX hW hWf x i
  rw [← heq]
  exact (tensorPointHomeomorph R B C D e he X h hf hC hD hX hW hWf).isHomeomorph

end TensorTopology

end WeilRestrictionTensorTopology

end Langlands.AlgebraicGeometry.AlgebraicSpace
