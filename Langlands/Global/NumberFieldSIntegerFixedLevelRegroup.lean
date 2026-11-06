import Langlands.Global.NumberFieldSIntegerFixedLevelWeil
import Langlands.Global.NumberFieldSIntegerLevelRegroup

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain
open _root_.AlgebraicGeometry
open scoped NumberField TensorProduct NumberField.LiesOver
  Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.NumberFieldSIntegerLevelWeil
  Langlands.Global.NumberFieldSIntegerFixedLevelWeil
  Langlands.Global.FixedModelLocalProduct
  Langlands.Global.AdelicFunctoriality.IntegralTopology

namespace Langlands.Global.NumberFieldSIntegerFixedLevelRegroup

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open AdelicFunctoriality NumberFieldSIntegerLevelWeil NumberFieldSIntegerFixedLevelWeil

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K)) (T : AdelicLevelIndexAbove S)


/-- The full upper preimage of the enlarged support, above the original upper base support. -/
def upperLevel : AdelicLevelIndexAbove (numberFieldExceptionalPreimage (L := L) S) :=
  ⟨numberFieldExceptionalPreimage (L := L) T.val, fun q hq =>
    (mem_numberFieldExceptionalPreimage T.val q).mpr
      (T.property ((mem_numberFieldExceptionalPreimage S q).mp hq))⟩

/-- The existing original-place reindexing at the enlarged support. -/
abbrev indexEquiv := NumberFieldSIntegerLevelRegroup.indexEquiv K L T.val

variable (Y : Over (Spec (CommRingCat.of (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L))))

/-- Each regrouped factor has the same original ring, fixed coefficient action and point topology. -/
def factorPointHomeomorph (z : Σ i, Above K L T.val i) :
    letI := schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (upperFactor K L T.val z.1 z.2)
    letI := schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y
      (NumberFieldLevelFactor L (upperLevel K L S T).val (indexEquiv K L S T z))
    RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (upperFactor K L T.val z.1 z.2) ≃ₜ
      RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y
        (NumberFieldLevelFactor L (upperLevel K L S T).val (indexEquiv K L S T z)) := by
  letI := schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (upperFactor K L T.val z.1 z.2)
  letI := schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y
    (NumberFieldLevelFactor L (upperLevel K L S T).val (indexEquiv K L S T z))
  rcases z with ⟨i, q⟩
  cases i with
  | inl p =>
    have h : FixedModelLocalProduct.numberFieldFactorAlgebra L
        (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)
        (indexEquiv K L S T ⟨.inl p, q⟩) =
        NumberFieldSIntegerFixedLevelWeil.upperCoefficientAlgebra K L S T (.inl p) q :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [h]
    exact Homeomorph.refl _
  | inr v =>
    cases v with
    | inl p =>
      have h : FixedModelLocalProduct.numberFieldFactorAlgebra L
          (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)
          (indexEquiv K L S T ⟨.inr (.inl p), q⟩) =
          NumberFieldSIntegerFixedLevelWeil.upperCoefficientAlgebra K L S T (.inr (.inl p)) q :=
        Algebra.algebra_ext _ _ fun _ => rfl
      rw [h]
      exact Homeomorph.refl _
    | inr p =>
      have h : FixedModelLocalProduct.numberFieldFactorAlgebra L
          (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)
          (indexEquiv K L S T ⟨.inr (.inr p), q⟩) =
          NumberFieldSIntegerFixedLevelWeil.upperCoefficientAlgebra K L S T (.inr (.inr p)) q :=
        Algebra.algebra_ext _ _ fun _ => rfl
      rw [h]
      exact Homeomorph.refl _

/-- Regroup the original upper factors with their original fixed-base product topologies. -/
def productPointHomeomorph :
    letI : ∀ z : Σ i, Above K L T.val i,
        TopologicalSpace (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (upperFactor K L T.val z.1 z.2)) :=
      fun _ => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y _
    letI : ∀ i, TopologicalSpace
        (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (NumberFieldLevelFactor L (upperLevel K L S T).val i)) :=
      fun _ => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y _
    (∀ z : Σ i, Above K L T.val i, RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (upperFactor K L T.val z.1 z.2)) ≃ₜ
      (∀ i, RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (NumberFieldLevelFactor L (upperLevel K L S T).val i)) := by
  letI : ∀ z : Σ i, Above K L T.val i,
      TopologicalSpace (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (upperFactor K L T.val z.1 z.2)) :=
    fun _ => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y _
  letI : ∀ i, TopologicalSpace
      (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (NumberFieldLevelFactor L (upperLevel K L S T).val i)) :=
    fun _ => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y _
  exact (Homeomorph.piCongrRight (factorPointHomeomorph K L S T Y)).trans
    (Homeomorph.piCongrLeft (Y := fun i =>
      RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (NumberFieldLevelFactor L (upperLevel K L S T).val i))
      (indexEquiv K L S T))

@[simp]
theorem productPointHomeomorph_apply
    (x : ∀ z : Σ i, Above K L T.val i, RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (upperFactor K L T.val z.1 z.2))
    (z : Σ i, Above K L T.val i) :
    productPointHomeomorph K L S T Y x (indexEquiv K L S T z) =
      factorPointHomeomorph K L S T Y z (x z) := by
  let : ∀ z : Σ i, Above K L T.val i,
      TopologicalSpace (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (upperFactor K L T.val z.1 z.2)) :=
    fun _ => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y _
  let : ∀ i, TopologicalSpace
      (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (NumberFieldLevelFactor L (upperLevel K L S T).val i)) :=
    fun _ => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y _
  change (Homeomorph.piCongrLeft (Y := fun i =>
    RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y
      (NumberFieldLevelFactor L (upperLevel K L S T).val i)) (indexEquiv K L S T))
    ((Homeomorph.piCongrRight (factorPointHomeomorph K L S T Y)) x)
    (indexEquiv K L S T z) = _
  exact Homeomorph.piCongrLeft_apply_apply (Y := fun i =>
    RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) Y
      (NumberFieldLevelFactor L (upperLevel K L S T).val i))
    (indexEquiv K L S T) ((Homeomorph.piCongrRight (factorPointHomeomorph K L S T Y)) x) z

variable [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]

/-- Original upper enlarged-level points are homeomorphic to their original fixed-base coordinates. -/
def upperPointHomeomorph :
    letI := numberFieldFixedModelStageTopology L
      (numberFieldExceptionalPreimage (L := L) S) Y (upperLevel K L S T)
    letI : ∀ i, TopologicalSpace
        (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (NumberFieldLevelFactor L (upperLevel K L S T).val i)) :=
      fun _ => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y _
    RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (numberFieldAdeleLevelOver L
        (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)) ≃ₜ
      (∀ i, RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (NumberFieldLevelFactor L (upperLevel K L S T).val i)) := by
  let U := NumberFieldLevelFactor L (upperLevel K L S T).val
  letI := numberFieldFixedModelStageTopology L
    (numberFieldExceptionalPreimage (L := L) S) Y (upperLevel K L S T)
  letI := localProductPointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) U Y
  letI : ∀ i, TopologicalSpace (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (U i)) := fun _ => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y _
  let E := Equiv.ofBijective (productPointMap (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) U Y)
    ⟨productPointMap_injective (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) U Y, productPointMap_surjective (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) U Y⟩
  exact (FixedModelLocalProduct.numberFieldStageHomeomorph L
    (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T) Y).trans
      (E.toHomeomorphOfIsInducing
        (productPointMap_isInducing_localProductPointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) U Y))

/-- The original upper coordinate map is the literal enlarged-level projection. -/
theorem upperPointHomeomorph_coordinate
    (p : RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (numberFieldAdeleLevelOver L
      (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)))
    (i : NumberFieldLevelFactorIndex L (upperLevel K L S T).val) :
    (upperPointHomeomorph K L S T Y p i).left =
      Spec.map (CommRingCat.ofHom
        (numberFieldLevelFactorProjection L (upperLevel K L S T).val i)) ≫ p.left :=
  FixedModelLocalProduct.numberFieldStageHomeomorph_coordinate L
    (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T) Y p i

variable [LocallyOfFiniteType Y.hom] (n : ℕ)
  (j : Y.left ⟶ ProjectiveSpace (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n) [IsImmersion j]
  (hj : j ≫ projectiveSpaceToSpec (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n = Y.hom)

/-- The two original fixed integral models have homeomorphic points at every enlarged full-preimage level. -/
def adelicLevelPointHomeomorph :
    letI := numberFieldFixedModelStageTopology K S (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) T
    letI := numberFieldFixedModelStageTopology L
      (numberFieldExceptionalPreimage (L := L) S) Y (upperLevel K L S T)
    RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) (numberFieldAdeleLevelOver K S T) ≃ₜ
      RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (numberFieldAdeleLevelOver L
        (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T)) := by
  letI := numberFieldFixedModelStageTopology K S (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) T
  letI := numberFieldFixedModelStageTopology L
    (numberFieldExceptionalPreimage (L := L) S) Y (upperLevel K L S T)
  letI : ∀ z : Σ i, Above K L T.val i,
      TopologicalSpace (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (upperFactor K L T.val z.1 z.2)) :=
    fun _ => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y _
  letI : ∀ i, TopologicalSpace
      (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (NumberFieldLevelFactor L (upperLevel K L S T).val i)) :=
    fun _ => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y _
  exact (NumberFieldSIntegerFixedLevelWeil.levelPointHomeomorph K L S T Y n j hj).trans
    ((productPointHomeomorph K L S T Y).trans (upperPointHomeomorph K L S T Y).symm)

/-- All original upper coordinates are exactly the regrouped original local Weil components. -/
theorem adelicLevelPointHomeomorph_coordinates
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) (numberFieldAdeleLevelOver K S T)) :
    upperPointHomeomorph K L S T Y (adelicLevelPointHomeomorph K L S T Y n j hj p) =
      productPointHomeomorph K L S T Y
        (NumberFieldSIntegerFixedLevelWeil.levelPointHomeomorph K L S T Y n j hj p) := by
  let := numberFieldFixedModelStageTopology L
    (numberFieldExceptionalPreimage (L := L) S) Y (upperLevel K L S T)
  let : ∀ z : Σ i, Above K L T.val i,
      TopologicalSpace (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (upperFactor K L T.val z.1 z.2)) :=
    fun _ => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y _
  let : ∀ i, TopologicalSpace
      (RingPoint (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y (NumberFieldLevelFactor L (upperLevel K L S T).val i)) :=
    fun _ => schemePointTopology (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y _
  exact (upperPointHomeomorph K L S T Y).apply_symm_apply _

/-- Each literal original upper projection recovers its original regrouped local Weil point. -/
theorem adelicLevelPointHomeomorph_coordinate_left
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) (numberFieldAdeleLevelOver K S T))
    (z : Σ i, Above K L T.val i) :
    Spec.map (CommRingCat.ofHom (numberFieldLevelFactorProjection L
        (upperLevel K L S T).val (indexEquiv K L S T z))) ≫
        (adelicLevelPointHomeomorph K L S T Y n j hj p).left =
      (factorPointHomeomorph K L S T Y z
        (NumberFieldSIntegerFixedLevelWeil.levelPointHomeomorph K L S T Y n j hj p z)).left := by
  rw [← upperPointHomeomorph_coordinate]
  rw [adelicLevelPointHomeomorph_coordinates, productPointHomeomorph_apply]

end Langlands.Global.NumberFieldSIntegerFixedLevelRegroup
