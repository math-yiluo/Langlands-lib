import Langlands.Global.NumberFieldSIntegerLevelWeil
import Langlands.Global.AdelicLevelModelTopologyProof

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain
open _root_.AlgebraicGeometry
open scoped NumberField TensorProduct NumberField.LiesOver
  Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.NumberFieldSIntegerLevelWeil
  Langlands.Global.AdelicFunctoriality.IntegralTopology

namespace Langlands.Global.NumberFieldSIntegerLevelRegroup

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open NumberFieldSIntegerLevelWeil AdelicFunctoriality

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K))

/-- Regroup each original upper place as its unique actual upper level coordinate. -/
def indexMap : (Σ i, Above K L S i) →
    NumberFieldLevelFactorIndex L (numberFieldExceptionalPreimage (L := L) S)
  | ⟨.inl _, q⟩ => .inl q.1
  | ⟨.inr (.inl p), q⟩ => .inr (.inl ⟨q.1, by
      rw [mem_numberFieldExceptionalPreimage, finitePlacesAbove_under p.1 q]
      exact p.2⟩)
  | ⟨.inr (.inr p), q⟩ => .inr (.inr ⟨q.1, by
      rw [mem_numberFieldExceptionalPreimage, finitePlacesAbove_under p.1 q]
      exact p.2⟩)

/-- Restriction of every original upper place recovers its lower level coordinate. -/
def indexInv : NumberFieldLevelFactorIndex L (numberFieldExceptionalPreimage (L := L) S) →
    (Σ i, Above K L S i)
  | .inl q => ⟨.inl (q.comap (algebraMap K L)), ⟨q, ⟨rfl⟩⟩⟩
  | .inr (.inl q) => ⟨.inr (.inl ⟨q.1.under (NumberField.RingOfIntegers K),
      (mem_numberFieldExceptionalPreimage S q.1).mp q.2⟩), ⟨q.1, inferInstance⟩⟩
  | .inr (.inr q) => ⟨.inr (.inr ⟨q.1.under (NumberField.RingOfIntegers K), fun h =>
      q.2 ((mem_numberFieldExceptionalPreimage S q.1).mpr h)⟩), ⟨q.1, inferInstance⟩⟩

/-- All original lower-coordinate/upper-place pairs are precisely the original upper level coordinates. -/
def indexEquiv : (Σ i, Above K L S i) ≃
    NumberFieldLevelFactorIndex L (numberFieldExceptionalPreimage (L := L) S) where
  toFun := indexMap K L S
  invFun := indexInv K L S
  left_inv z := by
    rcases z with ⟨i, q⟩
    cases i with
    | inl p =>
      rcases q with ⟨q, hq⟩
      let := hq
      have h : q.comap (algebraMap K L) = p := NumberField.InfinitePlace.LiesOver.comap_eq q p
      cases h
      rfl
    | inr z =>
      cases z with
      | inl p =>
        rcases p with ⟨p, hp⟩
        rcases q with ⟨q, hq⟩
        have h : q.under (NumberField.RingOfIntegers K) = p := finitePlacesAbove_under p ⟨q, hq⟩
        cases h
        rfl
      | inr p =>
        rcases p with ⟨p, hp⟩
        rcases q with ⟨q, hq⟩
        have h : q.under (NumberField.RingOfIntegers K) = p := finitePlacesAbove_under p ⟨q, hq⟩
        cases h
        rfl
  right_inv z := by
    cases z with
    | inl q => rfl
    | inr z => cases z <;> rfl

variable
  (Y : Over (Spec (CommRingCat.of
    ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)))))

/-- Regrouping retains exactly the same original coefficient ring, scalar map and point topology. -/
def factorPointHomeomorph (z : Σ i, Above K L S i) :
    letI : TopologicalSpace (RingPoint
        ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
        (upperFactor K L S z.1 z.2)) :=
      schemePointTopology _ Y (upperFactor K L S z.1 z.2)
    letI : TopologicalSpace (RingPoint
        ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
        (NumberFieldLevelFactor L (numberFieldExceptionalPreimage (L := L) S) (indexEquiv K L S z))) :=
      schemePointTopology _ Y _
    RingPoint
        ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
        (upperFactor K L S z.1 z.2) ≃ₜ
      RingPoint
        ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
        (NumberFieldLevelFactor L (numberFieldExceptionalPreimage (L := L) S) (indexEquiv K L S z)) := by
  letI : TopologicalSpace (RingPoint
      ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
      (upperFactor K L S z.1 z.2)) :=
    schemePointTopology _ Y _
  letI : TopologicalSpace (RingPoint
      ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
      (NumberFieldLevelFactor L (numberFieldExceptionalPreimage (L := L) S) (indexEquiv K L S z))) :=
    schemePointTopology _ Y _
  rcases z with ⟨i, q⟩
  cases i with
  | inl p =>
    have h : instAdelicLevelModelPoints10 L (numberFieldExceptionalPreimage (L := L) S)
        (indexEquiv K L S ⟨.inl p, q⟩) =
        upperCoefficientAlgebra K L S (.inl p) q :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [h]
    exact Homeomorph.refl _
  | inr z =>
    cases z with
    | inl p =>
      have h : instAdelicLevelModelPoints10 L (numberFieldExceptionalPreimage (L := L) S)
          (indexEquiv K L S ⟨.inr (.inl p), q⟩) =
          upperCoefficientAlgebra K L S (.inr (.inl p)) q :=
        Algebra.algebra_ext _ _ fun _ => rfl
      rw [h]
      exact Homeomorph.refl _
    | inr p => exact Homeomorph.refl _

/-- Regrouping all original upper point factors gives their original upper level coordinate product. -/
def productPointHomeomorph :
    letI : ∀ z : Σ i, Above K L S i, TopologicalSpace
        (RingPoint
          ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
          (upperFactor K L S z.1 z.2)) :=
      fun _ => schemePointTopology _ Y _
    letI : ∀ i : NumberFieldLevelFactorIndex L (numberFieldExceptionalPreimage (L := L) S), TopologicalSpace
        (RingPoint
          ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
          (NumberFieldLevelFactor L (numberFieldExceptionalPreimage (L := L) S) i)) :=
      fun _ => schemePointTopology _ Y _
    (∀ z : Σ i, Above K L S i,
      RingPoint
        ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
        (upperFactor K L S z.1 z.2)) ≃ₜ
      (∀ i : NumberFieldLevelFactorIndex L (numberFieldExceptionalPreimage (L := L) S),
        RingPoint
          ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
          (NumberFieldLevelFactor L (numberFieldExceptionalPreimage (L := L) S) i)) := by
  letI : ∀ z : Σ i, Above K L S i, TopologicalSpace
      (RingPoint
        ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
        (upperFactor K L S z.1 z.2)) :=
    fun z => schemePointTopology _ Y _
  letI : ∀ i : NumberFieldLevelFactorIndex L (numberFieldExceptionalPreimage (L := L) S), TopologicalSpace
      (RingPoint
        ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
        (NumberFieldLevelFactor L (numberFieldExceptionalPreimage (L := L) S) i)) :=
    fun i => schemePointTopology _ Y _
  exact (Homeomorph.piCongrRight (factorPointHomeomorph K L S Y)).trans
    (Homeomorph.piCongrLeft (Y := fun i => RingPoint
      ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
      (NumberFieldLevelFactor L (numberFieldExceptionalPreimage (L := L) S) i))
      (indexEquiv K L S))

@[simp]
theorem productPointHomeomorph_apply
    (x : ∀ z : Σ i, Above K L S i,
      RingPoint
        ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
        (upperFactor K L S z.1 z.2)) (z : Σ i, Above K L S i) :
    productPointHomeomorph K L S Y x (indexEquiv K L S z) =
      factorPointHomeomorph K L S Y z (x z) := by
  simp only [productPointHomeomorph, Homeomorph.trans_apply,
    Homeomorph.piCongrLeft_apply_apply, Homeomorph.piCongrRight_apply]

variable [LocallyOfFiniteType Y.hom] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
  (n : ℕ)
  (j : Y.left ⟶ ProjectiveSpace
    ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) n) [IsImmersion j]
  (hj : j ≫ projectiveSpaceToSpec
    ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) n = Y.hom)

/-- The actual lower Weil model and actual upper model have homeomorphic original adelic-level points. -/
def adelicLevelPointHomeomorph :
    letI : TopologicalSpace
        (RingPoint (((S : Set (FinitePlace K)).integer K))
          (affineChartWeilRestriction
            (((S : Set (FinitePlace K)).integer K)) _ Y)
          (numberFieldAdeleLevel K (S))) :=
      numberFieldLevelModelPointTopology K (S)
        (affineChartWeilRestriction
          (((S : Set (FinitePlace K)).integer K)) _ Y)
    letI : TopologicalSpace (RingPoint
        ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
        (numberFieldAdeleLevel L (numberFieldExceptionalPreimage (L := L) S))) :=
      numberFieldLevelModelPointTopology L
        (numberFieldExceptionalPreimage (L := L) S) Y
    RingPoint (((S : Set (FinitePlace K)).integer K))
        (affineChartWeilRestriction
          (((S : Set (FinitePlace K)).integer K)) _ Y)
        (numberFieldAdeleLevel K (S)) ≃ₜ
      RingPoint
        ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
        (numberFieldAdeleLevel L (numberFieldExceptionalPreimage (L := L) S)) := by
  let R₀ := ((S : Set (FinitePlace K)).integer K)
  let B₀ := (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)
  let S₀ := S
  let T₀ := numberFieldExceptionalPreimage (L := L) S₀
  let U₀ := NumberFieldLevelFactor L T₀
  let W := affineChartWeilRestriction R₀ B₀ Y
  letI : TopologicalSpace (RingPoint R₀ W (numberFieldAdeleLevel K S₀)) :=
    numberFieldLevelModelPointTopology K S₀ W
  letI : TopologicalSpace (RingPoint B₀ Y (numberFieldAdeleLevel L T₀)) :=
    numberFieldLevelModelPointTopology L T₀ Y
  letI : ∀ z : Σ i, Above K L S i,
      TopologicalSpace (RingPoint B₀ Y (upperFactor K L S z.1 z.2)) :=
    fun z => schemePointTopology _ Y _
  letI : ∀ i, TopologicalSpace (RingPoint B₀ Y (U₀ i)) :=
    fun i => schemePointTopology _ Y _
  letI : ∀ i, TopologicalSpace (RingPoint (U₀ i) (ringBaseChange B₀ (U₀ i) Y) (U₀ i)) :=
    fun i => schemePointTopology _ _ _
  letI : ∀ i, IsOpenUnits (U₀ i) := by
    intro i
    cases i with
    | inl p => dsimp [U₀, NumberFieldLevelFactor]; infer_instance
    | inr z => cases z <;> dsimp [U₀, NumberFieldLevelFactor] <;> infer_instance
  let Hupper := IsHomeomorph.homeomorph (numberFieldLevelModelPointMap L T₀ Y)
    (numberFieldLevelModelPointMap_isHomeomorph_of_compact_quasiSeparated L T₀ Y)
  exact (levelPointHomeomorph K L S Y n j hj).trans
    ((productPointHomeomorph K L S Y).trans
      ((Homeomorph.piCongrRight fun i =>
        schemePointBaseChangeHomeomorph B₀ (U₀ i) (U₀ i) Y).trans Hupper.symm))

/-- The original upper level coordinates are exactly the regrouped original local Weil components. -/
theorem adelicLevelPointHomeomorph_coordinates
    (p : RingPoint (((S : Set (FinitePlace K)).integer K))
      (affineChartWeilRestriction
        (((S : Set (FinitePlace K)).integer K)) _ Y)
      (numberFieldAdeleLevel K (S))) :
    numberFieldLevelModelPointMap L
        (numberFieldExceptionalPreimage (L := L) S)
        Y (adelicLevelPointHomeomorph K L S Y n j hj p) =
      fun i => ringPointBaseChangeEquiv
        ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L))
        (NumberFieldLevelFactor L (numberFieldExceptionalPreimage (L := L) S) i)
        (NumberFieldLevelFactor L (numberFieldExceptionalPreimage (L := L) S) i) Y
        (productPointHomeomorph K L S Y
          (levelPointHomeomorph K L S Y n j hj p) i) := by
  let B₀ := (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)
  let T₀ := numberFieldExceptionalPreimage (L := L) S
  let U₀ := NumberFieldLevelFactor L T₀
  let : TopologicalSpace (RingPoint B₀ Y (numberFieldAdeleLevel L T₀)) :=
    numberFieldLevelModelPointTopology L T₀ Y
  let : ∀ z : Σ i, Above K L S i,
      TopologicalSpace (RingPoint B₀ Y (upperFactor K L S z.1 z.2)) :=
    fun z => schemePointTopology _ Y _
  let : ∀ i, TopologicalSpace (RingPoint B₀ Y (U₀ i)) :=
    fun i => schemePointTopology _ Y _
  let : ∀ i, TopologicalSpace (RingPoint (U₀ i) (ringBaseChange B₀ (U₀ i) Y) (U₀ i)) :=
    fun i => schemePointTopology _ _ _
  let : ∀ i, IsOpenUnits (U₀ i) := by
    intro i
    cases i with
    | inl p => dsimp [U₀, NumberFieldLevelFactor]; infer_instance
    | inr z => cases z <;> dsimp [U₀, NumberFieldLevelFactor] <;> infer_instance
  let Hupper := IsHomeomorph.homeomorph (numberFieldLevelModelPointMap L T₀ Y)
    (numberFieldLevelModelPointMap_isHomeomorph_of_compact_quasiSeparated L T₀ Y)
  let Hlocal := Homeomorph.piCongrRight fun i =>
    schemePointBaseChangeHomeomorph B₀ (U₀ i) (U₀ i) Y
  exact Hupper.apply_symm_apply
    (Hlocal (productPointHomeomorph K L S Y (levelPointHomeomorph K L S Y n j hj p)))

end Langlands.Global.NumberFieldSIntegerLevelRegroup
