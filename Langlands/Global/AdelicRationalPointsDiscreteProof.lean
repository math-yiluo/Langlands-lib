import Langlands.Global.AdelicRationalPointsDiscreteStatement
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeCoefficientProofs
import Langlands.Global.PrincipalAdelesDiscreteProof
import Langlands.Global.FunctionFieldAdelesDiscreteProof

/-! # Proof of the discreteness of rational and integral affine points in adelic points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- An injective map out of a discrete space with discrete image is an embedding. -/
theorem isEmbedding_of_injective_of_discreteTopology_range {X Y : Type*}
    [TopologicalSpace X] [DiscreteTopology X] [TopologicalSpace Y] {f : X → Y}
    (hf : Function.Injective f) (hr : DiscreteTopology (Set.range f)) : IsEmbedding f := by
  let e : X ≃ₜ Set.range f :=
    { toEquiv := Equiv.ofInjective f hf
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  exact IsEmbedding.subtypeVal.comp e.isEmbedding

/-- The discrete-subring transfer for actual finite-type affine points. -/
theorem affineDiscreteSubringProperty_proof (R T : Type u) [CommRing R] [CommRing T]
    [Algebra R T] [TopologicalSpace T] : AffineDiscreteSubringProperty R T := by
  intro hinj hdisc
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  intro X _ _
  have hf : IsEmbedding (Algebra.ofId R T) :=
    isEmbedding_of_injective_of_discreteTopology_range (f := Algebra.ofId R T) hinj hdisc
  have hemb : IsEmbedding (RingPoint.changeRing (X := X) (Algebra.ofId R T)) :=
    ((affineSchemeCoefficientEmbeddings_proof R R T) X (Algebra.ofId R T)).1 hf
  refine ⟨hemb, ?_⟩
  have : DiscreteTopology (RingPoint R X R) := affineSchemeDiscrete_proof R R X
  exact hemb.toHomeomorph.discreteTopology

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- A ring map has discrete image when an open neighbourhood of zero meets the image
only in zero. -/
theorem discreteTopology_range_of_isolating {A B : Type*} [Ring A] [Ring B]
    [TopologicalSpace B] [IsTopologicalRing B] (f : A →+* B) (U : Set B) (hU : IsOpen U)
    (h0 : (0 : B) ∈ U) (hiso : ∀ a, f a ∈ U → f a = 0) :
    DiscreteTopology (Set.range f) := by
  have h : DiscreteTopology f.range := by
    refine discreteTopology_of_isOpen_singleton_zero ?_
    refine isOpen_induced_iff.mpr ⟨U, hU, ?_⟩
    ext ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := RingHom.mem_range.mp hb
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro ha
      exact Subtype.ext (hiso a ha)
    · intro ha
      have ha' : f a = 0 := congrArg Subtype.val ha
      rw [ha']
      exact h0
  rw [← f.coe_range]
  exact h

/-- Rational points of a number field are discrete in points over its adeles. -/
theorem numberFieldRationalPointsDiscrete_proof :
    NumberFieldRationalPointsDiscreteStatement.{u} := by
  intro K _ _
  apply affineDiscreteSubringProperty_proof
  · exact NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers K) K
  · refine discreteTopology_range_of_isolating (algebraMap K (Adeles K))
      (principalAdelesIsolatingSet K) (isOpen_principalAdelesIsolatingSet K)
      (zero_mem_principalAdelesIsolatingSet K) fun a ha => ?_
    have h := Set.ext_iff.mp (principalAdelesIsolatingSet_inter_principalAdeles K)
      (algebraMap K (Adeles K) a)
    exact h.mp ⟨ha, a, rfl⟩

/-- `S`-integral points of a number field are discrete in points over its adelic level. -/
theorem numberFieldIntegralPointsDiscrete_proof :
    NumberFieldIntegralPointsDiscreteStatement.{u} := by
  intro K _ _ S
  have hval (c : (S : Set (FinitePlace K)).integer K) :
      ((algebraMap ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K S) c :
        numberFieldAdeleLevel K S) : Adeles K) = algebraMap K (Adeles K) c.val := rfl
  apply affineDiscreteSubringProperty_proof
  · intro c d h
    apply Subtype.ext
    apply NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers K) K
    rw [← hval, ← hval, h]
  · refine discreteTopology_range_of_isolating
      (algebraMap ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K S))
      (Subtype.val ⁻¹' principalAdelesIsolatingSet K)
      ((isOpen_principalAdelesIsolatingSet K).preimage continuous_subtype_val)
      (zero_mem_principalAdelesIsolatingSet K) fun c hc => ?_
    apply Subtype.ext
    have h := Set.ext_iff.mp (principalAdelesIsolatingSet_inter_principalAdeles K)
      (algebraMap K (Adeles K) c.val)
    rw [hval]
    rw [Set.mem_preimage, hval] at hc
    exact h.mp ⟨hc, c.val, rfl⟩

/-- Rational points of a function field are discrete in points over its curve-place
adeles. -/
theorem curvePlaceRationalPointsDiscrete_proof :
    CurvePlaceRationalPointsDiscreteStatement.{u} := by
  intro k F _ _ _ _ _ _ _
  apply affineDiscreteSubringProperty_proof
  · intro x y h
    have h' := congrArg (fun a : CurvePlaceAdeleRing k F => a (curvePlaceReference k F)) h
    exact (algebraMap F (curvePlaceCompletion (curvePlaceReference k F))).injective h'
  · refine discreteTopology_range_of_isolating (algebraMap F (CurvePlaceAdeleRing k F))
      (curvePlaceDiagonalIsolatingSet k F) (isOpen_curvePlaceDiagonalIsolatingSet k F)
      (zero_mem_curvePlaceDiagonalIsolatingSet k F) fun x hx => ?_
    have h := Set.ext_iff.mp (curvePlaceDiagonalIsolatingSet_inter_range k F)
      (algebraMap F (CurvePlaceAdeleRing k F) x)
    exact h.mp ⟨hx, x, rfl⟩

/-- Outside-`S` integral points of a function field are discrete in points over its
curve-place adelic level; no perfectness of the constant field is needed. -/
theorem curvePlaceIntegralPointsDiscrete_proof :
    CurvePlaceIntegralPointsDiscreteStatement.{u} := by
  intro k F _ _ _ _ _ _ S
  have hval (c : curvePlaceSIntegers k F S) (v : AlgebraicCurve.Place k F) :
      ((algebraMap (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F S) c :
        curvePlaceAdeleLevel k F S) : CurvePlaceAdeleRing k F) v =
        algebraMap F (curvePlaceCompletion v) c.val := rfl
  apply affineDiscreteSubringProperty_proof
  · intro c d h
    apply Subtype.ext
    have h' := congrArg (fun a : curvePlaceAdeleLevel k F S =>
      (a : CurvePlaceAdeleRing k F) (curvePlaceReference k F)) h
    simp only [hval] at h'
    exact (algebraMap F (curvePlaceCompletion (curvePlaceReference k F))).injective h'
  · refine discreteTopology_range_of_isolating
      (algebraMap (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F S))
      (Subtype.val ⁻¹' curvePlaceDiagonalIsolatingSet k F)
      ((isOpen_curvePlaceDiagonalIsolatingSet k F).preimage continuous_subtype_val)
      (zero_mem_curvePlaceDiagonalIsolatingSet k F) fun c hc => ?_
    obtain ⟨hint, hstrict⟩ := hc
    have hc0 : c.val = 0 := by
      apply eq_zero_of_forall_mem_curvePlace_of_lt_one k F
        (fun v => (curvePlaceCompletion_mem_integers_iff v c.val).mp (by
          rw [← hval]
          exact hint v))
        (curvePlaceReference k F)
      rw [hval] at hstrict
      change Valued.v (algebraMap F
        ((curvePlaceReference k F).heightOneSpectrum.adicCompletion F) c.val) < 1 at hstrict
      simpa only [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
        Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
        AlgebraicCurve.Place.adicValuation] using hstrict
    have hc' : c = 0 := Subtype.ext hc0
    rw [hc', map_zero]

/-- Conrad's discreteness of rational and integral affine points in adelic points. -/
theorem adelicRationalPointsDiscrete_proof : AdelicRationalPointsDiscreteStatement.{u} :=
  ⟨fun R T _ _ _ _ => affineDiscreteSubringProperty_proof R T,
    numberFieldRationalPointsDiscrete_proof,
    numberFieldIntegralPointsDiscrete_proof,
    curvePlaceRationalPointsDiscrete_proof,
    curvePlaceIntegralPointsDiscrete_proof⟩

end Langlands.Global
