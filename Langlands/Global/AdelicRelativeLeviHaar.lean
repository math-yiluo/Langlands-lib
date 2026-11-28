import Langlands.Global.AdelicPositiveDecompositionReduction
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Global.LeftCosetProductMeasureProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof

/-! # Ambient norm-one Levi measures in relative split coordinates -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Set Topology
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

universe u

variable {F : Type u} [Field F] [NumberField F]
  {G M : GroupScheme (Spec (CommRingCat.of F))} (j : M ⟶ G)
  {A : CommGroupScheme (Spec (CommRingCat.of F))} (i : A.toGrp ⟶ M)

/-- Levi points whose images have norm one for the characters of the ambient group. -/
def ambientNormOneLevi : Subgroup (AdelicGroupPoints F M) :=
  (normOneSubgroup F G).comap (map F M G j).toMonoidHom

/-- The relative split component in the actual positive points of `A`. -/
def relativePositiveSubgroup : Subgroup (intrinsicSubgroup F A) :=
  (ambientNormOneLevi j).comap (positivePointMap F M A i).toMonoidHom

/-- The ambient norm-one condition on Levi points is closed. -/
theorem isClosed_ambientNormOneLevi :
    IsClosed (ambientNormOneLevi j : Set (AdelicGroupPoints F M)) :=
  (isClosed_normOneSubgroup F G).preimage (map F M G j).continuous

/-- The relative positive subgroup is closed in the positive split component. -/
theorem isClosed_relativePositiveSubgroup :
    IsClosed (relativePositiveSubgroup j i : Set (intrinsicSubgroup F A)) :=
  (isClosed_ambientNormOneLevi j).preimage (positivePointMap F M A i).continuous

private theorem normOne_le_ambientNormOneLevi :
    normOneSubgroup F M ≤ ambientNormOneLevi j := by
  intro m hm
  exact (mapNormOne F M G j ⟨m, hm⟩).property

/-- The intrinsic norm-one subgroup as a subgroup of the ambient norm-one Levi. -/
def relativeLeviInclusion : normOneSubgroup F M →* ambientNormOneLevi j :=
  (normOneSubgroup F M).subtype.codRestrict _ fun m =>
    normOne_le_ambientNormOneLevi j m.property

section Split

variable [IsAffineHom M.X.hom] (hM : IsConnectedReductive M) (hi : IsSplitComponent i)

private theorem split_mem_ambientNormOneLevi
    (p : intrinsicSubgroup F A × normOneSubgroup F M) :
    splitComponentNormOneDecomposition centralSplitTorusCharacter F M hM A i hi p ∈
      ambientNormOneLevi j ↔ p.1 ∈ relativePositiveSubgroup j i := by
  rw [splitComponentNormOneDecomposition_apply]
  have hm := normOne_le_ambientNormOneLevi j p.2.property
  exact (ambientNormOneLevi j).mul_mem_cancel_right hm

/-- Multiplication identifies the ambient norm-one Levi with the relative positive subgroup
times the intrinsic norm-one Levi. -/
def relativeLeviDecomposition :
    relativePositiveSubgroup j i × normOneSubgroup F M ≃ₜ* ambientNormOneLevi j := by
  let e := splitComponentNormOneDecomposition centralSplitTorusCharacter F M hM A i hi
  let incl : relativePositiveSubgroup j i × normOneSubgroup F M →*
      intrinsicSubgroup F A × normOneSubgroup F M :=
    (relativePositiveSubgroup j i).subtype.prodMap (MonoidHom.id _)
  have he (p : intrinsicSubgroup F A × normOneSubgroup F M) :
      e p ∈ ambientNormOneLevi j ↔ p.1 ∈ relativePositiveSubgroup j i :=
    split_mem_ambientNormOneLevi j i hM hi p
  have ha (x : ambientNormOneLevi j) : (e.symm x.val).1 ∈ relativePositiveSubgroup j i :=
    (he (e.symm x.val)).mp (by simpa only [e.apply_symm_apply] using x.property)
  refine {
    toFun := fun p => ⟨e (incl p), (he (incl p)).mpr p.1.property⟩
    invFun := fun x => (⟨(e.symm x.val).1, ha x⟩, (e.symm x.val).2)
    left_inv := ?_
    right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val)
    map_mul' := fun p q => Subtype.ext (by
      change e (incl (p * q)) = e (incl p) * e (incl q)
      exact (congrArg e (map_mul incl p q)).trans (map_mul e _ _))
    continuous_toFun := (e.continuous.comp
      (continuous_subtype_val.prodMap continuous_id)).subtype_mk _
    continuous_invFun := ?_ }
  · intro p
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (e.symm_apply_apply (incl p))
    · change (e.symm (e (incl p))).2 = (incl p).2
      exact congrArg Prod.snd (e.symm_apply_apply (incl p))
  · have h := e.symm.continuous.comp
      (continuous_subtype_val : Continuous (Subtype.val : ambientNormOneLevi j → _))
    exact (h.fst.subtype_mk ha).prodMk h.snd

@[simp] theorem relativeLeviDecomposition_apply
    (p : relativePositiveSubgroup j i × normOneSubgroup F M) :
    (relativeLeviDecomposition j i hM hi p : AdelicGroupPoints F M) =
      positivePointMap F M A i p.1.val * p.2 := rfl

end Split

/-- The principal subgroup of the ambient norm-one Levi, included from the intrinsic
norm-one Levi. -/
def relativeLeviRationalSubgroup : Subgroup (ambientNormOneLevi j) :=
  (rationalNormOneSubgroup F M).map (relativeLeviInclusion j)

variable [IsAffineHom M.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (hM : IsConnectedReductive M) (hi : IsSplitComponent i)

instance ambientNormOneLevi_secondCountable :
    SecondCountableTopology (ambientNormOneLevi j) :=
  TopologicalSpace.secondCountableTopology_induced _ (AdelicGroupPoints F M) Subtype.val

instance ambientNormOneLevi_locallyCompact :
    LocallyCompactSpace (ambientNormOneLevi j) :=
  (isClosed_ambientNormOneLevi j).locallyCompactSpace

omit [IsAffineHom M.X.hom] in
theorem isDiscrete_relativeLeviRationalSubgroup :
    IsDiscrete (relativeLeviRationalSubgroup j : Set (ambientNormOneLevi j)) :=
  (isDiscrete_rationalNormOneSubgroup F M).image
    (IsInducing.subtypeVal.codRestrict _)

omit [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] in
theorem relativeLeviDecomposition_mem_rational
    (p : relativePositiveSubgroup j i × normOneSubgroup F M) :
    relativeLeviDecomposition j i hM hi p ∈ relativeLeviRationalSubgroup j ↔
      p.1 = 1 ∧ p.2 ∈ rationalNormOneSubgroup F M := by
  have he (m : normOneSubgroup F M) :
      relativeLeviDecomposition j i hM hi (1, m) = relativeLeviInclusion j m := by
    apply Subtype.ext
    simp [relativeLeviInclusion]
  constructor
  · rintro ⟨m, hm, heq⟩
    have hp := (relativeLeviDecomposition j i hM hi).injective ((he m).trans heq)
    exact ⟨(congrArg Prod.fst hp).symm, congrArg Prod.snd hp ▸ hm⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨p.2, h₂, (he p.2).symm.trans
      (congrArg (relativeLeviDecomposition j i hM hi) (Prod.ext h₁.symm rfl))⟩

/-- A normalization of relative positive Haar makes the Haar product exact, with any
prescribed choice of ambient norm-one Levi Haar. -/
theorem exists_relativeLeviHaarProduct (dm : Measure (ambientNormOneLevi j)) [dm.IsHaarMeasure] :
    ∃ μA : Measure (relativePositiveSubgroup j i), μA.IsHaarMeasure ∧ SigmaFinite μA ∧
      MeasurePreserving (relativeLeviDecomposition j i hM hi)
        (μA.prod (Measure.haar : Measure (normOneSubgroup F M))) dm := by
  let I : Type u := hi.1.1.1.choose
  let : Finite I := hi.1.1.1.choose_spec.choose
  let : Fintype I := Fintype.ofFinite I
  let e : A.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I :=
    hi.1.1.1.choose_spec.choose_spec.some
  let : IsTopologicalGroup (intrinsicSubgroup F A) := positiveIsTopologicalGroup F A I e
  let : LocallyCompactSpace (intrinsicSubgroup F A) := positiveLocallyCompactSpace F A I e
  let : SecondCountableTopology (intrinsicSubgroup F A) :=
    positiveSecondCountableTopology F A I e
  let : SecondCountableTopology (relativePositiveSubgroup j i) :=
    TopologicalSpace.secondCountableTopology_induced _ (intrinsicSubgroup F A) Subtype.val
  let : LocallyCompactSpace (relativePositiveSubgroup j i) :=
    (isClosed_relativePositiveSubgroup j i).locallyCompactSpace
  let E := relativeLeviDecomposition j i hM hi
  let μ₀ : Measure (relativePositiveSubgroup j i) := Measure.haar
  let ν := Measure.map E (μ₀.prod (Measure.haar : Measure (normOneSubgroup F M)))
  let : ν.IsHaarMeasure := E.isHaarMeasure_map _
  let c := dm.haarScalarFactor ν
  have hc : 0 < c := haarScalarFactor_pos_of_isHaarMeasure dm ν
  have hE : Measurable (fun p => E p) := E.toHomeomorph.continuous.measurable
  refine ⟨c • μ₀, IsHaarMeasure.nnreal_smul _ hc.ne', inferInstance, hE, ?_⟩
  change Measure.map (fun p => E p) ((c • μ₀).prod Measure.haar) = dm
  rw [Measure.prod_smul_left, Measure.map_smul _ hE.aemeasurable]
  exact (isMulLeftInvariant_eq_smul dm ν).symm

/-- In the ambient norm-one Levi quotient only the intrinsic norm-one coordinate is
quotiented by principal points. The Haar normalization can be carried by the relative
positive coordinate alone. -/
theorem exists_relativeLeviQuotientProduct (dm : Measure (ambientNormOneLevi j))
    [dm.IsHaarMeasure] :
    ∃ μA : Measure (relativePositiveSubgroup j i), μA.IsHaarMeasure ∧
      MeasurePreserving
        (LeftCosetSpace.productHomeomorph (relativeLeviDecomposition j i hM hi)
          (rationalNormOneSubgroup F M) (relativeLeviRationalSubgroup j)
          (relativeLeviDecomposition_mem_rational j i hM hi))
        (LeftCosetSpace.discreteQuotientMeasure (relativeLeviRationalSubgroup j)
          (isDiscrete_relativeLeviRationalSubgroup j) dm)
        (μA.prod (normOneRationalQuotientHaarMeasure F M)) := by
  obtain ⟨μA, hHaar, hSF, hE⟩ := exists_relativeLeviHaarProduct j i hM hi dm
  exact ⟨μA, hHaar, LeftCosetSpace.productQuotientMeasure
    (relativeLeviDecomposition j i hM hi) (rationalNormOneSubgroup F M)
    (relativeLeviRationalSubgroup j) (relativeLeviDecomposition_mem_rational j i hM hi)
    (isDiscrete_rationalNormOneSubgroup F M) (isDiscrete_relativeLeviRationalSubgroup j)
    μA Measure.haar dm hE⟩

end Langlands.Global.PositiveRealTorus
