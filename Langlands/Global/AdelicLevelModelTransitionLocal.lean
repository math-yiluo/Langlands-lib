import Langlands.Global.AdelicLevelModelTransition
import Langlands.AlgebraicGeometry.PointTopology.SchemeCoefficientProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeSeparatedCoefficientProofs
import Langlands.AlgebraicGeometry.PointTopology.SchemeBaseChangeTopologyProofs

/-! # Local maps for actual changes of adelic level -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C D A B : Type u) [CommRing C] [CommRing D] [CommRing A] [CommRing B]
variable [Algebra C D] [Algebra C A] [Algebra C B] [Algebra D B]
variable [IsScalarTower C D B]

/-- Forget the source local base change, extend coefficients and make both target base changes. -/
def localBaseChangeCoefficientMap (X : Over (Spec (CommRingCat.of C)))
    (f : A →ₐ[C] B) :
    RingPoint A (ringBaseChange C A X) A →
      RingPoint B (ringBaseChange D B (ringBaseChange C D X)) B := fun q =>
  ringPointBaseChangeEquiv D B B (ringBaseChange C D X)
    (ringPointBaseChangeEquiv C D B X
      (RingPoint.changeRing f ((ringPointBaseChangeEquiv C A A X).symm q)))

/-- Its composite projection to the original model is the literal local coefficient change. -/
theorem localBaseChangeCoefficientMap_left_fst_fst
    (X : Over (Spec (CommRingCat.of C))) (f : A →ₐ[C] B)
    (q : RingPoint A (ringBaseChange C A X) A) :
    ((localBaseChangeCoefficientMap C D A B X f q).left ≫
        pullback.fst (ringBaseChange C D X).hom (Spec.algebraMap D B)) ≫
      pullback.fst X.hom (Spec.algebraMap C D) =
        Spec.map (CommRingCat.ofHom f.toRingHom) ≫
          (q.left ≫ pullback.fst X.hom (Spec.algebraMap C A)) := by
  let p := RingPoint.changeRing f ((ringPointBaseChangeEquiv C A A X).symm q)
  have h₁ := ringPointBaseChangeEquiv_left_fst D B B (ringBaseChange C D X)
    (ringPointBaseChangeEquiv C D B X p)
  have h₂ := ringPointBaseChangeEquiv_left_fst C D B X p
  have h₃ : p.left = Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      ((ringPointBaseChangeEquiv C A A X).symm q).left := rfl
  exact (congrArg (fun r => r ≫ pullback.fst X.hom (Spec.algebraMap C D)) h₁).trans
    (h₂.trans (h₃.trans
      (congrArg (fun r => Spec.map (CommRingCat.ofHom f.toRingHom) ≫ r)
        (ringPointBaseChangeEquiv_symm_left C A A X q))))

/-- A point of the twice-base-changed model is determined by its original projection. -/
theorem ringPoint_doubleBaseChange_ext
    (X : Over (Spec (CommRingCat.of C)))
    (p q : RingPoint B (ringBaseChange D B (ringBaseChange C D X)) B)
    (h : (p.left ≫ pullback.fst (ringBaseChange C D X).hom (Spec.algebraMap D B)) ≫
          pullback.fst X.hom (Spec.algebraMap C D) =
        (q.left ≫ pullback.fst (ringBaseChange C D X).hom (Spec.algebraMap D B)) ≫
          pullback.fst X.hom (Spec.algebraMap C D)) : p = q := by
  apply (ringPointBaseChangeEquiv D B B (ringBaseChange C D X)).symm.injective
  apply (ringPointBaseChangeEquiv C D B X).symm.injective
  apply Over.OverMorphism.ext
  simpa only [ringPointBaseChangeEquiv_symm_left, ringTest] using h

/-- A bijective local coefficient map gives a bijection of the local-model points. -/
theorem localBaseChangeCoefficientMap_bijective
    (X : Over (Spec (CommRingCat.of C))) (f : A →ₐ[C] B)
    (hf : Function.Bijective f) :
    Function.Bijective (localBaseChangeCoefficientMap C D A B X f) := by
  have hc : Function.Bijective (RingPoint.changeRing (X := X) f) :=
    (ringPointChangeRingEquiv C X (AlgEquiv.ofBijective f hf)).bijective
  exact (ringPointBaseChangeEquiv D B B (ringBaseChange C D X)).bijective.comp
    ((ringPointBaseChangeEquiv C D B X).bijective.comp
      (hc.comp (ringPointBaseChangeEquiv C A A X).symm.bijective))

/-- Separatedness and reduced source coefficients give local injectivity. -/
theorem localBaseChangeCoefficientMap_injective [_root_.IsReduced A]
    (X : Over (Spec (CommRingCat.of C))) [IsSeparated X.hom]
    (f : A →ₐ[C] B) (hf : Function.Injective f) :
    Function.Injective (localBaseChangeCoefficientMap C D A B X f) := by
  exact (ringPointBaseChangeEquiv D B B (ringBaseChange C D X)).injective.comp
    ((ringPointBaseChangeEquiv C D B X).injective.comp
      ((schemeSeparatedCoefficientInjectivity_proof C A B X f hf).comp
        (ringPointBaseChangeEquiv C A A X).symm.injective))


variable [TopologicalSpace A] [TopologicalSpace B]
variable [IsTopologicalRing A] [IsTopologicalRing B]
variable [IsLocalRing A] [IsLocalRing B] [IsOpenUnits A] [IsOpenUnits B]

/-- The local transition is continuous for every model. -/
theorem continuous_localBaseChangeCoefficientMap
    (X : Over (Spec (CommRingCat.of C))) (f : A →ₐ[C] B) (hf : Continuous f) :
    Continuous[schemePointTopology A (ringBaseChange C A X) A,
      schemePointTopology B (ringBaseChange D B (ringBaseChange C D X)) B]
      (localBaseChangeCoefficientMap C D A B X f) := by
  let : TopologicalSpace (RingPoint C X A) := schemePointTopology C X A
  let : TopologicalSpace (RingPoint A (ringBaseChange C A X) A) :=
    schemePointTopology A (ringBaseChange C A X) A
  let : TopologicalSpace (RingPoint C X B) := schemePointTopology C X B
  let : TopologicalSpace (RingPoint D (ringBaseChange C D X) B) :=
    schemePointTopology D (ringBaseChange C D X) B
  let : TopologicalSpace (RingPoint B (ringBaseChange D B (ringBaseChange C D X)) B) :=
    schemePointTopology B (ringBaseChange D B (ringBaseChange C D X)) B
  have hA := schemeBaseChangeTopology_proof C A A X
  have hAi := (ringPointBaseChangeEquiv C A A X).continuous_symm_iff.mpr hA.isOpenMap
  exact (schemeBaseChangeTopology_proof D B B (ringBaseChange C D X)).continuous.comp
    ((schemeBaseChangeTopology_proof C D B X).continuous.comp
      ((schemeCoefficientContinuity_proof C A B X f hf).comp hAi))

/-- Local finite type makes each local transition open. -/
theorem isOpenMap_localBaseChangeCoefficientMap
    (X : Over (Spec (CommRingCat.of C))) [LocallyOfFiniteType X.hom]
    (f : A →ₐ[C] B) (hf : IsOpenEmbedding f) :
    letI := schemePointTopology A (ringBaseChange C A X) A
    letI := schemePointTopology B (ringBaseChange D B (ringBaseChange C D X)) B
    IsOpenMap (localBaseChangeCoefficientMap C D A B X f) := by
  let : TopologicalSpace (RingPoint C X A) := schemePointTopology C X A
  let : TopologicalSpace (RingPoint A (ringBaseChange C A X) A) :=
    schemePointTopology A (ringBaseChange C A X) A
  let : TopologicalSpace (RingPoint C X B) := schemePointTopology C X B
  let : TopologicalSpace (RingPoint D (ringBaseChange C D X) B) :=
    schemePointTopology D (ringBaseChange C D X) B
  let : TopologicalSpace (RingPoint B (ringBaseChange D B (ringBaseChange C D X)) B) :=
    schemePointTopology B (ringBaseChange D B (ringBaseChange C D X)) B
  have hA := schemeBaseChangeTopology_proof C A A X
  have hAi := (ringPointBaseChangeEquiv C A A X).continuous_symm_iff.mpr hA.isOpenMap
  have hAio := ((ringPointBaseChangeEquiv C A A X).symm.isHomeomorph_iff.mpr
    ⟨hAi, hA.continuous⟩).isOpenMap
  exact (schemeBaseChangeTopology_proof D B B (ringBaseChange C D X)).isOpenMap.comp
    ((schemeBaseChangeTopology_proof C D B X).isOpenMap.comp
      ((schemeCoefficientOpen_proof C A B X f hf).comp hAio))


end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable {S T : Finset (AlgebraicCurve.Place k F)} (hST : S ⊆ T)

/-- Match each target factor with the source factor at the identical actual place. -/
def curvePlaceLevelSourceIndex :
    CurvePlaceLevelFactorIndex k F T → CurvePlaceLevelFactorIndex k F S := by
  classical
  exact fun i => (Equiv.sumCompl (fun v => v ∈ S)).symm
    (Equiv.sumCompl (fun v => v ∈ T) i)

/-- This index match is an equivalence because both sides enumerate all places. -/
def curvePlaceLevelSourceIndexEquiv :
    CurvePlaceLevelFactorIndex k F T ≃ CurvePlaceLevelFactorIndex k F S := by
  classical
  exact (Equiv.sumCompl (fun v => v ∈ T)).trans (Equiv.sumCompl (fun v => v ∈ S)).symm

@[simp]
theorem curvePlaceLevelSourceIndex_inl_of_mem
    (v : {v : AlgebraicCurve.Place k F // v ∈ T}) (hv : v.1 ∈ S) :
    curvePlaceLevelSourceIndex k F (S := S) (.inl v) = .inl ⟨v.1, hv⟩ := by
  classical
  exact Equiv.sumCompl_symm_apply_of_pos hv

@[simp]
theorem curvePlaceLevelSourceIndex_inl_of_not_mem
    (v : {v : AlgebraicCurve.Place k F // v ∈ T}) (hv : v.1 ∉ S) :
    curvePlaceLevelSourceIndex k F (S := S) (.inl v) = .inr ⟨v.1, hv⟩ := by
  classical
  exact Equiv.sumCompl_symm_apply_of_neg hv

@[simp]
theorem curvePlaceLevelSourceIndex_inr
    (v : {v : AlgebraicCurve.Place k F // v ∉ T}) :
    curvePlaceLevelSourceIndex k F (S := S) (.inr v) =
      .inr ⟨v.1, fun h => v.2 (hST h)⟩ := by
  classical
  exact Equiv.sumCompl_symm_apply_of_neg (fun h => v.2 (hST h))

/-- Whether the local coefficient ring does not change at the target index. -/
def curvePlaceLevelUnchanged (i : CurvePlaceLevelFactorIndex k F T) : Prop :=
  match i with
  | .inl v => v.1 ∈ S
  | .inr _ => True

/-- Construct the literal local homomorphism together with its coordinate identity and topology. -/
def curvePlaceLevelLocalRingHomData (i : CurvePlaceLevelFactorIndex k F T) :
    { f : CurvePlaceLevelFactor k F S (curvePlaceLevelSourceIndex k F i) →+*
        CurvePlaceLevelFactor k F T i //
      f.comp (curvePlaceLevelFactorProjection k F S (curvePlaceLevelSourceIndex k F i)) =
        (curvePlaceLevelFactorProjection k F T i).comp (curvePlaceAdeleLevelMap k F hST) ∧
      IsOpenEmbedding f ∧ (curvePlaceLevelUnchanged k F (S := S) i → Function.Bijective f) } := by
  classical
  cases i with
  | inl v =>
    by_cases hv : v.1 ∈ S
    · rw [curvePlaceLevelSourceIndex_inl_of_mem k F v hv]
      refine ⟨RingHom.id _, ?_, IsOpenEmbedding.id, fun _ => Function.bijective_id⟩
      ext a
      rfl
    · rw [curvePlaceLevelSourceIndex_inl_of_not_mem k F v hv]
      refine ⟨(curvePlaceCompletionIntegers v.1).subtype, ?_, ?_, ?_⟩
      · ext a
        rfl
      · exact (Valued.isOpen_valuationSubring (curvePlaceCompletion v.1)).isOpenEmbedding_subtypeVal
      · exact fun h => (hv h).elim
  | inr v =>
    rw [curvePlaceLevelSourceIndex_inr k F hST v]
    refine ⟨RingHom.id _, ?_, IsOpenEmbedding.id, fun _ => Function.bijective_id⟩
    ext a
    rfl

/-- At a newly inverted place use the original valuation-subring inclusion. -/
def curvePlaceLevelLocalRingHom (i : CurvePlaceLevelFactorIndex k F T) :
    CurvePlaceLevelFactor k F S (curvePlaceLevelSourceIndex k F i) →+*
      CurvePlaceLevelFactor k F T i :=
  (curvePlaceLevelLocalRingHomData k F hST i).val

/-- Local coefficient extension is the actual coordinate of the level inclusion. -/
theorem curvePlaceLevelLocalRingHom_projection (i : CurvePlaceLevelFactorIndex k F T) :
    (curvePlaceLevelLocalRingHom k F hST i).comp
        (curvePlaceLevelFactorProjection k F S (curvePlaceLevelSourceIndex k F i)) =
      (curvePlaceLevelFactorProjection k F T i).comp (curvePlaceAdeleLevelMap k F hST) :=
  (curvePlaceLevelLocalRingHomData k F hST i).property.1

/-- Every local inclusion is an open embedding with its original topology. -/
theorem isOpenEmbedding_curvePlaceLevelLocalRingHom (i : CurvePlaceLevelFactorIndex k F T) :
    IsOpenEmbedding (curvePlaceLevelLocalRingHom k F hST i) :=
  (curvePlaceLevelLocalRingHomData k F hST i).property.2.1

/-- Unchanged places give bijective local coefficient maps. -/
theorem curvePlaceLevelLocalRingHom_bijective (i : CurvePlaceLevelFactorIndex k F T)
    (hi : curvePlaceLevelUnchanged k F (S := S) i) :
    Function.Bijective (curvePlaceLevelLocalRingHom k F hST i) :=
  (curvePlaceLevelLocalRingHomData k F hST i).property.2.2 hi

/-- Only finitely many local coefficient maps can fail to be bijective. -/
theorem curvePlaceLevelUnchanged_cofinite :
    {i : CurvePlaceLevelFactorIndex k F T | ¬ curvePlaceLevelUnchanged k F (S := S) i}.Finite := by
  classical
  have hfin : (Set.range (fun v : {v : AlgebraicCurve.Place k F // v ∈ T} =>
      (Sum.inl v : CurvePlaceLevelFactorIndex k F T))).Finite := Set.finite_range _
  apply hfin.subset
  rintro (v | v) hi
  · exact ⟨v, rfl⟩
  · exact (hi trivial).elim

/-- Every actual local factor is reduced, including completed valuation rings. -/
theorem curvePlaceLevelFactor_isReduced (i : CurvePlaceLevelFactorIndex k F S) :
    _root_.IsReduced (CurvePlaceLevelFactor k F S i) := by
  cases i with
  | inl v => exact inferInstanceAs (_root_.IsReduced (curvePlaceCompletion v.1))
  | inr v => exact inferInstanceAs (_root_.IsReduced (curvePlaceCompletionIntegers v.1))

/-- Restrict the target local scalar action along the literal integer inclusion. -/
abbrev curvePlaceLevelTargetFactorAlgebra (i : CurvePlaceLevelFactorIndex k F T) :
    Algebra (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F T i) :=
  ((algebraMap (curvePlaceSIntegers k F T) (CurvePlaceLevelFactor k F T i)).comp
    (curvePlaceSIntegersMap k F hST)).toAlgebra

/-- The original local coefficient map respects the original source integer scalars. -/
def curvePlaceLevelLocalAlgHom (i : CurvePlaceLevelFactorIndex k F T) :
    letI := curvePlaceLevelTargetFactorAlgebra k F hST i
    CurvePlaceLevelFactor k F S (curvePlaceLevelSourceIndex k F i) →ₐ[curvePlaceSIntegers k F S]
      CurvePlaceLevelFactor k F T i := by
  letI := curvePlaceLevelTargetFactorAlgebra k F hST i
  refine { curvePlaceLevelLocalRingHom k F hST i with commutes' := ?_ }
  intro c
  change curvePlaceLevelLocalRingHom k F hST i
      (curvePlaceLevelFactorProjection k F S (curvePlaceLevelSourceIndex k F i)
        (curvePlaceAdeleLevelDiagonal k F S c)) =
    curvePlaceLevelFactorProjection k F T i
      (curvePlaceAdeleLevelDiagonal k F T (curvePlaceSIntegersMap k F hST c))
  exact (congrArg (fun f : curvePlaceAdeleLevel k F S →+* CurvePlaceLevelFactor k F T i =>
      f (curvePlaceAdeleLevelDiagonal k F S c))
        (curvePlaceLevelLocalRingHom_projection k F hST i)).trans
    (congrArg (fun f : curvePlaceSIntegers k F S →+* curvePlaceAdeleLevel k F T =>
      curvePlaceLevelFactorProjection k F T i (f c))
        (curvePlaceAdeleLevelDiagonal_natural k F hST))

/-- The actual local point transition with both target base changes. -/
def curvePlaceLevelLocalPointMap
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (i : CurvePlaceLevelFactorIndex k F T) :
    RingPoint (CurvePlaceLevelFactor k F S (curvePlaceLevelSourceIndex k F i))
        (ringBaseChange (curvePlaceSIntegers k F S)
          (CurvePlaceLevelFactor k F S (curvePlaceLevelSourceIndex k F i)) X)
        (CurvePlaceLevelFactor k F S (curvePlaceLevelSourceIndex k F i)) →
      RingPoint (CurvePlaceLevelFactor k F T i)
        (ringBaseChange (curvePlaceSIntegers k F T) (CurvePlaceLevelFactor k F T i)
          (curvePlaceLevelModelBaseChange k F hST X)) (CurvePlaceLevelFactor k F T i) := by
  letI := (curvePlaceSIntegersMap k F hST).toAlgebra
  letI := curvePlaceLevelTargetFactorAlgebra k F hST i
  letI : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T)
      (CurvePlaceLevelFactor k F T i) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact localBaseChangeCoefficientMap _ _ _ _ X (curvePlaceLevelLocalAlgHom k F hST i)

/-- The local transition is the original arithmetic transition in the original coordinates. -/
theorem curvePlaceLevelModelTransition_coordinates
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
    (i : CurvePlaceLevelFactorIndex k F T) :
    curvePlaceLevelModelPointMap k F T (curvePlaceLevelModelBaseChange k F hST X)
        (curvePlaceLevelModelTransition k F hST X p) i =
      curvePlaceLevelLocalPointMap k F hST X i
        (curvePlaceLevelModelPointMap k F S X p (curvePlaceLevelSourceIndex k F i)) := by
  let :=  (curvePlaceSIntegersMap k F hST).toAlgebra
  let :=  curvePlaceLevelTargetFactorAlgebra k F hST i
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T)
      (CurvePlaceLevelFactor k F T i) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply ringPoint_doubleBaseChange_ext (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F T) (CurvePlaceLevelFactor k F T i) X
  refine Eq.trans ?_ (localBaseChangeCoefficientMap_left_fst_fst
    (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T)
    (CurvePlaceLevelFactor k F S (curvePlaceLevelSourceIndex k F i))
    (CurvePlaceLevelFactor k F T i) X (curvePlaceLevelLocalAlgHom k F hST i)
    (curvePlaceLevelModelPointMap k F S X p (curvePlaceLevelSourceIndex k F i))).symm
  have h₁ := congrArg (fun r => r ≫
      pullback.fst X.hom (Spec.algebraMap (curvePlaceSIntegers k F S)
        (curvePlaceSIntegers k F T)))
    (curvePlaceLevelModelPointMap_left_fst k F T
      (curvePlaceLevelModelBaseChange k F hST X)
      (curvePlaceLevelModelTransition k F hST X p) i)
  have h₂ := congrArg (fun r =>
      Spec.map (CommRingCat.ofHom (curvePlaceLevelFactorProjection k F T i)) ≫ r)
    (curvePlaceLevelModelTransition_left_fst k F hST X p)
  have h₃ := congrArg (fun r =>
      Spec.map (CommRingCat.ofHom (curvePlaceLevelLocalRingHom k F hST i)) ≫ r)
    (curvePlaceLevelModelPointMap_left_fst k F S X p
      (curvePlaceLevelSourceIndex k F i))
  have h₄ :
      Spec.map (CommRingCat.ofHom (curvePlaceLevelFactorProjection k F T i)) ≫
          (Spec.map (CommRingCat.ofHom (curvePlaceAdeleLevelMap k F hST)) ≫ p.left) =
        Spec.map (CommRingCat.ofHom (curvePlaceLevelLocalRingHom k F hST i)) ≫
          (Spec.map (CommRingCat.ofHom (curvePlaceLevelFactorProjection k F S
            (curvePlaceLevelSourceIndex k F i))) ≫ p.left) := by
    erw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : curvePlaceAdeleLevel k F S →+* CurvePlaceLevelFactor k F T i =>
      Spec.map (CommRingCat.ofHom f) ≫ p.left)
      (curvePlaceLevelLocalRingHom_projection k F hST i).symm
  exact h₁.trans ((Category.assoc _ _ _).trans (h₂.trans (h₄.trans h₃.symm)))

end Curve

section NumberField

variable (K : Type u) [Field K]
variable {S T : Finset (FinitePlace K)} (hST : S ⊆ T)

/-- Keep every infinite place and match finite indices by the underlying actual place. -/
def numberFieldLevelSourceIndex :
    NumberFieldLevelFactorIndex K T → NumberFieldLevelFactorIndex K S := by
  classical
  exact Sum.map id (fun i => (Equiv.sumCompl (fun v => v ∈ S)).symm
    (Equiv.sumCompl (fun v => v ∈ T) i))

/-- The full source index match is an equivalence, including the infinite places. -/
def numberFieldLevelSourceIndexEquiv :
    NumberFieldLevelFactorIndex K T ≃ NumberFieldLevelFactorIndex K S := by
  classical
  exact Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCompl (fun v => v ∈ T)).trans
    (Equiv.sumCompl (fun v => v ∈ S)).symm)

@[simp]
theorem numberFieldLevelSourceIndex_infinite (v : InfinitePlace K) :
    numberFieldLevelSourceIndex K (S := S) (T := T) (.inl v) = .inl v := rfl

@[simp]
theorem numberFieldLevelSourceIndex_finite_of_mem
    (v : {v : FinitePlace K // v ∈ T}) (hv : v.1 ∈ S) :
    numberFieldLevelSourceIndex K (S := S) (.inr (.inl v)) = .inr (.inl ⟨v.1, hv⟩) := by
  classical
  exact congrArg Sum.inr (Equiv.sumCompl_symm_apply_of_pos hv)

@[simp]
theorem numberFieldLevelSourceIndex_finite_of_not_mem
    (v : {v : FinitePlace K // v ∈ T}) (hv : v.1 ∉ S) :
    numberFieldLevelSourceIndex K (S := S) (.inr (.inl v)) = .inr (.inr ⟨v.1, hv⟩) := by
  classical
  exact congrArg Sum.inr (Equiv.sumCompl_symm_apply_of_neg hv)

@[simp]
theorem numberFieldLevelSourceIndex_integer
    (v : {v : FinitePlace K // v ∉ T}) :
    numberFieldLevelSourceIndex K (S := S) (.inr (.inr v)) =
      .inr (.inr ⟨v.1, fun h => v.2 (hST h)⟩) := by
  classical
  exact congrArg Sum.inr (Equiv.sumCompl_symm_apply_of_neg (fun h => v.2 (hST h)))

/-- Every infinite place and every finite place outside T is unchanged. -/
def numberFieldLevelUnchanged (i : NumberFieldLevelFactorIndex K T) : Prop :=
  match i with
  | .inl _ => True
  | .inr (.inl v) => v.1 ∈ S
  | .inr (.inr _) => True

variable [NumberField K]

/-- Actual local homomorphisms and their projection, openness and unchanged-place laws. -/
def numberFieldLevelLocalRingHomData (i : NumberFieldLevelFactorIndex K T) :
    { f : NumberFieldLevelFactor K S (numberFieldLevelSourceIndex K i) →+*
        NumberFieldLevelFactor K T i //
      f.comp (numberFieldLevelFactorProjection K S (numberFieldLevelSourceIndex K i)) =
        (numberFieldLevelFactorProjection K T i).comp (numberFieldAdeleLevelMap K hST) ∧
      IsOpenEmbedding f ∧ (numberFieldLevelUnchanged K (S := S) i → Function.Bijective f) } := by
  classical
  cases i with
  | inl v =>
    refine ⟨RingHom.id _, ?_, IsOpenEmbedding.id, fun _ => Function.bijective_id⟩
    ext a
    rfl
  | inr j =>
    cases j with
    | inl v =>
      by_cases hv : v.1 ∈ S
      · rw [numberFieldLevelSourceIndex_finite_of_mem K v hv]
        refine ⟨RingHom.id _, ?_, IsOpenEmbedding.id, fun _ => Function.bijective_id⟩
        ext a
        rfl
      · rw [numberFieldLevelSourceIndex_finite_of_not_mem K v hv]
        refine ⟨(v.1.adicCompletionIntegers K).subtype, ?_, ?_, ?_⟩
        · ext a
          rfl
        · exact (Valued.isOpen_valuationSubring (FiniteCompletion K v.1)).isOpenEmbedding_subtypeVal
        · exact fun h => (hv h).elim
    | inr v =>
      rw [numberFieldLevelSourceIndex_integer K hST v]
      refine ⟨RingHom.id _, ?_, IsOpenEmbedding.id, fun _ => Function.bijective_id⟩
      ext a
      rfl

/-- The actual coefficient inclusion at one full adelic factor. -/
def numberFieldLevelLocalRingHom (i : NumberFieldLevelFactorIndex K T) :
    NumberFieldLevelFactor K S (numberFieldLevelSourceIndex K i) →+*
      NumberFieldLevelFactor K T i :=
  (numberFieldLevelLocalRingHomData K hST i).val

/-- Local and full adelic coefficient changes commute. -/
theorem numberFieldLevelLocalRingHom_projection (i : NumberFieldLevelFactorIndex K T) :
    (numberFieldLevelLocalRingHom K hST i).comp
        (numberFieldLevelFactorProjection K S (numberFieldLevelSourceIndex K i)) =
      (numberFieldLevelFactorProjection K T i).comp (numberFieldAdeleLevelMap K hST) :=
  (numberFieldLevelLocalRingHomData K hST i).property.1

/-- The full arithmetic local coefficient maps are open embeddings. -/
theorem isOpenEmbedding_numberFieldLevelLocalRingHom (i : NumberFieldLevelFactorIndex K T) :
    IsOpenEmbedding (numberFieldLevelLocalRingHom K hST i) :=
  (numberFieldLevelLocalRingHomData K hST i).property.2.1

/-- The coefficient maps at unchanged places, including all infinite places, are bijections. -/
theorem numberFieldLevelLocalRingHom_bijective (i : NumberFieldLevelFactorIndex K T)
    (hi : numberFieldLevelUnchanged K (S := S) i) :
    Function.Bijective (numberFieldLevelLocalRingHom K hST i) :=
  (numberFieldLevelLocalRingHomData K hST i).property.2.2 hi

omit [NumberField K] in
/-- Only finitely many finite places can give nonbijective coefficient maps. -/
theorem numberFieldLevelUnchanged_cofinite :
    {i : NumberFieldLevelFactorIndex K T | ¬ numberFieldLevelUnchanged K (S := S) i}.Finite := by
  classical
  have hfin : (Set.range (fun v : {v : FinitePlace K // v ∈ T} =>
      (Sum.inr (.inl v) : NumberFieldLevelFactorIndex K T))).Finite := Set.finite_range _
  apply hfin.subset
  rintro (v | (v | v)) hi
  · exact (hi trivial).elim
  · exact ⟨v, rfl⟩
  · exact (hi trivial).elim

/-- All full arithmetic local factors are reduced. -/
theorem numberFieldLevelFactor_isReduced (i : NumberFieldLevelFactorIndex K S) :
    _root_.IsReduced (NumberFieldLevelFactor K S i) := by
  rcases i with v | (v | v)
  · exact inferInstanceAs (_root_.IsReduced (InfiniteCompletion K v))
  · exact inferInstanceAs (_root_.IsReduced (FiniteCompletion K v.1))
  · exact inferInstanceAs (_root_.IsReduced (v.1.adicCompletionIntegers K))

/-- Restrict the target local scalar action along the literal integer inclusion. -/
abbrev numberFieldLevelTargetFactorAlgebra (i : NumberFieldLevelFactorIndex K T) :
    Algebra ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K T i) :=
  ((algebraMap ((T : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K T i)).comp
    (numberFieldSIntegersMap K hST)).toAlgebra

/-- The original local coefficient map respects the original source integer scalars. -/
def numberFieldLevelLocalAlgHom (i : NumberFieldLevelFactorIndex K T) :
    letI := numberFieldLevelTargetFactorAlgebra K hST i
    NumberFieldLevelFactor K S (numberFieldLevelSourceIndex K i) →ₐ[(S : Set (FinitePlace K)).integer K]
      NumberFieldLevelFactor K T i := by
  letI := numberFieldLevelTargetFactorAlgebra K hST i
  refine { numberFieldLevelLocalRingHom K hST i with commutes' := ?_ }
  intro c
  change numberFieldLevelLocalRingHom K hST i
      (numberFieldLevelFactorProjection K S (numberFieldLevelSourceIndex K i)
        (numberFieldAdeleLevelDiagonal K S c)) =
    numberFieldLevelFactorProjection K T i
      (numberFieldAdeleLevelDiagonal K T (numberFieldSIntegersMap K hST c))
  exact (congrArg (fun f : numberFieldAdeleLevel K S →+* NumberFieldLevelFactor K T i =>
      f (numberFieldAdeleLevelDiagonal K S c))
        (numberFieldLevelLocalRingHom_projection K hST i)).trans
    (congrArg (fun f : ((S : Set (FinitePlace K)).integer K) →+* numberFieldAdeleLevel K T =>
      numberFieldLevelFactorProjection K T i (f c))
        (numberFieldAdeleLevelDiagonal_natural K hST))

/-- The actual local point transition with both target base changes. -/
def numberFieldLevelLocalPointMap
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (i : NumberFieldLevelFactorIndex K T) :
    RingPoint (NumberFieldLevelFactor K S (numberFieldLevelSourceIndex K i))
        (ringBaseChange ((S : Set (FinitePlace K)).integer K)
          (NumberFieldLevelFactor K S (numberFieldLevelSourceIndex K i)) X)
        (NumberFieldLevelFactor K S (numberFieldLevelSourceIndex K i)) →
      RingPoint (NumberFieldLevelFactor K T i)
        (ringBaseChange ((T : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K T i)
          (numberFieldLevelModelBaseChange K hST X)) (NumberFieldLevelFactor K T i) := by
  letI := (numberFieldSIntegersMap K hST).toAlgebra
  letI := numberFieldLevelTargetFactorAlgebra K hST i
  letI : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K T i) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact localBaseChangeCoefficientMap _ _ _ _ X (numberFieldLevelLocalAlgHom K hST i)

/-- The local transition is the original arithmetic transition in the original coordinates. -/
theorem numberFieldLevelModelTransition_coordinates
    (X : Over (Spec (CommRingCat.of (((S : Set (FinitePlace K)).integer K)))))
    (p : RingPoint (((S : Set (FinitePlace K)).integer K)) X (numberFieldAdeleLevel K S))
    (i : NumberFieldLevelFactorIndex K T) :
    numberFieldLevelModelPointMap K T (numberFieldLevelModelBaseChange K hST X)
        (numberFieldLevelModelTransition K hST X p) i =
      numberFieldLevelLocalPointMap K hST X i
        (numberFieldLevelModelPointMap K S X p (numberFieldLevelSourceIndex K i)) := by
  let :=  (numberFieldSIntegersMap K hST).toAlgebra
  let :=  numberFieldLevelTargetFactorAlgebra K hST i
  let : IsScalarTower (((S : Set (FinitePlace K)).integer K)) (((T : Set (FinitePlace K)).integer K))
      (NumberFieldLevelFactor K T i) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply ringPoint_doubleBaseChange_ext (((S : Set (FinitePlace K)).integer K))
    (((T : Set (FinitePlace K)).integer K)) (NumberFieldLevelFactor K T i) X
  refine Eq.trans ?_ (localBaseChangeCoefficientMap_left_fst_fst
    (((S : Set (FinitePlace K)).integer K)) (((T : Set (FinitePlace K)).integer K))
    (NumberFieldLevelFactor K S (numberFieldLevelSourceIndex K i))
    (NumberFieldLevelFactor K T i) X (numberFieldLevelLocalAlgHom K hST i)
    (numberFieldLevelModelPointMap K S X p (numberFieldLevelSourceIndex K i))).symm
  have h₁ := congrArg (fun r => r ≫
      pullback.fst X.hom (Spec.algebraMap (((S : Set (FinitePlace K)).integer K))
        (((T : Set (FinitePlace K)).integer K))))
    (numberFieldLevelModelPointMap_left_fst K T
      (numberFieldLevelModelBaseChange K hST X)
      (numberFieldLevelModelTransition K hST X p) i)
  have h₂ := congrArg (fun r =>
      Spec.map (CommRingCat.ofHom (numberFieldLevelFactorProjection K T i)) ≫ r)
    (numberFieldLevelModelTransition_left_fst K hST X p)
  have h₃ := congrArg (fun r =>
      Spec.map (CommRingCat.ofHom (numberFieldLevelLocalRingHom K hST i)) ≫ r)
    (numberFieldLevelModelPointMap_left_fst K S X p
      (numberFieldLevelSourceIndex K i))
  have h₄ :
      Spec.map (CommRingCat.ofHom (numberFieldLevelFactorProjection K T i)) ≫
          (Spec.map (CommRingCat.ofHom (numberFieldAdeleLevelMap K hST)) ≫ p.left) =
        Spec.map (CommRingCat.ofHom (numberFieldLevelLocalRingHom K hST i)) ≫
          (Spec.map (CommRingCat.ofHom (numberFieldLevelFactorProjection K S
            (numberFieldLevelSourceIndex K i))) ≫ p.left) := by
    erw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : numberFieldAdeleLevel K S →+* NumberFieldLevelFactor K T i =>
      Spec.map (CommRingCat.ofHom f) ≫ p.left)
      (numberFieldLevelLocalRingHom_projection K hST i).symm
  exact h₁.trans ((Category.assoc _ _ _).trans (h₂.trans (h₄.trans h₃.symm)))

end NumberField

end Langlands.Global
