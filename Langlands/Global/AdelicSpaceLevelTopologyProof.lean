import Langlands.Global.AdelicSpaceLevelFactors
import Langlands.Global.AdelicSpaceLevelTopologyStatement
import Langlands.Global.IntegralFiniteAdeles
import Langlands.Global.FunctionFieldAdelesLocallyCompactProof

/-!
# Topology of adelic-level points of separated algebraic spaces

Proof of Conrad's p.17 claims for the adelic levels: for a separated algebraic space of finite
type over the `S`-integers of a global field, the level points are locally compact and
Hausdorff, and every change of level is an open embedding.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry IsDedekindDomain
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointTopologyFacts
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)
open NumberField (RingOfIntegers)

namespace Langlands.Global

namespace AdelicSpaceLevelTopologyProof

open AdelicSpaceLocalFields AdelicSpaceLevelFactors

section NumberField

variable (K : Type u) [Field K] [NumberField K]

theorem finiteCompletion_locallyCompactSpace (v : FinitePlace K) :
    LocallyCompactSpace (FiniteCompletion K v) :=
  (isCompact_adicCompletionIntegers K v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Valued.isOpen_valuationSubring _).mem_nhds (v.adicCompletionIntegers K).zero_mem)

variable (S : Finset (FinitePlace K))
  {X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

/-- Every factor of a number-field level is Hausdorff and locally compact. -/
theorem numberField_factor (hX : IsSeparated X)
    (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (i : NumberFieldLevelFactorIndex K S) :
    @T2Space _ (fieldValuedPointTopology _ X (numberFieldLevelFieldAlgHom K S i)) ∧
      @LocallyCompactSpace _ (fieldValuedPointTopology _ X (numberFieldLevelFieldAlgHom K S i)) := by
  rcases i with v | v | v
  · let N : NontriviallyNormedField (NumberFieldLevelField K S (.inl v)) := infiniteNormedField K v
    have hK : IsHenselianValuedField (NumberFieldLevelField K S (.inl v)) :=
      infinite_isHenselianValuedField K v
    have hLC : LocallyCompactSpace (NumberFieldLevelField K S (.inl v)) :=
      (inferInstance : LocallyCompactSpace (InfiniteCompletion K v))
    have hb : Function.Bijective (numberFieldLevelFieldAlgHom K S (.inl v)) :=
      Function.bijective_id
    exact ⟨@t2Space_field _ _ X _ N (instAdelicSpaceLevelTopology6 K S (.inl v)) _ _ _
        (numberFieldLevelFieldAlgHom K S (.inl v)) hb hK hX hft,
      @locallyCompactSpace_field _ _ X _ N (instAdelicSpaceLevelTopology6 K S (.inl v)) _ _ _
        (numberFieldLevelFieldAlgHom K S (.inl v)) hb hK hLC hX hft⟩
  · let N : NontriviallyNormedField (NumberFieldLevelField K S (.inr (.inl v))) :=
      normedField (RingOfIntegers K) K v.1
    have hK : IsHenselianValuedField (NumberFieldLevelField K S (.inr (.inl v))) :=
      isHenselianValuedField (RingOfIntegers K) K v.1
    have hLC : LocallyCompactSpace (NumberFieldLevelField K S (.inr (.inl v))) :=
      finiteCompletion_locallyCompactSpace K v.1
    have hb : Function.Bijective (numberFieldLevelFieldAlgHom K S (.inr (.inl v))) :=
      Function.bijective_id
    exact ⟨@t2Space_field _ _ X _ N (instAdelicSpaceLevelTopology6 K S (.inr (.inl v))) _ _ _
        (numberFieldLevelFieldAlgHom K S (.inr (.inl v))) hb hK hX hft,
      @locallyCompactSpace_field _ _ X _ N (instAdelicSpaceLevelTopology6 K S (.inr (.inl v)))
        _ _ _ (numberFieldLevelFieldAlgHom K S (.inr (.inl v))) hb hK hLC hX hft⟩
  · let N : NontriviallyNormedField (NumberFieldLevelField K S (.inr (.inr v))) :=
      normedField (RingOfIntegers K) K v.1
    have hK : IsHenselianValuedField (NumberFieldLevelField K S (.inr (.inr v))) :=
      isHenselianValuedField (RingOfIntegers K) K v.1
    have hLC : LocallyCompactSpace (NumberFieldLevelField K S (.inr (.inr v))) :=
      finiteCompletion_locallyCompactSpace K v.1
    let O : Subring (NumberFieldLevelField K S (.inr (.inr v))) :=
      (v.1.adicCompletionIntegers K).toSubring
    let AO : Algebra ((S : Set (FinitePlace K)).integer K) O :=
      instAdelicLevelModelPoints10 K S (.inr (.inr v))
    let AL : Algebra ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelField K S (.inr (.inr v))) :=
      instAdelicSpaceLevelTopology6 K S (.inr (.inr v))
    have hT : IsScalarTower ((S : Set (FinitePlace K)).integer K) O
        (NumberFieldLevelField K S (.inr (.inr v))) := ⟨fun c o x => by
      change ((algebraMap _ O c * o : O) : NumberFieldLevelField K S (.inr (.inr v))) * x =
        algebraMap _ (NumberFieldLevelField K S (.inr (.inr v))) c * ((o : _) * x)
      rw [Subring.coe_mul, mul_assoc]
      rfl⟩
    exact ⟨@t2Space_integer _ _ X _ N AL O AO hT hK hX hft,
      @locallyCompactSpace_integer _ _ X _ N AL O AO hT hK
        (mem_adicCompletionIntegers_iff (RingOfIntegers K) K v.1)
        (henselianLocalRing (RingOfIntegers K) K v.1) hLC hX hft⟩

/-- The integer factor at a place outside `S` has the data of Corollary 5.7: compact, with
open image in the points over the completion. -/
theorem numberField_integer (hX : IsSeparated X)
    (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (v : {v : FinitePlace K // v ∉ S}) :
    @CompactSpace _ (fieldValuedPointTopology _ X (numberFieldLevelFieldAlgHom K S (.inr (.inr v)))) ∧
      IsOpen[etaleChartTopology (NumberFieldLevelField K S (.inr (.inr v)))
          (baseChange (Spec.algebraMap ((S : Set (FinitePlace K)).integer K)
            (NumberFieldLevelField K S (.inr (.inr v)))) X)]
        (Set.range (fieldValuedPointMap _ X (numberFieldLevelFieldAlgHom K S (.inr (.inr v))))) := by
  let N : NontriviallyNormedField (NumberFieldLevelField K S (.inr (.inr v))) :=
    normedField (RingOfIntegers K) K v.1
  have hLC : LocallyCompactSpace (NumberFieldLevelField K S (.inr (.inr v))) :=
    finiteCompletion_locallyCompactSpace K v.1
  let O : Subring (NumberFieldLevelField K S (.inr (.inr v))) :=
    (v.1.adicCompletionIntegers K).toSubring
  let AO : Algebra ((S : Set (FinitePlace K)).integer K) O :=
    instAdelicLevelModelPoints10 K S (.inr (.inr v))
  let AL : Algebra ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelField K S (.inr (.inr v))) :=
    instAdelicSpaceLevelTopology6 K S (.inr (.inr v))
  have hT : IsScalarTower ((S : Set (FinitePlace K)).integer K) O
      (NumberFieldLevelField K S (.inr (.inr v))) := ⟨fun c o x => by
    change ((algebraMap _ O c * o : O) : NumberFieldLevelField K S (.inr (.inr v))) * x =
      algebraMap _ (NumberFieldLevelField K S (.inr (.inr v))) c * ((o : _) * x)
    rw [Subring.coe_mul, mul_assoc]
    rfl⟩
  exact ⟨@compactSpace_integer _ _ X _ N AL O AO hT
      (mem_adicCompletionIntegers_iff (RingOfIntegers K) K v.1)
      (henselianLocalRing (RingOfIntegers K) K v.1) hLC hX hft,
    @isOpen_range_integer _ _ X _ N AL O AO hT
      (mem_adicCompletionIntegers_iff (RingOfIntegers K) K v.1)
      (henselianLocalRing (RingOfIntegers K) K v.1) hX hft⟩

/-- **Locally compact and Hausdorff**, number fields. -/
theorem numberField_locallyCompact_t2 (hX : IsSeparated X)
    (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X) :
    @LocallyCompactSpace _ (numberFieldSpaceLevelTopology K S X) ∧
      @T2Space _ (numberFieldSpaceLevelTopology K S X) := by
  have hbij := numberFieldSpaceLevelPoints K S X hX hft
  refine ⟨locallyCompactSpace_coordinatePointTopology X _ _ _ _ hbij
      (Set.range Sum.inl ∪ Set.range (fun v => Sum.inr (Sum.inl v)))
      ((Set.finite_range _).union (Set.finite_range _))
      (fun i => (numberField_factor K S hX hft i).2) ?_,
    t2Space_coordinatePointTopology X _ _ _ _ hbij.1 (fun i => (numberField_factor K S hX hft i).1)⟩
  rintro (v | v | v) h
  · exact absurd (Or.inl ⟨v, rfl⟩) h
  · exact absurd (Or.inr ⟨v, rfl⟩) h
  · exact (numberField_integer K S hX hft v).1

end NumberField

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FunctionField k F]
variable (S : Finset (AlgebraicCurve.Place k F))
  {X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

/-- Every factor of a curve-place level is Hausdorff and locally compact. -/
theorem curve_factor (hX : IsSeparated X) (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (i : CurvePlaceLevelFactorIndex k F S) :
    @T2Space _ (fieldValuedPointTopology _ X (curvePlaceLevelFieldAlgHom k F S i)) ∧
      @LocallyCompactSpace _ (fieldValuedPointTopology _ X (curvePlaceLevelFieldAlgHom k F S i)) := by
  rcases i with v | v
  · let N : NontriviallyNormedField (CurvePlaceLevelField k F S (.inl v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    have hK : IsHenselianValuedField (CurvePlaceLevelField k F S (.inl v)) :=
      isHenselianValuedField v.1.toValuationSubring F v.1.heightOneSpectrum
    have hLC : LocallyCompactSpace (CurvePlaceLevelField k F S (.inl v)) :=
      curvePlaceCompletion_locallyCompactSpace k F v.1
    have hb : Function.Bijective (curvePlaceLevelFieldAlgHom k F S (.inl v)) :=
      Function.bijective_id
    exact ⟨@t2Space_field _ _ X _ N (instAdelicSpaceLevelTopology3 k F S (.inl v)) _ _ _
        (curvePlaceLevelFieldAlgHom k F S (.inl v)) hb hK hX hft,
      @locallyCompactSpace_field _ _ X _ N (instAdelicSpaceLevelTopology3 k F S (.inl v)) _ _ _
        (curvePlaceLevelFieldAlgHom k F S (.inl v)) hb hK hLC hX hft⟩
  · let N : NontriviallyNormedField (CurvePlaceLevelField k F S (.inr v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    have hK : IsHenselianValuedField (CurvePlaceLevelField k F S (.inr v)) :=
      isHenselianValuedField v.1.toValuationSubring F v.1.heightOneSpectrum
    have hLC : LocallyCompactSpace (CurvePlaceLevelField k F S (.inr v)) :=
      curvePlaceCompletion_locallyCompactSpace k F v.1
    let O : Subring (CurvePlaceLevelField k F S (.inr v)) :=
      (v.1.heightOneSpectrum.adicCompletionIntegers F).toSubring
    let AO : Algebra (curvePlaceSIntegers k F S) O := instAdelicLevelModelPoints5 k F S (.inr v)
    let AL : Algebra (curvePlaceSIntegers k F S) (CurvePlaceLevelField k F S (.inr v)) :=
      instAdelicSpaceLevelTopology3 k F S (.inr v)
    have hT : IsScalarTower (curvePlaceSIntegers k F S) O (CurvePlaceLevelField k F S (.inr v)) :=
      ⟨fun c o x => by
        change ((algebraMap _ O c * o : O) : CurvePlaceLevelField k F S (.inr v)) * x =
          algebraMap _ (CurvePlaceLevelField k F S (.inr v)) c * ((o : _) * x)
        rw [Subring.coe_mul, mul_assoc]
        rfl⟩
    exact ⟨@t2Space_integer _ _ X _ N AL O AO hT hK hX hft,
      @locallyCompactSpace_integer _ _ X _ N AL O AO hT hK
        (mem_adicCompletionIntegers_iff v.1.toValuationSubring F v.1.heightOneSpectrum)
        (henselianLocalRing v.1.toValuationSubring F v.1.heightOneSpectrum) hLC hX hft⟩

/-- The integer factor at a place outside `S`: compact, with open image. -/
theorem curve_integer (hX : IsSeparated X) (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (v : {v : AlgebraicCurve.Place k F // v ∉ S}) :
    @CompactSpace _ (fieldValuedPointTopology _ X (curvePlaceLevelFieldAlgHom k F S (.inr v))) ∧
      IsOpen[etaleChartTopology (CurvePlaceLevelField k F S (.inr v))
          (baseChange (Spec.algebraMap (curvePlaceSIntegers k F S)
            (CurvePlaceLevelField k F S (.inr v))) X)]
        (Set.range (fieldValuedPointMap _ X (curvePlaceLevelFieldAlgHom k F S (.inr v)))) := by
  let N : NontriviallyNormedField (CurvePlaceLevelField k F S (.inr v)) :=
    normedField v.1.toValuationSubring F v.1.heightOneSpectrum
  have hLC : LocallyCompactSpace (CurvePlaceLevelField k F S (.inr v)) :=
    curvePlaceCompletion_locallyCompactSpace k F v.1
  let O : Subring (CurvePlaceLevelField k F S (.inr v)) :=
    (v.1.heightOneSpectrum.adicCompletionIntegers F).toSubring
  let AO : Algebra (curvePlaceSIntegers k F S) O := instAdelicLevelModelPoints5 k F S (.inr v)
  let AL : Algebra (curvePlaceSIntegers k F S) (CurvePlaceLevelField k F S (.inr v)) :=
    instAdelicSpaceLevelTopology3 k F S (.inr v)
  have hT : IsScalarTower (curvePlaceSIntegers k F S) O (CurvePlaceLevelField k F S (.inr v)) :=
    ⟨fun c o x => by
      change ((algebraMap _ O c * o : O) : CurvePlaceLevelField k F S (.inr v)) * x =
        algebraMap _ (CurvePlaceLevelField k F S (.inr v)) c * ((o : _) * x)
      rw [Subring.coe_mul, mul_assoc]
      rfl⟩
  exact ⟨@compactSpace_integer _ _ X _ N AL O AO hT
      (mem_adicCompletionIntegers_iff v.1.toValuationSubring F v.1.heightOneSpectrum)
      (henselianLocalRing v.1.toValuationSubring F v.1.heightOneSpectrum) hLC hX hft,
    @isOpen_range_integer _ _ X _ N AL O AO hT
      (mem_adicCompletionIntegers_iff v.1.toValuationSubring F v.1.heightOneSpectrum)
      (henselianLocalRing v.1.toValuationSubring F v.1.heightOneSpectrum) hX hft⟩

/-- **Locally compact and Hausdorff**, global function fields. -/
theorem curve_locallyCompact_t2 (hS : S.Nonempty) (hX : IsSeparated X)
    (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X) :
    @LocallyCompactSpace _ (curvePlaceSpaceLevelTopology k F S X) ∧
      @T2Space _ (curvePlaceSpaceLevelTopology k F S X) := by
  have hbij := curvePlaceSpaceLevelPoints k F S hS X hX hft
  refine ⟨locallyCompactSpace_coordinatePointTopology X _ _ _ _ hbij (Set.range Sum.inl)
      (Set.finite_range _) (fun i => (curve_factor k F S hX hft i).2) ?_,
    t2Space_coordinatePointTopology X _ _ _ _ hbij.1 (fun i => (curve_factor k F S hX hft i).1)⟩
  rintro (v | v) h
  · exact absurd ⟨v, rfl⟩ h
  · exact (curve_integer k F S hX hft v).1

end Curve

section NumberFieldTransition

variable (K : Type u) [Field K] [NumberField K] {S T : Finset (FinitePlace K)} [hST : Fact (S ⊆ T)]

/-- The inclusion of `S`-integers in `T`-integers. -/
@[instance_reducible]
def algST : Algebra ((S : Set (FinitePlace K)).integer K) ((T : Set (FinitePlace K)).integer K) :=
  (numberFieldSIntegersMap K hST.out).toAlgebra

attribute [local instance] algST

/-- The `T`-level as an algebra over the `S`-integers. -/
@[instance_reducible]
def algLevel : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T) :=
  ((algebraMap ((T : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T)).comp
    (algebraMap ((S : Set (FinitePlace K)).integer K) ((T : Set (FinitePlace K)).integer K))).toAlgebra

/-- The factors of the `T`-level as algebras over the `S`-integers. -/
@[instance_reducible]
def algFactor (j : NumberFieldLevelFactorIndex K T) :
    Algebra ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K T j) :=
  ((algebraMap ((T : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K T j)).comp
    (algebraMap ((S : Set (FinitePlace K)).integer K) ((T : Set (FinitePlace K)).integer K))).toAlgebra

/-- The fields of the `T`-level as algebras over the `S`-integers. -/
@[instance_reducible]
def algField (j : NumberFieldLevelFactorIndex K T) :
    Algebra ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelField K T j) :=
  ((algebraMap ((T : Set (FinitePlace K)).integer K) (NumberFieldLevelField K T j)).comp
    (algebraMap ((S : Set (FinitePlace K)).integer K) ((T : Set (FinitePlace K)).integer K))).toAlgebra

attribute [local instance] algLevel algFactor algField

theorem towerLevel : IsScalarTower ((S : Set (FinitePlace K)).integer K)
    ((T : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem towerFactor (j : NumberFieldLevelFactorIndex K T) :
    IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K T j) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem towerField (j : NumberFieldLevelFactorIndex K T) :
    IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T : Set (FinitePlace K)).integer K)
      (NumberFieldLevelField K T j) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] towerLevel towerFactor towerField

/-- The level inclusion as a map of algebras over the `S`-integers. -/
def levelAlg : numberFieldAdeleLevel K S →ₐ[(S : Set (FinitePlace K)).integer K]
    numberFieldAdeleLevel K T :=
  { numberFieldAdeleLevelMap K hST.out with commutes' := fun _ => rfl }

variable {K}
variable (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

/-- The change of level is change of coefficients along the level inclusion, followed by the
point identification of the base change. -/
theorem transition_eq :
    numberFieldSpaceLevelTransition K hST.out X = fun x =>
      (baseChangeRingPointsEquiv _ _ (numberFieldAdeleLevel K T) X).symm
        (RingPoints.changeRing (levelAlg K) x) := by
  funext x
  apply (baseChangeRingPointsEquiv _ _ (numberFieldAdeleLevel K T) X).injective
  rw [Equiv.apply_symm_apply]
  change X.pullback _ (X.pullback _ x) = X.pullback _ x
  refine (pullback_comp X _ _ x).symm.trans ?_
  apply BaseChangeComparison.pullback_congr_left
  simp
  rfl

/-- The coordinates of a point of `X` over the `T`-level, viewed over the `S`-integers,
determine the point. -/
theorem coordT_injective (hX : IsSeparated X) :
    Function.Injective (fun (y : RingPoints _ X (numberFieldAdeleLevel K T))
      (j : NumberFieldLevelFactorIndex K T) =>
        RingPoints.changeRing ((numberFieldLevelFactorAlgHom K T j).restrictScalars
          ((S : Set (FinitePlace K)).integer K)) y) := by
  have h := separatedProductPoints_injective _ X hX (NumberFieldLevelFactorIndex K T)
    (NumberFieldLevelFactor K T)
  have he := (AdelicSpaceLevelPointsProof.changeRing_bijective (X := X)
    ((numberFieldLevelFactorAlgEquiv K T).restrictScalars ((S : Set (FinitePlace K)).integer K))).1
  intro y y' hyy
  apply he
  apply h
  funext j
  simp only [ProductPointsDescent.changeRing_changeRing]
  exact congrFun hyy j

/-- Every composite field map of the `T`-level, restricted to the `S`-level, is one of the
`S`-level. -/
theorem matching₁ (j : NumberFieldLevelFactorIndex K T) :
    ∃ i : NumberFieldLevelFactorIndex K S,
      TopologicalSpace.induced (fieldValuedPointMap _ X
          ((numberFieldLevelFieldAlgHom K S i).comp (numberFieldLevelFactorAlgHom K S i)))
          (etaleChartTopology (NumberFieldLevelField K S i)
            (baseChange (Spec.algebraMap _ (NumberFieldLevelField K S i)) X)) =
        TopologicalSpace.induced (fieldValuedPointMap _ X
          ((restrictedFieldMap (NumberFieldLevelFactor K T) (NumberFieldLevelField K T)
            (numberFieldLevelFieldAlgHom K T) (numberFieldLevelFactorAlgHom K T) j).comp
              (levelAlg K)))
          (etaleChartTopology (NumberFieldLevelField K T j)
            (baseChange (Spec.algebraMap _ (NumberFieldLevelField K T j)) X)) := by
  rcases j with v | ⟨v, hvT⟩ | ⟨v, hvT⟩
  · exact ⟨.inl v, rfl⟩
  · by_cases hvS : v ∈ S
    · exact ⟨.inr (.inl ⟨v, hvS⟩), rfl⟩
    · exact ⟨.inr (.inr ⟨v, hvS⟩), rfl⟩
  · exact ⟨.inr (.inr ⟨v, fun h => hvT (hST.out h)⟩), rfl⟩

/-- Every composite field map of the `S`-level is a restricted one of the `T`-level. -/
theorem matching₂ (i : NumberFieldLevelFactorIndex K S) :
    ∃ j : NumberFieldLevelFactorIndex K T,
      TopologicalSpace.induced (fieldValuedPointMap _ X
          ((restrictedFieldMap (NumberFieldLevelFactor K T) (NumberFieldLevelField K T)
            (numberFieldLevelFieldAlgHom K T) (numberFieldLevelFactorAlgHom K T) j).comp
              (levelAlg K)))
          (etaleChartTopology (NumberFieldLevelField K T j)
            (baseChange (Spec.algebraMap _ (NumberFieldLevelField K T j)) X)) =
        TopologicalSpace.induced (fieldValuedPointMap _ X
          ((numberFieldLevelFieldAlgHom K S i).comp (numberFieldLevelFactorAlgHom K S i)))
          (etaleChartTopology (NumberFieldLevelField K S i)
            (baseChange (Spec.algebraMap _ (NumberFieldLevelField K S i)) X)) := by
  rcases i with v | ⟨v, hvS⟩ | ⟨v, hvS⟩
  · exact ⟨.inl v, rfl⟩
  · exact ⟨.inr (.inl ⟨v, hST.out hvS⟩), rfl⟩
  · by_cases hvT : v ∈ T
    · exact ⟨.inr (.inl ⟨v, hvT⟩), rfl⟩
    · exact ⟨.inr (.inr ⟨v, hvT⟩), rfl⟩

/-- **The image of a level in a larger level is open**: it consists of the points whose
coordinates at the new places come from the completed integers. -/
theorem numberField_isOpen_range (hX : IsSeparated X)
    (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X) :
    IsOpen[restrictedTopology X (NumberFieldLevelFactor K T) (NumberFieldLevelField K T)
        (numberFieldLevelFieldAlgHom K T) (numberFieldLevelFactorAlgHom K T)]
      (Set.range (RingPoints.changeRing (X := X) (levelAlg K))) := by
  classical
  let Ψ := fun j => fieldValuedPointMap _ X (restrictedFieldMap (NumberFieldLevelFactor K T)
    (NumberFieldLevelField K T) (numberFieldLevelFieldAlgHom K T) (numberFieldLevelFactorAlgHom K T) j)
  have hrange : Set.range (RingPoints.changeRing (X := X) (levelAlg K)) =
      ⋂ w : {w : {w : FinitePlace K // w ∈ T} // w.1 ∉ S}, Ψ (.inr (.inl w.1)) ⁻¹'
        Set.range (fieldValuedPointMap _ X
          (numberFieldLevelFieldAlgHom K S (.inr (.inr ⟨w.1.1, w.2⟩)))) := by
    ext y
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨p, rfl⟩ w
      refine ⟨RingPoints.changeRing (numberFieldLevelFactorAlgHom K S (.inr (.inr ⟨w.1.1, w.2⟩))) p, ?_⟩
      exact (fieldValuedPointMap_comp X _ _ p).symm.trans
        (fieldValuedPointMap_comp X (restrictedFieldMap (NumberFieldLevelFactor K T)
          (NumberFieldLevelField K T) (numberFieldLevelFieldAlgHom K T)
          (numberFieldLevelFactorAlgHom K T) (.inr (.inl w.1))) (levelAlg K) p)
    · intro hy
      choose z hz using hy
      let πT : ∀ j : NumberFieldLevelFactorIndex K T,
          numberFieldAdeleLevel K T →ₐ[(S : Set (FinitePlace K)).integer K]
            NumberFieldLevelFactor K T j := fun j =>
        (numberFieldLevelFactorAlgHom K T j).restrictScalars ((S : Set (FinitePlace K)).integer K)
      let x : ∀ i : NumberFieldLevelFactorIndex K S,
          RingPoints ((S : Set (FinitePlace K)).integer K) X (NumberFieldLevelFactor K S i) :=
        fun i => match i with
        | .inl v => RingPoints.changeRing (πT (.inl v)) y
        | .inr (.inl v) => RingPoints.changeRing (πT (.inr (.inl ⟨v.1, hST.out v.2⟩))) y
        | .inr (.inr v) => if hvT : v.1 ∈ T then z ⟨⟨v.1, hvT⟩, v.2⟩ else
            RingPoints.changeRing (πT (.inr (.inr ⟨v.1, hvT⟩))) y
      obtain ⟨p, hp⟩ := (numberFieldSpaceLevelPoints K S X hX hft).2 x
      refine ⟨p, coordT_injective X hX (funext fun j => ?_)⟩
      change RingPoints.changeRing (πT j) (RingPoints.changeRing (levelAlg K) p) =
        RingPoints.changeRing (πT j) y
      rw [ProductPointsDescent.changeRing_changeRing]
      rcases j with v | ⟨v, hvT⟩ | ⟨v, hvT⟩
      · exact congrFun hp (.inl v)
      · by_cases hvS : v ∈ S
        · exact congrFun hp (.inr (.inl ⟨v, hvS⟩))
        · have h2 : x (.inr (.inr ⟨v, hvS⟩)) = z ⟨⟨v, hvT⟩, hvS⟩ := dite_eq_left hvT
          have h3 : RingPoints.changeRing (numberFieldLevelFactorAlgHom K S (.inr (.inr ⟨v, hvS⟩))) p =
              z ⟨⟨v, hvT⟩, hvS⟩ := (congrFun hp (.inr (.inr ⟨v, hvS⟩))).trans h2
          have hb : Function.Bijective (fieldValuedPointMap _ X
              ((numberFieldLevelFieldAlgHom K T (.inr (.inl ⟨v, hvT⟩))).restrictScalars
                ((S : Set (FinitePlace K)).integer K))) :=
            fieldValuedPointMap_bijective X _ Function.bijective_id
          apply hb.1
          have h4 := hz ⟨⟨v, hvT⟩, hvS⟩
          rw [← h3] at h4
          let φT := (numberFieldLevelFieldAlgHom K T (.inr (.inl ⟨v, hvT⟩))).restrictScalars
            ((S : Set (FinitePlace K)).integer K)
          have h5 : fieldValuedPointMap _ X (φT.comp ((πT (.inr (.inl ⟨v, hvT⟩))).comp (levelAlg K))) p =
              fieldValuedPointMap _ X (φT.comp (πT (.inr (.inl ⟨v, hvT⟩)))) y :=
            (fieldValuedPointMap_comp X (numberFieldLevelFieldAlgHom K S (.inr (.inr ⟨v, hvS⟩)))
              (numberFieldLevelFactorAlgHom K S (.inr (.inr ⟨v, hvS⟩))) p).trans h4
          exact (fieldValuedPointMap_comp X φT ((πT (.inr (.inl ⟨v, hvT⟩))).comp (levelAlg K)) p).symm.trans
            (h5.trans (fieldValuedPointMap_comp X φT (πT (.inr (.inl ⟨v, hvT⟩))) y))
      · have h2 : x (.inr (.inr ⟨v, fun h => hvT (hST.out h)⟩)) =
            RingPoints.changeRing (πT (.inr (.inr ⟨v, hvT⟩))) y := dite_eq_right hvT
        exact (congrFun hp (.inr (.inr ⟨v, fun h => hvT (hST.out h)⟩))).trans h2
  rw [hrange]
  let : TopologicalSpace (RingPoints ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevel K T)) :=
    restrictedTopology X (NumberFieldLevelFactor K T) (NumberFieldLevelField K T)
      (numberFieldLevelFieldAlgHom K T) (numberFieldLevelFactorAlgHom K T)
  refine isOpen_iInter_of_finite fun w => ?_
  exact @Continuous.isOpen_preimage _ _ _ (etaleChartTopology _ _) _
    (continuous_restrictedFieldMap X (NumberFieldLevelFactor K T) (NumberFieldLevelField K T)
      (numberFieldLevelFieldAlgHom K T) (numberFieldLevelFactorAlgHom K T) (.inr (.inl w.1)))
    _ (numberField_integer K S hX hft ⟨w.1.1, w.2⟩).2

/-- **Change of level is an open embedding**, number fields. -/
theorem numberField_transition (hX : IsSeparated X)
    (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X) :
    @IsOpenEmbedding _ _ (numberFieldSpaceLevelTopology K S X)
      (numberFieldSpaceLevelTopology K T (numberFieldSpaceLevelBaseChange K hST.out X))
      (numberFieldSpaceLevelTransition K hST.out X) := by
  rw [transition_eq]
  have h0 : @T0Space _ (numberFieldSpaceLevelTopology K S X) := by
    let := numberFieldSpaceLevelTopology K S X
    have := (numberField_locallyCompact_t2 K S hX hft).2
    infer_instance
  exact isOpenEmbedding_levelChange X _ _ _ _ _ _ _ _ (levelAlg K) h0 (matching₁ X) (matching₂ X)
    (numberField_isOpen_range X hX hft)

end NumberFieldTransition

section CurveTransition

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  {S T : Finset (AlgebraicCurve.Place k F)} [hST : Fact (S ⊆ T)]

/-- The inclusion of `S`-integers in `T`-integers. -/
@[instance_reducible]
def curveAlgST : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T) :=
  (curvePlaceSIntegersMap k F hST.out).toAlgebra

attribute [local instance] curveAlgST

/-- The `T`-level as an algebra over the `S`-integers. -/
@[instance_reducible]
def curveAlgLevel : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F T) :=
  ((algebraMap (curvePlaceSIntegers k F T) (curvePlaceAdeleLevel k F T)).comp
    (algebraMap (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T))).toAlgebra

/-- The factors of the `T`-level as algebras over the `S`-integers. -/
@[instance_reducible]
def curveAlgFactor (j : CurvePlaceLevelFactorIndex k F T) :
    Algebra (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F T j) :=
  ((algebraMap (curvePlaceSIntegers k F T) (CurvePlaceLevelFactor k F T j)).comp
    (algebraMap (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T))).toAlgebra

/-- The fields of the `T`-level as algebras over the `S`-integers. -/
@[instance_reducible]
def curveAlgField (j : CurvePlaceLevelFactorIndex k F T) :
    Algebra (curvePlaceSIntegers k F S) (CurvePlaceLevelField k F T j) :=
  ((algebraMap (curvePlaceSIntegers k F T) (CurvePlaceLevelField k F T j)).comp
    (algebraMap (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T))).toAlgebra

attribute [local instance] curveAlgLevel curveAlgFactor curveAlgField

theorem curveTowerLevel : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T)
    (curvePlaceAdeleLevel k F T) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem curveTowerFactor (j : CurvePlaceLevelFactorIndex k F T) :
    IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T)
      (CurvePlaceLevelFactor k F T j) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem curveTowerField (j : CurvePlaceLevelFactorIndex k F T) :
    IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T)
      (CurvePlaceLevelField k F T j) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] curveTowerLevel curveTowerFactor curveTowerField

/-- The level inclusion as a map of algebras over the `S`-integers. -/
def curveLevelAlg : curvePlaceAdeleLevel k F S →ₐ[curvePlaceSIntegers k F S]
    curvePlaceAdeleLevel k F T :=
  { curvePlaceAdeleLevelMap k F hST.out with commutes' := fun _ => rfl }

variable {k F}
variable (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

/-- The change of level is change of coefficients along the level inclusion, followed by the
point identification of the base change. -/
theorem curve_transition_eq :
    curvePlaceSpaceLevelTransition k F hST.out X = fun x =>
      (baseChangeRingPointsEquiv _ _ (curvePlaceAdeleLevel k F T) X).symm
        (RingPoints.changeRing (curveLevelAlg k F) x) := by
  funext x
  apply (baseChangeRingPointsEquiv _ _ (curvePlaceAdeleLevel k F T) X).injective
  rw [Equiv.apply_symm_apply]
  change X.pullback _ (X.pullback _ x) = X.pullback _ x
  refine (pullback_comp X _ _ x).symm.trans ?_
  apply BaseChangeComparison.pullback_congr_left
  simp
  rfl

/-- The coordinates of a point of `X` over the `T`-level, viewed over the `S`-integers,
determine the point. -/
theorem curve_coordT_injective (hX : IsSeparated X) :
    Function.Injective (fun (y : RingPoints _ X (curvePlaceAdeleLevel k F T))
      (j : CurvePlaceLevelFactorIndex k F T) =>
        RingPoints.changeRing ((curvePlaceLevelFactorAlgHom k F T j).restrictScalars
          (curvePlaceSIntegers k F S)) y) := by
  have h := separatedProductPoints_injective _ X hX (CurvePlaceLevelFactorIndex k F T)
    (CurvePlaceLevelFactor k F T)
  have he := (AdelicSpaceLevelPointsProof.changeRing_bijective (X := X)
    ((curvePlaceLevelFactorAlgEquiv k F T).restrictScalars (curvePlaceSIntegers k F S))).1
  intro y y' hyy
  apply he
  apply h
  funext j
  simp only [ProductPointsDescent.changeRing_changeRing]
  exact congrFun hyy j

theorem curve_matching₁ (j : CurvePlaceLevelFactorIndex k F T) :
    ∃ i : CurvePlaceLevelFactorIndex k F S,
      TopologicalSpace.induced (fieldValuedPointMap _ X
          ((curvePlaceLevelFieldAlgHom k F S i).comp (curvePlaceLevelFactorAlgHom k F S i)))
          (etaleChartTopology (CurvePlaceLevelField k F S i)
            (baseChange (Spec.algebraMap _ (CurvePlaceLevelField k F S i)) X)) =
        TopologicalSpace.induced (fieldValuedPointMap _ X
          ((restrictedFieldMap (CurvePlaceLevelFactor k F T) (CurvePlaceLevelField k F T)
            (curvePlaceLevelFieldAlgHom k F T) (curvePlaceLevelFactorAlgHom k F T) j).comp
              (curveLevelAlg k F)))
          (etaleChartTopology (CurvePlaceLevelField k F T j)
            (baseChange (Spec.algebraMap _ (CurvePlaceLevelField k F T j)) X)) := by
  rcases j with ⟨v, hvT⟩ | ⟨v, hvT⟩
  · by_cases hvS : v ∈ S
    · exact ⟨.inl ⟨v, hvS⟩, rfl⟩
    · exact ⟨.inr ⟨v, hvS⟩, rfl⟩
  · exact ⟨.inr ⟨v, fun h => hvT (hST.out h)⟩, rfl⟩

theorem curve_matching₂ (i : CurvePlaceLevelFactorIndex k F S) :
    ∃ j : CurvePlaceLevelFactorIndex k F T,
      TopologicalSpace.induced (fieldValuedPointMap _ X
          ((restrictedFieldMap (CurvePlaceLevelFactor k F T) (CurvePlaceLevelField k F T)
            (curvePlaceLevelFieldAlgHom k F T) (curvePlaceLevelFactorAlgHom k F T) j).comp
              (curveLevelAlg k F)))
          (etaleChartTopology (CurvePlaceLevelField k F T j)
            (baseChange (Spec.algebraMap _ (CurvePlaceLevelField k F T j)) X)) =
        TopologicalSpace.induced (fieldValuedPointMap _ X
          ((curvePlaceLevelFieldAlgHom k F S i).comp (curvePlaceLevelFactorAlgHom k F S i)))
          (etaleChartTopology (CurvePlaceLevelField k F S i)
            (baseChange (Spec.algebraMap _ (CurvePlaceLevelField k F S i)) X)) := by
  rcases i with ⟨v, hvS⟩ | ⟨v, hvS⟩
  · exact ⟨.inl ⟨v, hST.out hvS⟩, rfl⟩
  · by_cases hvT : v ∈ T
    · exact ⟨.inl ⟨v, hvT⟩, rfl⟩
    · exact ⟨.inr ⟨v, hvT⟩, rfl⟩

/-- **The image of a level in a larger level is open**, global function fields. -/
theorem curve_isOpen_range [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FunctionField k F] (hS : S.Nonempty) (hX : IsSeparated X)
    (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X) :
    IsOpen[restrictedTopology X (CurvePlaceLevelFactor k F T) (CurvePlaceLevelField k F T)
        (curvePlaceLevelFieldAlgHom k F T) (curvePlaceLevelFactorAlgHom k F T)]
      (Set.range (RingPoints.changeRing (X := X) (curveLevelAlg k F))) := by
  classical
  let Ψ := fun j => fieldValuedPointMap _ X (restrictedFieldMap (CurvePlaceLevelFactor k F T)
    (CurvePlaceLevelField k F T) (curvePlaceLevelFieldAlgHom k F T) (curvePlaceLevelFactorAlgHom k F T) j)
  have hrange : Set.range (RingPoints.changeRing (X := X) (curveLevelAlg k F)) =
      ⋂ w : {w : {w : AlgebraicCurve.Place k F // w ∈ T} // w.1 ∉ S}, Ψ (.inl w.1) ⁻¹'
        Set.range (fieldValuedPointMap _ X (curvePlaceLevelFieldAlgHom k F S (.inr ⟨w.1.1, w.2⟩))) := by
    ext y
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨p, rfl⟩ w
      refine ⟨RingPoints.changeRing (curvePlaceLevelFactorAlgHom k F S (.inr ⟨w.1.1, w.2⟩)) p, ?_⟩
      exact (fieldValuedPointMap_comp X _ _ p).symm.trans
        (fieldValuedPointMap_comp X (restrictedFieldMap (CurvePlaceLevelFactor k F T)
          (CurvePlaceLevelField k F T) (curvePlaceLevelFieldAlgHom k F T)
          (curvePlaceLevelFactorAlgHom k F T) (.inl w.1)) (curveLevelAlg k F) p)
    · intro hy
      choose z hz using hy
      let πT : ∀ j : CurvePlaceLevelFactorIndex k F T,
          curvePlaceAdeleLevel k F T →ₐ[curvePlaceSIntegers k F S]
            CurvePlaceLevelFactor k F T j := fun j =>
        (curvePlaceLevelFactorAlgHom k F T j).restrictScalars (curvePlaceSIntegers k F S)
      let x : ∀ i : CurvePlaceLevelFactorIndex k F S,
          RingPoints (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F S i) :=
        fun i => match i with
        | .inl v => RingPoints.changeRing (πT (.inl ⟨v.1, hST.out v.2⟩)) y
        | .inr v => if hvT : v.1 ∈ T then z ⟨⟨v.1, hvT⟩, v.2⟩ else
            RingPoints.changeRing (πT (.inr ⟨v.1, hvT⟩)) y
      obtain ⟨p, hp⟩ := (curvePlaceSpaceLevelPoints k F S hS X hX hft).2 x
      refine ⟨p, curve_coordT_injective X hX (funext fun j => ?_)⟩
      change RingPoints.changeRing (πT j) (RingPoints.changeRing (curveLevelAlg k F) p) =
        RingPoints.changeRing (πT j) y
      rw [ProductPointsDescent.changeRing_changeRing]
      rcases j with ⟨v, hvT⟩ | ⟨v, hvT⟩
      · by_cases hvS : v ∈ S
        · exact congrFun hp (.inl ⟨v, hvS⟩)
        · have h2 : x (.inr ⟨v, hvS⟩) = z ⟨⟨v, hvT⟩, hvS⟩ := dite_eq_left hvT
          have h3 : RingPoints.changeRing (curvePlaceLevelFactorAlgHom k F S (.inr ⟨v, hvS⟩)) p =
              z ⟨⟨v, hvT⟩, hvS⟩ := (congrFun hp (.inr ⟨v, hvS⟩)).trans h2
          have hb : Function.Bijective (fieldValuedPointMap _ X
              ((curvePlaceLevelFieldAlgHom k F T (.inl ⟨v, hvT⟩)).restrictScalars
                (curvePlaceSIntegers k F S))) :=
            fieldValuedPointMap_bijective X _ Function.bijective_id
          apply hb.1
          have h4 := hz ⟨⟨v, hvT⟩, hvS⟩
          rw [← h3] at h4
          let φT := (curvePlaceLevelFieldAlgHom k F T (.inl ⟨v, hvT⟩)).restrictScalars
            (curvePlaceSIntegers k F S)
          have h5 : fieldValuedPointMap _ X (φT.comp ((πT (.inl ⟨v, hvT⟩)).comp (curveLevelAlg k F))) p =
              fieldValuedPointMap _ X (φT.comp (πT (.inl ⟨v, hvT⟩))) y :=
            (fieldValuedPointMap_comp X (curvePlaceLevelFieldAlgHom k F S (.inr ⟨v, hvS⟩))
              (curvePlaceLevelFactorAlgHom k F S (.inr ⟨v, hvS⟩)) p).trans h4
          exact (fieldValuedPointMap_comp X φT ((πT (.inl ⟨v, hvT⟩)).comp (curveLevelAlg k F)) p).symm.trans
            (h5.trans (fieldValuedPointMap_comp X φT (πT (.inl ⟨v, hvT⟩)) y))
      · have h2 : x (.inr ⟨v, fun h => hvT (hST.out h)⟩) =
            RingPoints.changeRing (πT (.inr ⟨v, hvT⟩)) y := dite_eq_right hvT
        exact (congrFun hp (.inr ⟨v, fun h => hvT (hST.out h)⟩)).trans h2
  rw [hrange]
  let : TopologicalSpace (RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F T)) :=
    restrictedTopology X (CurvePlaceLevelFactor k F T) (CurvePlaceLevelField k F T)
      (curvePlaceLevelFieldAlgHom k F T) (curvePlaceLevelFactorAlgHom k F T)
  refine isOpen_iInter_of_finite fun w => ?_
  exact @Continuous.isOpen_preimage _ _ _ (etaleChartTopology _ _) _
    (continuous_restrictedFieldMap X (CurvePlaceLevelFactor k F T) (CurvePlaceLevelField k F T)
      (curvePlaceLevelFieldAlgHom k F T) (curvePlaceLevelFactorAlgHom k F T) (.inl w.1))
    _ (curve_integer k F S hX hft ⟨w.1.1, w.2⟩).2

/-- **Change of level is an open embedding**, global function fields. -/
theorem curve_transition [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FunctionField k F] (hS : S.Nonempty) (hX : IsSeparated X)
    (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X) :
    @IsOpenEmbedding _ _ (curvePlaceSpaceLevelTopology k F S X)
      (curvePlaceSpaceLevelTopology k F T (curvePlaceSpaceLevelBaseChange k F hST.out X))
      (curvePlaceSpaceLevelTransition k F hST.out X) := by
  rw [curve_transition_eq]
  have h0 : @T0Space _ (curvePlaceSpaceLevelTopology k F S X) := by
    let := curvePlaceSpaceLevelTopology k F S X
    have := (curve_locallyCompact_t2 k F S hS hX hft).2
    infer_instance
  exact isOpenEmbedding_levelChange X _ _ _ _ _ _ _ _ (curveLevelAlg k F) h0 (curve_matching₁ X)
    (curve_matching₂ X) (curve_isOpen_range X hS hX hft)

end CurveTransition

end AdelicSpaceLevelTopologyProof

open AdelicSpaceLevelTopologyProof in
/-- **Conrad's p.17 claims for number-field levels.** -/
theorem numberFieldSpaceLevelTopology_proof : NumberFieldSpaceLevelTopologyStatement.{u} := by
  intro K _ _ S X hX hft
  refine ⟨numberField_locallyCompact_t2 K S hX hft, fun T hST => ?_⟩
  have : Fact (S ⊆ T) := ⟨hST⟩
  exact numberField_transition X hX hft

open AdelicSpaceLevelTopologyProof in
/-- **Conrad's p.17 claims for function-field levels.** -/
theorem curvePlaceSpaceLevelTopology_proof : CurvePlaceSpaceLevelTopologyStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S hS X hX hft
  refine ⟨curve_locallyCompact_t2 k F S hS hX hft, fun T hST => ?_⟩
  have : Fact (S ⊆ T) := ⟨hST⟩
  exact curve_transition X hS hX hft

/-- **Conrad's p.17 topological claims for adelic levels** (printed p.17), for global fields
of both characteristics. -/
theorem adelicSpaceLevelTopology : AdelicSpaceLevelTopologyStatement.{u} :=
  ⟨numberFieldSpaceLevelTopology_proof, curvePlaceSpaceLevelTopology_proof⟩

end Langlands.Global
