import Langlands.Global.AdelicLevelModelTransitionTopologyStatement
import Langlands.Global.AdelicLevelModelTransitionLocal
import Langlands.Global.AdelicLevelModelTopologyProof
import Langlands.Global.AdelicLocalFactorUnitsProof
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Topology of the actual arithmetic changes of adelic level -/

noncomputable section
universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A coordinate transition inherits continuity and openness from its local maps.
Only finitely many of the local maps may fail to be surjective. -/
theorem coordinateTransition_continuous_open
    {P Q I J : Type u} [TopologicalSpace P] [TopologicalSpace Q]
    (A : I → Type u) (B : J → Type u)
    [∀ i, TopologicalSpace (A i)] [∀ j, TopologicalSpace (B j)]
    (source : P → ∀ i, A i) (target : Q → ∀ j, B j)
    (hsource : IsHomeomorph source) (htarget : IsHomeomorph target)
    (e : J ≃ I) (f : ∀ j, A (e j) → B j) (transition : P → Q)
    (hnatural : ∀ p j, target (transition p) j = f j (source p (e j)))
    (hc : ∀ j, Continuous (f j)) (ho : ∀ j, IsOpenMap (f j))
    (hs : ∀ᶠ j in Filter.cofinite, Function.Surjective (f j)) :
    Continuous transition ∧ IsOpenMap transition := by
  have hprodC : Continuous (fun p : ∀ i, A i => fun j => f j (p (e j))) :=
    continuous_pi fun j => (hc j).comp (continuous_apply (e j))
  have hprodO : IsOpenMap (fun p : ∀ i, A i => fun j => f j (p (e j))) :=
    (IsOpenMap.piMap ho hs).comp (Homeomorph.piCongrLeft e).symm.isOpenMap
  have hn : target ∘ transition =
      (fun p : ∀ i, A i => fun j => f j (p (e j))) ∘ source :=
    funext fun p => funext fun j => hnatural p j
  constructor
  · apply (htarget.homeomorph target).comp_continuous_iff.mp
    change Continuous (target ∘ transition)
    rw [hn]
    exact hprodC.comp hsource.continuous
  · apply (htarget.homeomorph target).comp_isOpenMap_iff.mp
    change IsOpenMap (target ∘ transition)
    rw [hn]
    exact hprodO.comp hsource.isOpenMap

/-- Injective local maps give injectivity of the original coordinate transition. -/
theorem coordinateTransition_injective
    {P Q I J : Type u} (A : I → Type u) (B : J → Type u)
    (source : P → ∀ i, A i) (target : Q → ∀ j, B j)
    (hsource : Function.Injective source) (e : J ≃ I)
    (f : ∀ j, A (e j) → B j) (transition : P → Q)
    (hnatural : ∀ p j, target (transition p) j = f j (source p (e j)))
    (hi : ∀ j, Function.Injective (f j)) : Function.Injective transition := by
  intro p q hpq
  apply hsource
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  apply hi j
  rw [← hnatural p j, ← hnatural q j, hpq]

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable {S T : Finset (AlgebraicCurve.Place k F)} (hST : S ⊆ T)
variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

/-- The local point transition is continuous and, in local finite type, open. -/
theorem curvePlaceLevelLocalPointMap_continuous_open [LocallyOfFiniteType X.hom]
    (i : CurvePlaceLevelFactorIndex k F T) :
    letI := schemePointTopology
      (CurvePlaceLevelFactor k F S (curvePlaceLevelSourceIndex k F i))
      (ringBaseChange (curvePlaceSIntegers k F S)
        (CurvePlaceLevelFactor k F S (curvePlaceLevelSourceIndex k F i)) X)
      (CurvePlaceLevelFactor k F S (curvePlaceLevelSourceIndex k F i))
    letI := schemePointTopology (CurvePlaceLevelFactor k F T i)
      (ringBaseChange (curvePlaceSIntegers k F T) (CurvePlaceLevelFactor k F T i)
        (curvePlaceLevelModelBaseChange k F hST X)) (CurvePlaceLevelFactor k F T i)
    Continuous (curvePlaceLevelLocalPointMap k F hST X i) ∧
      IsOpenMap (curvePlaceLevelLocalPointMap k F hST X i) := by
  let := (curvePlaceSIntegersMap k F hST).toAlgebra
  let := curvePlaceLevelTargetFactorAlgebra k F hST i
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T)
      (CurvePlaceLevelFactor k F T i) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsOpenUnits (CurvePlaceLevelFactor k F S (curvePlaceLevelSourceIndex k F i)) :=
    adelicLocalFactorUnits.1 k F S (curvePlaceLevelSourceIndex k F i)
  let : IsOpenUnits (CurvePlaceLevelFactor k F T i) := adelicLocalFactorUnits.1 k F T i
  have hf := isOpenEmbedding_curvePlaceLevelLocalRingHom k F hST i
  exact ⟨continuous_localBaseChangeCoefficientMap _ _ _ _ X
      (curvePlaceLevelLocalAlgHom k F hST i) hf.continuous,
    isOpenMap_localBaseChangeCoefficientMap _ _ _ _ X
      (curvePlaceLevelLocalAlgHom k F hST i) hf⟩

/-- The local point transition is bijective wherever the coefficient ring is unchanged. -/
theorem curvePlaceLevelLocalPointMap_bijective (i : CurvePlaceLevelFactorIndex k F T)
    (hi : curvePlaceLevelUnchanged k F (S := S) i) :
    Function.Bijective (curvePlaceLevelLocalPointMap k F hST X i) := by
  let := (curvePlaceSIntegersMap k F hST).toAlgebra
  let := curvePlaceLevelTargetFactorAlgebra k F hST i
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T)
      (CurvePlaceLevelFactor k F T i) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact localBaseChangeCoefficientMap_bijective _ _ _ _ X
    (curvePlaceLevelLocalAlgHom k F hST i)
    (curvePlaceLevelLocalRingHom_bijective k F hST i hi)

/-- Reduced actual factors give local injectivity for separated models. -/
theorem curvePlaceLevelLocalPointMap_injective [IsSeparated X.hom]
    (i : CurvePlaceLevelFactorIndex k F T) :
    Function.Injective (curvePlaceLevelLocalPointMap k F hST X i) := by
  let := (curvePlaceSIntegersMap k F hST).toAlgebra
  let := curvePlaceLevelTargetFactorAlgebra k F hST i
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T)
      (CurvePlaceLevelFactor k F T i) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : _root_.IsReduced (CurvePlaceLevelFactor k F S (curvePlaceLevelSourceIndex k F i)) :=
    curvePlaceLevelFactor_isReduced k F (curvePlaceLevelSourceIndex k F i)
  exact localBaseChangeCoefficientMap_injective _ _ _ _ X
    (curvePlaceLevelLocalAlgHom k F hST i)
    (isOpenEmbedding_curvePlaceLevelLocalRingHom k F hST i).injective

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

/-- Finite-type curve models have continuous open transitions in their original topologies. -/
theorem curvePlaceLevelModelTransition_continuous_open [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    letI := curvePlaceLevelModelPointTopology k F S X
    letI := curvePlaceLevelModelPointTopology k F T
      (curvePlaceLevelModelBaseChange k F hST X)
    Continuous (curvePlaceLevelModelTransition k F hST X) ∧
      IsOpenMap (curvePlaceLevelModelTransition k F hST X) ∧
      ∀ [IsSeparated X.hom],
        IsOpenEmbedding (curvePlaceLevelModelTransition k F hST X) := by
  let := curvePlaceLevelModelPointTopology k F S X
  let := curvePlaceLevelModelPointTopology k F T
    (curvePlaceLevelModelBaseChange k F hST X)
  let : ∀ i : CurvePlaceLevelFactorIndex k F S, TopologicalSpace
      (RingPoint (CurvePlaceLevelFactor k F S i)
        (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
        (CurvePlaceLevelFactor k F S i)) :=
    fun i => schemePointTopology (CurvePlaceLevelFactor k F S i)
      (ringBaseChange (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F S i) X)
      (CurvePlaceLevelFactor k F S i)
  let : ∀ i : CurvePlaceLevelFactorIndex k F T, TopologicalSpace
      (RingPoint (CurvePlaceLevelFactor k F T i)
        (ringBaseChange (curvePlaceSIntegers k F T) (CurvePlaceLevelFactor k F T i)
          (curvePlaceLevelModelBaseChange k F hST X)) (CurvePlaceLevelFactor k F T i)) :=
    fun i => schemePointTopology (CurvePlaceLevelFactor k F T i)
      (ringBaseChange (curvePlaceSIntegers k F T) (CurvePlaceLevelFactor k F T i)
        (curvePlaceLevelModelBaseChange k F hST X)) (CurvePlaceLevelFactor k F T i)
  let : LocallyOfFiniteType (curvePlaceLevelModelBaseChange k F hST X).hom := by
    dsimp [curvePlaceLevelModelBaseChange]
    infer_instance
  let : QuasiCompact (curvePlaceLevelModelBaseChange k F hST X).hom := by
    dsimp [curvePlaceLevelModelBaseChange]
    infer_instance
  have hs := curvePlaceLevelModelPointMap_isHomeomorph_of_finiteType k F S X
  have ht := curvePlaceLevelModelPointMap_isHomeomorph_of_finiteType k F T
    (curvePlaceLevelModelBaseChange k F hST X)
  have hco : ∀ᶠ i in Filter.cofinite,
      Function.Surjective (curvePlaceLevelLocalPointMap k F hST X i) := by
    have hu := Filter.eventually_cofinite.mpr
      (curvePlaceLevelUnchanged_cofinite k F (S := S) (T := T))
    filter_upwards [hu] with i hi
    exact (curvePlaceLevelLocalPointMap_bijective k F hST X i hi).surjective
  have h := coordinateTransition_continuous_open _ _
    (curvePlaceLevelModelPointMap k F S X)
    (curvePlaceLevelModelPointMap k F T (curvePlaceLevelModelBaseChange k F hST X))
    hs ht (curvePlaceLevelSourceIndexEquiv k F)
    (curvePlaceLevelLocalPointMap k F hST X) (curvePlaceLevelModelTransition k F hST X)
    (curvePlaceLevelModelTransition_coordinates k F hST X)
    (fun i => (curvePlaceLevelLocalPointMap_continuous_open k F hST X i).1)
    (fun i => (curvePlaceLevelLocalPointMap_continuous_open k F hST X i).2) hco
  refine ⟨h.1, h.2, ?_⟩
  intro hSep
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap h.1
    (coordinateTransition_injective _ _ (curvePlaceLevelModelPointMap k F S X)
      (curvePlaceLevelModelPointMap k F T (curvePlaceLevelModelBaseChange k F hST X))
      hs.injective (curvePlaceLevelSourceIndexEquiv k F)
      (curvePlaceLevelLocalPointMap k F hST X) (curvePlaceLevelModelTransition k F hST X)
      (curvePlaceLevelModelTransition_coordinates k F hST X)
      (curvePlaceLevelLocalPointMap_injective k F hST X)) h.2

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable {S T : Finset (FinitePlace K)} (hST : S ⊆ T)
variable (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

/-- The local point transition is continuous and, in local finite type, open. -/
theorem numberFieldLevelLocalPointMap_continuous_open [LocallyOfFiniteType X.hom]
    (i : NumberFieldLevelFactorIndex K T) :
    letI := schemePointTopology
      (NumberFieldLevelFactor K S (numberFieldLevelSourceIndex K i))
      (ringBaseChange ((S : Set (FinitePlace K)).integer K)
        (NumberFieldLevelFactor K S (numberFieldLevelSourceIndex K i)) X)
      (NumberFieldLevelFactor K S (numberFieldLevelSourceIndex K i))
    letI := schemePointTopology (NumberFieldLevelFactor K T i)
      (ringBaseChange ((T : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K T i)
        (numberFieldLevelModelBaseChange K hST X)) (NumberFieldLevelFactor K T i)
    Continuous (numberFieldLevelLocalPointMap K hST X i) ∧
      IsOpenMap (numberFieldLevelLocalPointMap K hST X i) := by
  let := (numberFieldSIntegersMap K hST).toAlgebra
  let := numberFieldLevelTargetFactorAlgebra K hST i
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K T i) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsOpenUnits (NumberFieldLevelFactor K S (numberFieldLevelSourceIndex K i)) :=
    adelicLocalFactorUnits.2 K S (numberFieldLevelSourceIndex K i)
  let : IsOpenUnits (NumberFieldLevelFactor K T i) := adelicLocalFactorUnits.2 K T i
  have hf := isOpenEmbedding_numberFieldLevelLocalRingHom K hST i
  exact ⟨continuous_localBaseChangeCoefficientMap _ _ _ _ X
      (numberFieldLevelLocalAlgHom K hST i) hf.continuous,
    isOpenMap_localBaseChangeCoefficientMap _ _ _ _ X
      (numberFieldLevelLocalAlgHom K hST i) hf⟩

/-- The local point transition is bijective wherever the coefficient ring is unchanged. -/
theorem numberFieldLevelLocalPointMap_bijective (i : NumberFieldLevelFactorIndex K T)
    (hi : numberFieldLevelUnchanged K (S := S) i) :
    Function.Bijective (numberFieldLevelLocalPointMap K hST X i) := by
  let := (numberFieldSIntegersMap K hST).toAlgebra
  let := numberFieldLevelTargetFactorAlgebra K hST i
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K T i) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact localBaseChangeCoefficientMap_bijective _ _ _ _ X
    (numberFieldLevelLocalAlgHom K hST i)
    (numberFieldLevelLocalRingHom_bijective K hST i hi)

/-- Reduced actual factors give local injectivity for separated models. -/
theorem numberFieldLevelLocalPointMap_injective [IsSeparated X.hom]
    (i : NumberFieldLevelFactorIndex K T) :
    Function.Injective (numberFieldLevelLocalPointMap K hST X i) := by
  let := (numberFieldSIntegersMap K hST).toAlgebra
  let := numberFieldLevelTargetFactorAlgebra K hST i
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K T i) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : _root_.IsReduced (NumberFieldLevelFactor K S (numberFieldLevelSourceIndex K i)) :=
    numberFieldLevelFactor_isReduced K (numberFieldLevelSourceIndex K i)
  exact localBaseChangeCoefficientMap_injective _ _ _ _ X
    (numberFieldLevelLocalAlgHom K hST i)
    (isOpenEmbedding_numberFieldLevelLocalRingHom K hST i).injective

/-- Finite-type full number-field models have continuous open transitions in their original topologies. -/
theorem numberFieldLevelModelTransition_continuous_open [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] :
    letI := numberFieldLevelModelPointTopology K S X
    letI := numberFieldLevelModelPointTopology K T
      (numberFieldLevelModelBaseChange K hST X)
    Continuous (numberFieldLevelModelTransition K hST X) ∧
      IsOpenMap (numberFieldLevelModelTransition K hST X) ∧
      ∀ [IsSeparated X.hom],
        IsOpenEmbedding (numberFieldLevelModelTransition K hST X) := by
  let := numberFieldLevelModelPointTopology K S X
  let := numberFieldLevelModelPointTopology K T
    (numberFieldLevelModelBaseChange K hST X)
  let : ∀ i : NumberFieldLevelFactorIndex K S, TopologicalSpace
      (RingPoint (NumberFieldLevelFactor K S i)
        (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
        (NumberFieldLevelFactor K S i)) :=
    fun i => schemePointTopology (NumberFieldLevelFactor K S i)
      (ringBaseChange ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K S i) X)
      (NumberFieldLevelFactor K S i)
  let : ∀ i : NumberFieldLevelFactorIndex K T, TopologicalSpace
      (RingPoint (NumberFieldLevelFactor K T i)
        (ringBaseChange ((T : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K T i)
          (numberFieldLevelModelBaseChange K hST X)) (NumberFieldLevelFactor K T i)) :=
    fun i => schemePointTopology (NumberFieldLevelFactor K T i)
      (ringBaseChange ((T : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K T i)
        (numberFieldLevelModelBaseChange K hST X)) (NumberFieldLevelFactor K T i)
  let : LocallyOfFiniteType (numberFieldLevelModelBaseChange K hST X).hom := by
    dsimp [numberFieldLevelModelBaseChange]
    infer_instance
  let : QuasiCompact (numberFieldLevelModelBaseChange K hST X).hom := by
    dsimp [numberFieldLevelModelBaseChange]
    infer_instance
  have hs := numberFieldLevelModelPointMap_isHomeomorph_of_finiteType K S X
  have ht := numberFieldLevelModelPointMap_isHomeomorph_of_finiteType K T
    (numberFieldLevelModelBaseChange K hST X)
  have hco : ∀ᶠ i in Filter.cofinite,
      Function.Surjective (numberFieldLevelLocalPointMap K hST X i) := by
    have hu := Filter.eventually_cofinite.mpr
      (numberFieldLevelUnchanged_cofinite K (S := S) (T := T))
    filter_upwards [hu] with i hi
    exact (numberFieldLevelLocalPointMap_bijective K hST X i hi).surjective
  have h := coordinateTransition_continuous_open _ _
    (numberFieldLevelModelPointMap K S X)
    (numberFieldLevelModelPointMap K T (numberFieldLevelModelBaseChange K hST X))
    hs ht (numberFieldLevelSourceIndexEquiv K)
    (numberFieldLevelLocalPointMap K hST X) (numberFieldLevelModelTransition K hST X)
    (numberFieldLevelModelTransition_coordinates K hST X)
    (fun i => (numberFieldLevelLocalPointMap_continuous_open K hST X i).1)
    (fun i => (numberFieldLevelLocalPointMap_continuous_open K hST X i).2) hco
  refine ⟨h.1, h.2, ?_⟩
  intro hSep
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap h.1
    (coordinateTransition_injective _ _ (numberFieldLevelModelPointMap K S X)
      (numberFieldLevelModelPointMap K T (numberFieldLevelModelBaseChange K hST X))
      hs.injective (numberFieldLevelSourceIndexEquiv K)
      (numberFieldLevelLocalPointMap K hST X) (numberFieldLevelModelTransition K hST X)
      (numberFieldLevelModelTransition_coordinates K hST X)
      (numberFieldLevelLocalPointMap_injective K hST X)) h.2

end NumberField

/-- The exact topology theorem for actual model transitions in both characteristics. -/
theorem adelicLevelModelTransitionTopology :
    AdelicLevelModelTransitionTopologyStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ S T hST X _ _
    exact curvePlaceLevelModelTransition_continuous_open k F hST X
  · intro K _ _ S T hST X _ _
    exact numberFieldLevelModelTransition_continuous_open K hST X

end Langlands.Global
