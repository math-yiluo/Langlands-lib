import Langlands.Global.AdelicLevelModelTransition
import Langlands.AlgebraicGeometry.PointTopology.FilteredRingPointTopology
import Mathlib.CategoryTheory.Filtered.Basic

/-! # Actual arithmetic adelic levels over a fixed model base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Finite sets containing the fixed initial set, ordered by inclusion. -/
abbrev AdelicLevelIndexAbove {ι : Type u} (S : Finset ι) :=
  {T : Finset ι // S ⊆ T}

instance {ι : Type u} (S : Finset ι) : Nonempty (AdelicLevelIndexAbove S) :=
  ⟨⟨S, Finset.Subset.refl S⟩⟩

instance {ι : Type u} (S : Finset ι) : IsFiltered (AdelicLevelIndexAbove S) where
  cocone_objs T U := by
    classical
    exact ⟨⟨T.val ∪ U.val, T.property.trans Finset.subset_union_left⟩,
      homOfLE Finset.subset_union_left, homOfLE Finset.subset_union_right, trivial⟩
  cocone_maps _ _ _ _ := ⟨_, 𝟙 _, Subsingleton.elim _ _⟩

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F))

/-- The original level ring at `T` as an algebra over the fixed outside-`S` integers. -/
def curvePlaceAdeleLevelOver (T : AdelicLevelIndexAbove S) :
    CommAlgCat.{u} (curvePlaceSIntegers k F S) := by
  letI : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F T.val) :=
    ((curvePlaceAdeleLevelDiagonal k F T.val).comp
      (curvePlaceSIntegersMap k F T.property)).toAlgebra
  exact CommAlgCat.of (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F T.val)

/-- The literal coefficient inclusion respects the fixed initial scalar action. -/
def curvePlaceAdeleLevelOverMap {T U : AdelicLevelIndexAbove S} (hTU : T ≤ U) :
    curvePlaceAdeleLevelOver k F S T ⟶ curvePlaceAdeleLevelOver k F S U := by
  let f : curvePlaceAdeleLevelOver k F S T →ₐ[curvePlaceSIntegers k F S]
      curvePlaceAdeleLevelOver k F S U :=
    { toRingHom := curvePlaceAdeleLevelMap k F hTU
      commutes' := fun _ => rfl }
  exact ConcreteCategory.ofHom (C := CommAlgCat (curvePlaceSIntegers k F S)) f

/-- The actual coefficient diagram used by a fixed initial arithmetic model. -/
def curvePlaceAdeleLevelOverDiagram :
    AdelicLevelIndexAbove S ⥤ CommAlgCat.{u} (curvePlaceSIntegers k F S) where
  obj := curvePlaceAdeleLevelOver k F S
  map h := curvePlaceAdeleLevelOverMap k F S (leOfHom h)
  map_id _ := by ext a; rfl
  map_comp _ _ := by ext a; rfl

variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

/-- The canonical comparison with points of the original model pulled back to `T`. -/
def curvePlaceFixedModelPointEquiv (T : AdelicLevelIndexAbove S) :
    RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T) ≃
      RingPoint (curvePlaceSIntegers k F T.val)
        (curvePlaceLevelModelBaseChange k F T.property X) (curvePlaceAdeleLevel k F T.val) := by
  letI : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  letI : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))
  letI : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ringPointBaseChangeEquiv (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) X

/-- The equivalence forgets the base change by the actual first pullback projection. -/
@[simp]
theorem curvePlaceFixedModelPointEquiv_symm_left (T : AdelicLevelIndexAbove S)
    (p : RingPoint (curvePlaceSIntegers k F T.val)
      (curvePlaceLevelModelBaseChange k F T.property X) (curvePlaceAdeleLevel k F T.val)) :
    ((curvePlaceFixedModelPointEquiv k F S X T).symm p).left =
      p.left ≫ pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F T.property))) := by
  let algST : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let algSA : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleLevelOver k F S T) :=
    (curvePlaceAdeleLevelOver k F S T).algebra
  let algTA : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))
  let tower : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algST algTA algSA (fun _ => rfl)
  exact @ringPointBaseChangeEquiv_symm_left (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F T.val) _ _ algST (curvePlaceAdeleLevelOver k F S T)
    (curvePlaceAdeleLevelOver k F S T).commRing algSA algTA tower X p

/-- Transport the existing arithmetic `T`-model topology to the fixed-base points. -/
@[instance_reducible]
def curvePlaceFixedModelStageTopology (T : AdelicLevelIndexAbove S) :
    TopologicalSpace
      (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :=
  TopologicalSpace.induced (curvePlaceFixedModelPointEquiv k F S X T)
    (curvePlaceLevelModelPointTopology k F T.val
      (curvePlaceLevelModelBaseChange k F T.property X))

/-- The stage comparison is a homeomorphism for the transported original topology. -/
def curvePlaceFixedModelPointHomeomorph (T : AdelicLevelIndexAbove S) :
    @Homeomorph
      (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T))
      (RingPoint (curvePlaceSIntegers k F T.val)
        (curvePlaceLevelModelBaseChange k F T.property X) (curvePlaceAdeleLevel k F T.val))
      (curvePlaceFixedModelStageTopology k F S X T)
      (curvePlaceLevelModelPointTopology k F T.val
        (curvePlaceLevelModelBaseChange k F T.property X)) := by
  letI := curvePlaceFixedModelStageTopology k F S X T
  letI := curvePlaceLevelModelPointTopology k F T.val
    (curvePlaceLevelModelBaseChange k F T.property X)
  exact (curvePlaceFixedModelPointEquiv k F S X T).toHomeomorphOfIsInducing ⟨rfl⟩

/-- The actual point diagram now has a single fixed model and literal coefficient maps. -/
def curvePlaceFixedModelPointDiagram : AdelicLevelIndexAbove S ⥤ Type u :=
  curvePlaceAdeleLevelOverDiagram k F S ⋙ ringPointFunctor (curvePlaceSIntegers k F S) X

/-- The actual point quotient with the final topology from the original arithmetic stages. -/
abbrev CurvePlaceFixedModelPointColimit :=
  RingPointColimit (curvePlaceSIntegers k F S) (curvePlaceAdeleLevelOverDiagram k F S) X

@[instance_reducible]
def curvePlaceFixedModelPointColimitTopology :
    TopologicalSpace (CurvePlaceFixedModelPointColimit k F S X) :=
  ringPointColimitTopology (curvePlaceSIntegers k F S)
    (curvePlaceAdeleLevelOverDiagram k F S) X (curvePlaceFixedModelStageTopology k F S X)

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable (S : Finset (FinitePlace K))

/-- The original full number-field level ring at `T` as an algebra over the fixed outside-`S` integers. -/
def numberFieldAdeleLevelOver (T : AdelicLevelIndexAbove S) :
    CommAlgCat.{u} ((S : Set (FinitePlace K)).integer K) := by
  letI : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val) :=
    ((numberFieldAdeleLevelDiagonal K T.val).comp
      (numberFieldSIntegersMap K T.property)).toAlgebra
  exact CommAlgCat.of ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val)

/-- The literal coefficient inclusion respects the fixed initial scalar action. -/
def numberFieldAdeleLevelOverMap {T U : AdelicLevelIndexAbove S} (hTU : T ≤ U) :
    numberFieldAdeleLevelOver K S T ⟶ numberFieldAdeleLevelOver K S U := by
  let f : numberFieldAdeleLevelOver K S T →ₐ[((S : Set (FinitePlace K)).integer K)]
      numberFieldAdeleLevelOver K S U :=
    { toRingHom := numberFieldAdeleLevelMap K hTU
      commutes' := fun _ => rfl }
  exact ConcreteCategory.ofHom (C := CommAlgCat ((S : Set (FinitePlace K)).integer K)) f

/-- The actual coefficient diagram used by a fixed initial arithmetic model. -/
def numberFieldAdeleLevelOverDiagram :
    AdelicLevelIndexAbove S ⥤ CommAlgCat.{u} ((S : Set (FinitePlace K)).integer K) where
  obj := numberFieldAdeleLevelOver K S
  map h := numberFieldAdeleLevelOverMap K S (leOfHom h)
  map_id _ := by ext a; rfl
  map_comp _ _ := by ext a; rfl

variable (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

/-- The canonical comparison with points of the original model pulled back to `T`. -/
def numberFieldFixedModelPointEquiv (T : AdelicLevelIndexAbove S) :
    RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T) ≃
      RingPoint ((T.val : Set (FinitePlace K)).integer K)
        (numberFieldLevelModelBaseChange K T.property X) (numberFieldAdeleLevel K T.val) := by
  letI : Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  letI : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val))
  letI : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ringPointBaseChangeEquiv ((S : Set (FinitePlace K)).integer K)
    ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) X

/-- The equivalence forgets the base change by the actual first pullback projection. -/
@[simp]
theorem numberFieldFixedModelPointEquiv_symm_left (T : AdelicLevelIndexAbove S)
    (p : RingPoint ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldLevelModelBaseChange K T.property X) (numberFieldAdeleLevel K T.val)) :
    ((numberFieldFixedModelPointEquiv K S X T).symm p).left =
      p.left ≫ pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property))) := by
  let algST : Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let algSA : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    (numberFieldAdeleLevelOver K S T).algebra
  let algTA : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val))
  let tower : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K S T) :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algST algTA algSA (fun _ => rfl)
  exact @ringPointBaseChangeEquiv_symm_left ((S : Set (FinitePlace K)).integer K)
    ((T.val : Set (FinitePlace K)).integer K) _ _ algST (numberFieldAdeleLevelOver K S T)
    (numberFieldAdeleLevelOver K S T).commRing algSA algTA tower X p

/-- Transport the existing arithmetic `T`-model topology to the fixed-base points. -/
@[instance_reducible]
def numberFieldFixedModelStageTopology (T : AdelicLevelIndexAbove S) :
    TopologicalSpace
      (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) :=
  TopologicalSpace.induced (numberFieldFixedModelPointEquiv K S X T)
    (numberFieldLevelModelPointTopology K T.val
      (numberFieldLevelModelBaseChange K T.property X))

/-- The stage comparison is a homeomorphism for the transported original topology. -/
def numberFieldFixedModelPointHomeomorph (T : AdelicLevelIndexAbove S) :
    @Homeomorph
      (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T))
      (RingPoint ((T.val : Set (FinitePlace K)).integer K)
        (numberFieldLevelModelBaseChange K T.property X) (numberFieldAdeleLevel K T.val))
      (numberFieldFixedModelStageTopology K S X T)
      (numberFieldLevelModelPointTopology K T.val
        (numberFieldLevelModelBaseChange K T.property X)) := by
  letI := numberFieldFixedModelStageTopology K S X T
  letI := numberFieldLevelModelPointTopology K T.val
    (numberFieldLevelModelBaseChange K T.property X)
  exact (numberFieldFixedModelPointEquiv K S X T).toHomeomorphOfIsInducing ⟨rfl⟩

/-- The actual point diagram now has a single fixed model and literal coefficient maps. -/
def numberFieldFixedModelPointDiagram : AdelicLevelIndexAbove S ⥤ Type u :=
  numberFieldAdeleLevelOverDiagram K S ⋙ ringPointFunctor ((S : Set (FinitePlace K)).integer K) X

/-- The actual point quotient with the final topology from the original arithmetic stages. -/
abbrev NumberFieldFixedModelPointColimit :=
  RingPointColimit ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOverDiagram K S) X

@[instance_reducible]
def numberFieldFixedModelPointColimitTopology :
    TopologicalSpace (NumberFieldFixedModelPointColimit K S X) :=
  ringPointColimitTopology ((S : Set (FinitePlace K)).integer K)
    (numberFieldAdeleLevelOverDiagram K S) X (numberFieldFixedModelStageTopology K S X)

end NumberField

end Langlands.Global
