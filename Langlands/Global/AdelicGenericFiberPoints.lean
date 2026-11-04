import Langlands.Global.AdelicFixedModelCocone
import Langlands.Global.CurvePlaceAdeleDiagonal
import Mathlib.Topology.Homeomorph.TransferInstance

/-! # Actual generic-fiber adelic points and the topology from a specified spread -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F))

/-- The actual pullback to the original field along the integer-subring inclusion. -/
def curvePlaceModelGenericFiber
    (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) :
    Over (Spec (CommRingCat.of F)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))).obj X

variable [PerfectField k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [FunctionField k F]

/-- Actual full-adele points of a scheme over the original function field. -/
abbrev CurvePlaceAdelePoints (Y : Over (Spec (CommRingCat.of F))) :=
  RingPoint F Y (CurvePlaceAdeleRing k F)

variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

/-- The pullback adjunction gives the generic-fiber equality in Conrad (3.5.1). -/
def curvePlaceGenericFiberAdelePointEquiv :
    CurvePlaceFixedModelAdelePoints k F S X ≃
      CurvePlaceAdelePoints k F (curvePlaceModelGenericFiber k F S X) := by
  letI : Algebra (curvePlaceSIntegers k F S) F :=
    (curvePlaceSIntegers k F S).subtype.toAlgebra
  letI : Algebra F (curvePlaceAdeleOver k F S) :=
    inferInstanceAs (Algebra F (CurvePlaceAdeleRing k F))
  letI : IsScalarTower (curvePlaceSIntegers k F S) F (curvePlaceAdeleOver k F S) :=
    IsScalarTower.of_algebraMap_eq (curvePlaceAdeleLevelDiagonal_eq k F S)
  exact ringPointBaseChangeEquiv (curvePlaceSIntegers k F S) F
    (curvePlaceAdeleOver k F S) X

/-- The inverse forgets the generic fiber by its first projection. -/
@[simp]
theorem curvePlaceGenericFiberAdelePointEquiv_symm_left
    (p : CurvePlaceAdelePoints k F (curvePlaceModelGenericFiber k F S X)) :
    ((curvePlaceGenericFiberAdelePointEquiv k F S X).symm p).left =
      p.left ≫ pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype)) := by
  let algSF : Algebra (curvePlaceSIntegers k F S) F :=
    (curvePlaceSIntegers k F S).subtype.toAlgebra
  let algSA : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleOver k F S) :=
    (curvePlaceAdeleOver k F S).algebra
  let algFA : Algebra F (curvePlaceAdeleOver k F S) :=
    inferInstanceAs (Algebra F (CurvePlaceAdeleRing k F))
  let tower : IsScalarTower (curvePlaceSIntegers k F S) F (curvePlaceAdeleOver k F S) :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSF algFA algSA
      (curvePlaceAdeleLevelDiagonal_eq k F S)
  exact @ringPointBaseChangeEquiv_symm_left (curvePlaceSIntegers k F S) F
    _ _ algSF (curvePlaceAdeleOver k F S) (curvePlaceAdeleOver k F S).commRing
    algSA algFA tower X p

/-- The generic-fiber comparison preserves the underlying point of the model. -/
@[simp]
theorem curvePlaceGenericFiberAdelePointEquiv_left_fst
    (p : CurvePlaceFixedModelAdelePoints k F S X) :
    (curvePlaceGenericFiberAdelePointEquiv k F S X p).left ≫
      pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype)) = p.left := by
  exact (curvePlaceGenericFiberAdelePointEquiv_symm_left k F S X _).symm.trans
    (congrArg (fun q => q.left)
      ((curvePlaceGenericFiberAdelePointEquiv k F S X).symm_apply_apply p))

/-- The comparison commutes with a model morphism and its actual generic fiber. -/
theorem curvePlaceGenericFiberAdelePointEquiv_natural
    {X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}
    (f : X ⟶ Y) (p : CurvePlaceFixedModelAdelePoints k F S X) :
    curvePlaceGenericFiberAdelePointEquiv k F S Y (p ≫ f) =
      curvePlaceGenericFiberAdelePointEquiv k F S X p ≫
        (Over.pullback
          (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype))).map f := by
  let algSF : Algebra (curvePlaceSIntegers k F S) F :=
    (curvePlaceSIntegers k F S).subtype.toAlgebra
  let algSA : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleOver k F S) :=
    (curvePlaceAdeleOver k F S).algebra
  let algFA : Algebra F (curvePlaceAdeleOver k F S) :=
    inferInstanceAs (Algebra F (CurvePlaceAdeleRing k F))
  let tower := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSF algFA algSA
    (curvePlaceAdeleLevelDiagonal_eq k F S)
  exact @ringPointBaseChangeEquiv_natural (curvePlaceSIntegers k F S) F
    _ _ algSF (curvePlaceAdeleOver k F S) (curvePlaceAdeleOver k F S).commRing
    algSA algFA tower X Y f p

variable (Y : Over (Spec (CommRingCat.of F)))
variable (e : curvePlaceModelGenericFiber k F S X ≅ Y)

/-- A specified generic-fiber isomorphism identifies the model's actual points. -/
def curvePlaceSpreadAdelePointEquiv :
    CurvePlaceFixedModelAdelePoints k F S X ≃ CurvePlaceAdelePoints k F Y :=
  (curvePlaceGenericFiberAdelePointEquiv k F S X).trans
    (Iso.homCongr (Iso.refl _) e)

/-- The adelic topology obtained from this specified model and generic-fiber iso. -/
@[instance_reducible]
def curvePlaceSpreadAdelePointTopology : TopologicalSpace (CurvePlaceAdelePoints k F Y) :=
  @Equiv.topologicalSpace _ _ (curvePlaceFixedModelAdelePointTopology k F S X)
    (curvePlaceSpreadAdelePointEquiv k F S X Y e).symm

/-- This is the homeomorphism defining the topology attached to the spread. -/
def curvePlaceSpreadAdelePointHomeomorph :
    @Homeomorph (CurvePlaceFixedModelAdelePoints k F S X) (CurvePlaceAdelePoints k F Y)
      (curvePlaceFixedModelAdelePointTopology k F S X)
      (curvePlaceSpreadAdelePointTopology k F S X Y e) := by
  letI := curvePlaceFixedModelAdelePointTopology k F S X
  letI := curvePlaceSpreadAdelePointTopology k F S X Y e
  exact ((curvePlaceSpreadAdelePointEquiv k F S X Y e).symm.homeomorph).symm

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable (S : Finset (FinitePlace K))

/-- The actual pullback along the original number-field integer-subring inclusion. -/
def numberFieldModelGenericFiber
    (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))) :
    Over (Spec (CommRingCat.of K)) :=
  (Over.pullback
    (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype))).obj X

/-- Actual full-adele points, including every infinite factor, over the number field. -/
abbrev NumberFieldAdelePoints (Y : Over (Spec (CommRingCat.of K))) :=
  RingPoint K Y (Adeles K)

variable (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

/-- Actual model points and actual points of its generic fiber are equivalent. -/
def numberFieldGenericFiberAdelePointEquiv :
    NumberFieldFixedModelAdelePoints K S X ≃
      NumberFieldAdelePoints K (numberFieldModelGenericFiber K S X) := by
  let algSK : Algebra ((S : Set (FinitePlace K)).integer K) K :=
    ((S : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  let algSA : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    (numberFieldAdeleOver K S).algebra
  let algKA : Algebra K (numberFieldAdeleOver K S) :=
    inferInstanceAs (Algebra K (Adeles K))
  let tower := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSK algKA algSA (fun _ => rfl)
  exact @ringPointBaseChangeEquiv ((S : Set (FinitePlace K)).integer K) K
    _ _ algSK (numberFieldAdeleOver K S) (numberFieldAdeleOver K S).commRing
    algSA algKA tower X

/-- The inverse is postcomposition with the actual first projection. -/
@[simp]
theorem numberFieldGenericFiberAdelePointEquiv_symm_left
    (p : NumberFieldAdelePoints K (numberFieldModelGenericFiber K S X)) :
    ((numberFieldGenericFiberAdelePointEquiv K S X).symm p).left =
      p.left ≫ pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype)) := by
  let algSK : Algebra ((S : Set (FinitePlace K)).integer K) K :=
    ((S : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  let algSA : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    (numberFieldAdeleOver K S).algebra
  let algKA : Algebra K (numberFieldAdeleOver K S) :=
    inferInstanceAs (Algebra K (Adeles K))
  let tower := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSK algKA algSA (fun _ => rfl)
  exact @ringPointBaseChangeEquiv_symm_left ((S : Set (FinitePlace K)).integer K) K
    _ _ algSK (numberFieldAdeleOver K S) (numberFieldAdeleOver K S).commRing
    algSA algKA tower X p

/-- The comparison preserves the underlying point of the original model. -/
@[simp]
theorem numberFieldGenericFiberAdelePointEquiv_left_fst
    (p : NumberFieldFixedModelAdelePoints K S X) :
    (numberFieldGenericFiberAdelePointEquiv K S X p).left ≫
      pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype)) =
      p.left := by
  exact (numberFieldGenericFiberAdelePointEquiv_symm_left K S X _).symm.trans
    (congrArg (fun q => q.left)
      ((numberFieldGenericFiberAdelePointEquiv K S X).symm_apply_apply p))

/-- The comparison is natural for model morphisms and their actual generic fibers. -/
theorem numberFieldGenericFiberAdelePointEquiv_natural
    {X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}
    (f : X ⟶ Y) (p : NumberFieldFixedModelAdelePoints K S X) :
    numberFieldGenericFiberAdelePointEquiv K S Y (p ≫ f) =
      numberFieldGenericFiberAdelePointEquiv K S X p ≫
        (Over.pullback
          (Spec.map (CommRingCat.ofHom
            ((S : Set (FinitePlace K)).integer K).toSubring.subtype))).map f := by
  let algSK : Algebra ((S : Set (FinitePlace K)).integer K) K :=
    ((S : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  let algSA : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    (numberFieldAdeleOver K S).algebra
  let algKA : Algebra K (numberFieldAdeleOver K S) :=
    inferInstanceAs (Algebra K (Adeles K))
  let tower := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSK algKA algSA (fun _ => rfl)
  exact @ringPointBaseChangeEquiv_natural ((S : Set (FinitePlace K)).integer K) K
    _ _ algSK (numberFieldAdeleOver K S) (numberFieldAdeleOver K S).commRing
    algSA algKA tower X Y f p

variable (Y : Over (Spec (CommRingCat.of K)))
variable (e : numberFieldModelGenericFiber K S X ≅ Y)

/-- A specified generic-fiber isomorphism identifies the actual model points. -/
def numberFieldSpreadAdelePointEquiv :
    NumberFieldFixedModelAdelePoints K S X ≃ NumberFieldAdelePoints K Y :=
  (numberFieldGenericFiberAdelePointEquiv K S X).trans (Iso.homCongr (Iso.refl _) e)

/-- The adelic topology obtained from the specified model and generic-fiber iso. -/
@[instance_reducible]
def numberFieldSpreadAdelePointTopology : TopologicalSpace (NumberFieldAdelePoints K Y) :=
  @Equiv.topologicalSpace _ _ (numberFieldFixedModelAdelePointTopology K S X)
    (numberFieldSpreadAdelePointEquiv K S X Y e).symm

/-- This homeomorphism defines the topology attached to the spread. -/
def numberFieldSpreadAdelePointHomeomorph :
    @Homeomorph (NumberFieldFixedModelAdelePoints K S X) (NumberFieldAdelePoints K Y)
      (numberFieldFixedModelAdelePointTopology K S X)
      (numberFieldSpreadAdelePointTopology K S X Y e) := by
  letI := numberFieldFixedModelAdelePointTopology K S X
  letI := numberFieldSpreadAdelePointTopology K S X Y e
  exact ((numberFieldSpreadAdelePointEquiv K S X Y e).symm.homeomorph).symm

end NumberField

end Langlands.Global
