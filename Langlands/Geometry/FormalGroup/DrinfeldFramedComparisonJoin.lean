import Langlands.Geometry.FormalGroup.DrinfeldFramedComparisonRefinement
import Langlands.Geometry.FormalGroup.SpecialAtlasComparisonJoin

/-! # Joining and composing specified original framed comparisons -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := κ) π}
variable {X Y Z : DrinfeldFramedAtlas Φ A}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Join the original target comparisons and their actual quotient framing squares. -/
theorem FramingSquare.join (e : X.residueMap = Y.residueMap)
    (f : Y.residueMap = Z.residueMap)
    (c : SpecialAtlas.Comparison X.target.val Y.target.val)
    (d : SpecialAtlas.Comparison Y.target.val Z.target.val)
    (h : c.right.opens = d.left.opens)
    (hc : FramingSquare e c) (hd : FramingSquare f d) :
    FramingSquare (e.trans f) (c.join d h) := by
  unfold FramingSquare
  rw [SpecialAtlas.reductionComparison_join]
  exact ReducedFramingSquare.join e f _ _
    (SpecialAtlas.reductionComparisonJoinCover c d h) hc hd

/-- Product-cover composition preserves the actual original framing condition. -/
theorem FramingSquare.trans (e : X.residueMap = Y.residueMap)
    (f : Y.residueMap = Z.residueMap)
    (c : SpecialAtlas.Comparison X.target.val Y.target.val)
    (d : SpecialAtlas.Comparison Y.target.val Z.target.val)
    (hc : FramingSquare e c) (hd : FramingSquare f d) :
    FramingSquare (e.trans f) (c.trans d) :=
  FramingSquare.join e f _ _ rfl
    (FramingSquare.refine e c hc (BasicAtlas.commonLeft c.left.atlas d.left.atlas))
    (FramingSquare.refine f d hd (BasicAtlas.commonRight c.left.atlas d.left.atlas))

namespace Comparison

/-- Join exactly the specified original target comparisons on equal middle covers. -/
def join (f : Comparison X Y) (g : Comparison Y Z)
    (h : f.targetComparison.right.opens = g.targetComparison.left.opens) : Comparison X Z where
  targetComparison := f.targetComparison.join g.targetComparison h
  residue_eq := f.residue_eq.trans g.residue_eq
  square := FramingSquare.join f.residue_eq g.residue_eq _ _ h f.square g.square

/-- Compose the specified original comparisons on their actual common product cover. -/
def trans (f : Comparison X Y) (g : Comparison Y Z) : Comparison X Z where
  targetComparison := f.targetComparison.trans g.targetComparison
  residue_eq := f.residue_eq.trans g.residue_eq
  square := FramingSquare.trans f.residue_eq g.residue_eq _ _ f.square g.square

@[simp]
theorem join_targetComparison (f : Comparison X Y) (g : Comparison Y Z)
    (h : f.targetComparison.right.opens = g.targetComparison.left.opens) :
    (f.join g h).targetComparison = f.targetComparison.join g.targetComparison h := rfl

@[simp]
theorem join_residue_eq (f : Comparison X Y) (g : Comparison Y Z)
    (h : f.targetComparison.right.opens = g.targetComparison.left.opens) :
    (f.join g h).residue_eq = f.residue_eq.trans g.residue_eq := rfl

@[simp]
theorem trans_targetComparison (f : Comparison X Y) (g : Comparison Y Z) :
    (f.trans g).targetComparison = f.targetComparison.trans g.targetComparison := rfl

@[simp]
theorem trans_residue_eq (f : Comparison X Y) (g : Comparison Y Z) :
    (f.trans g).residue_eq = f.residue_eq.trans g.residue_eq := rfl

/-- The specified joined comparison acts by composition on complete target families. -/
theorem join_targetPointFunctorIso_hom_app (f : Comparison X Y) (g : Comparison Y Z)
    (h : f.targetComparison.right.opens = g.targetComparison.left.opens)
    (B : CommAlgCat.{u} A.obj) (x : X.target.val.Point B) :
    ((f.join g h).targetPointFunctorIso.hom.app B) x =
      (g.targetPointFunctorIso.hom.app B) ((f.targetPointFunctorIso.hom.app B) x) :=
  BasicAtlas.OrderAction.Comparison.onPoints_join _ _ h B x

/-- Product-cover composition acts by composition on every complete target family. -/
theorem trans_targetPointFunctorIso_hom_app (f : Comparison X Y) (g : Comparison Y Z)
    (B : CommAlgCat.{u} A.obj) (x : X.target.val.Point B) :
    ((f.trans g).targetPointFunctorIso.hom.app B) x =
      (g.targetPointFunctorIso.hom.app B) ((f.targetPointFunctorIso.hom.app B) x) :=
  BasicAtlas.OrderAction.Comparison.onPoints_trans _ _ B x

end Comparison

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
