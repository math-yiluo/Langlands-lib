import Langlands.Representation.CuspidalSupport.RationalUniversalProgenerator
import Langlands.Representation.Aubert.General.SupportCategory
import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.CategoryTheory.Renard.HomFunctors
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! Membership and the small-progenerator target for the actual Π₁. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section BlockProperty

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- Membership and the exact lifting, faithful-Hom and coproduct conditions
for the actual compact induction, in its actual inertia block. -/
def IsRationalNormKernelSmallProgenerator
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) : Prop :=
  ∃ hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      (rationalNormKernelCompactInduction G π),
    let P : RationalInertiaBlock G (rationalInertiaBaseLift G π) :=
      ⟨rationalNormKernelCompactInduction G π, hmem⟩
    (∀ (X Y : RationalInertiaBlock G (rationalInertiaBaseLift G π)) (q : X ⟶ Y),
      Epi q → ∀ f : P ⟶ Y, ∃ g : P ⟶ X, g ≫ q = f) ∧
    (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P).Faithful ∧
    (∀ I : Type (max uF uV),
      HasColimitsOfShape (Discrete I) (RationalInertiaBlock G (rationalInertiaBaseLift G π))) ∧
    (∀ I : Type (max uF uV),
      PreservesColimitsOfShape (Discrete I)
        (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P))

end BlockProperty

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- VI.4.1 for the full-restriction alternative Π₁, with cuspidality measured
by every proper actual standard parabolic. -/
def RationalUniversalSmallProgeneratorStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (GroupScheme.rationalPoints G)]
      [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
      [T2Space (GroupScheme.rationalPoints G)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{uF})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (GroupScheme.rationalPoints G))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      ∀ π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G),
        π.IsIrreducible →
        IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU π →
        IsRationalNormKernelSmallProgenerator G π

end Langlands.CuspidalSupport
