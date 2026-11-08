import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorStatement

/-! Renard VI.4.1, Proposition: compact induction of one irreducible summand of
the restriction to the common norm kernel is a small progenerator of the block. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section BlockProperty

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalSummandSmallProgeneratorPointTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

/-- Membership of an arbitrary actual smooth representation `X` in the actual
inertia block of the lifted `π`, with the lifting, faithful-Hom and coproduct
conditions of `IsRationalNormKernelSmallProgenerator` for the resulting object. -/
def IsRationalInertiaSmallProgenerator
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (X : SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G)) : Prop :=
  ∃ hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π) X,
    let P : RationalInertiaBlock G (rationalInertiaBaseLift G π) := ⟨X, hmem⟩
    (∀ (Y Z : RationalInertiaBlock G (rationalInertiaBaseLift G π)) (q : Y ⟶ Z),
      Epi q → ∀ f : P ⟶ Z, ∃ g : P ⟶ Y, g ≫ q = f) ∧
    (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P).Faithful ∧
    (∀ I : Type (max uF uV),
      HasColimitsOfShape (Discrete I) (RationalInertiaBlock G (rationalInertiaBaseLift G π))) ∧
    (∀ I : Type (max uF uV),
      PreservesColimitsOfShape (Discrete I)
        (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P))

/-- The published predicate for Π₁ is this predicate at Π₁. -/
theorem isRationalNormKernelSmallProgenerator_iff
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    IsRationalNormKernelSmallProgenerator G π ↔
      IsRationalInertiaSmallProgenerator G π (rationalNormKernelCompactInduction G π) :=
  Iff.rfl

/-- Renard's Π = ind_{⁰G}^G(ρ, W): the published compact induction, from the
common norm kernel, of an actual smooth representation ρ of that kernel. -/
abbrev rationalNormKernelSummandInduction
    (ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G)) :
    SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G) :=
  (Induction.compactInductionFunctor (rationalCommonNormKernel G)).obj (SmoothRep.toRep.obj ρ)

end BlockProperty

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- VI.4.1, Proposition: for an irreducible cuspidal π and an irreducible smooth
ρ of the common norm kernel admitting an injective equivariant map into the
restriction of π, the compact induction of ρ is a small progenerator of the
actual inertia block, with cuspidality measured by every proper standard parabolic. -/
def RationalSummandSmallProgeneratorStatement : Prop :=
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
        ∀ ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G),
          ρ.IsIrreducible →
          ∀ j : ρ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π,
            Function.Injective (SmoothRep.hom j) →
            IsRationalInertiaSmallProgenerator G π (rationalNormKernelSummandInduction G ρ)

end Langlands.CuspidalSupport
