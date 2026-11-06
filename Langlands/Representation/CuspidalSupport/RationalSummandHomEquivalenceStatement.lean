import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorStatement
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! Renard VI.4.1, Theorem: the Hom functor of the single-summand compact
induction is an equivalence of the block with right modules over its
endomorphism ring. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- VI.4.1, Theorem: for an irreducible cuspidal π and an irreducible smooth ρ
of the common norm kernel admitting an injective equivariant map into the
restriction of π, the compact induction Π of ρ lies in the actual inertia block,
and `Hom(Π, •)` is an equivalence from the block to unital modules over
`(End Π)ᵐᵒᵖ`, i.e. unital right `End Π`-modules. -/
def RationalSummandHomEquivalenceStatement : Prop :=
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
    haveI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
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
            ∃ hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
                ((Induction.compactInductionFunctor (rationalCommonNormKernel G)).obj
                  (SmoothRep.toRep.obj ρ)),
              (preadditiveCoyonedaObj
                (⟨_, hmem⟩ : RationalInertiaBlock G (rationalInertiaBaseLift G π))).IsEquivalence

end Langlands.CuspidalSupport
