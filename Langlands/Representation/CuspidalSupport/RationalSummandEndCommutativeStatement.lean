import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorStatement

/-! Renard VI.4.3, Corollary (ii): the endomorphism ring of the compact induction
of one irreducible summand of the restriction of an irreducible cuspidal π to the
common norm kernel is commutative exactly when that restriction is
multiplicity-free. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme Induction

/-- VI.4.3, Corollary (ii): for an irreducible cuspidal π and an irreducible
smooth ρ of the common norm kernel H⁰ with an injective equivariant map into the
restriction of π, the ring End(ind_{H⁰}^G ρ) is commutative if and only if the
restriction of π to H⁰ is multiplicity-free: every irreducible smooth σ of H⁰
has Hom_{H⁰}(σ, Res π) of dimension at most one. -/
def RationalSummandEndCommutativeStatement : Prop :=
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
            ((∀ α β : End ((compactInductionFunctor (rationalCommonNormKernel G)).obj
                (SmoothRep.toRep.obj ρ)), α * β = β * α) ↔
              ∀ σ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G),
                σ.IsIrreducible →
                Module.rank ℂ
                  (σ ⟶ SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π) ≤ 1)

end Langlands.CuspidalSupport
