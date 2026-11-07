import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorStatement
import Mathlib.CategoryTheory.Center.Preadditive

/-! Renard VI.4.5: the equivalence of VI.4.1 identifies the center of the
inertia block M(G)[π] with the center of the endomorphism ring of the compact
induction Π of one irreducible summand ρ of the restriction of π to the common
norm kernel; the identification is evaluation at Π. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- VI.4.5: for an irreducible cuspidal π and an irreducible smooth ρ of the
common norm kernel admitting an injective equivariant map into the restriction
of π, the compact induction Π of ρ lies in the actual inertia block, and the
component at Π, z ↦ z_Π, is a ring isomorphism from the center of the block
onto the center of `End Π`. -/
def RationalSummandBlockCenterStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
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
      (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
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
            let I := (Induction.compactInductionFunctor (rationalCommonNormKernel G)).obj
              (SmoothRep.toRep.obj ρ)
            ∃ hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π) I,
              ∃ e : CatCenter (RationalInertiaBlock G (rationalInertiaBaseLift G π)) ≃+*
                  Subalgebra.center ℂ (End I),
                ∀ z : CatCenter (RationalInertiaBlock G (rationalInertiaBaseLift G π)),
                  (e z : End I) = (z.app ⟨I, hmem⟩).hom

end Langlands.CuspidalSupport
