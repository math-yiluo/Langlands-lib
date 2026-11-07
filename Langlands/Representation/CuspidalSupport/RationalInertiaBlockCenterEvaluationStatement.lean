import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorStatement
import Mathlib.CategoryTheory.Center.Preadditive

/-! Renard VI.4.5, Proposition: the center of the inertia block M(G)[π] of an
irreducible cuspidal π is the group algebra ℂ[T/⁰G], the algebra of functions on
Irr(G)[π], and an element of the center acts on each irreducible π ⊗ ω of the
block by its value at π ⊗ ω. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- VI.4.5, Proposition: let π be irreducible cuspidal and T the intersection of
the kernels of the unramified characters ω with π ⊗ ω ≅ π. There is a ring
isomorphism e from the group algebra ℂ[T/H⁰] onto the center of the actual
inertia block of π, such that the image of a scalar c acts on every object of the
block by c, and the image of the class of t ∈ T acts on every unramified twist
π ⊗ ω by ω(t). -/
def RationalInertiaBlockCenterEvaluationStatement : Prop :=
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
        let T : Subgroup (GroupScheme.rationalPoints G) :=
          ⨅ (ω : unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul))
            (_ : Nonempty (rationalUnramifiedTwist G ω π ≅ π)),
            ω.val.toMonoidHom.ker
        ∃ e : MonoidAlgebra ℂ (T ⧸ (rationalCommonNormKernel G).subgroupOf T) ≃+*
            CatCenter (RationalInertiaBlock G (rationalInertiaBaseLift G π)),
          (∀ (c : ℂ) (X : RationalInertiaBlock G (rationalInertiaBaseLift G π)),
            ((e (MonoidAlgebra.single 1 c)).app X).hom = c • 𝟙 X.obj) ∧
          ∀ (t : T)
            (ω : unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul))
            (hω : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
              (rationalUnramifiedTwist G ω (rationalInertiaBaseLift G π))),
            ((e (MonoidAlgebra.of ℂ _ (QuotientGroup.mk t))).app ⟨_, hω⟩).hom =
              ((ω.val (t : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) •
                𝟙 (rationalUnramifiedTwist G ω (rationalInertiaBaseLift G π))

end Langlands.CuspidalSupport
