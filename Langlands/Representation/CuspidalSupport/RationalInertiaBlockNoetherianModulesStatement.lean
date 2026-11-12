import Langlands.Representation.CuspidalSupport.RationalSummandHomEquivalenceStatement
import Langlands.Representation.CuspidalSupport.RationalSummandEndNoetherianStatement

/-! Renard VI.4.4, the sentence closing the proof of the Corollary: the inertia
block `M(G)[π]` of an irreducible cuspidal `π` is equivalent to the category of
right modules over a (left and right) noetherian `ℂ`-algebra. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- VI.4.4, end of the proof of the Corollary: for an irreducible cuspidal `π`,
in the setting of the published VI.4.1 and VI.4.4 statements, there are a
`ℂ`-algebra `R`, left and right noetherian, and an equivalence of the actual
inertia block `M(G)[π]` (carriers in `Type (max uF uV)`, as in the published
statements) with the category of unital right `R`-modules
(`ModuleCat Rᵐᵒᵖ`) at the same carrier universe. -/
def RationalInertiaBlockNoetherianModulesStatement : Prop :=
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
        ∃ (R : Type (max uF uV)) (_ : Ring R) (_ : Algebra ℂ R),
          IsNoetherianRing R ∧ IsNoetherianRing Rᵐᵒᵖ ∧
            Nonempty (RationalInertiaBlock G (rationalInertiaBaseLift G π) ≌
              ModuleCat.{max uF uV} Rᵐᵒᵖ)

end Langlands.CuspidalSupport
