import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorStatement

/-! Renard VI.4.3, Corollary (i): the endomorphism ring of the compact induction
of an irreducible representation of the common norm kernel is a domain. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open GroupScheme Induction

/-- VI.4.3, Corollary (i): for an irreducible smooth ρ of the common norm kernel
H⁰, the ring R = End(ind_{H⁰}^G ρ) is a domain: it is nontrivial and has no zero
divisors. -/
def RationalNormKernelEndDomainStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    haveI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    ∀ ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G),
      ρ.IsIrreducible →
      IsDomain (End ((compactInductionFunctor (rationalCommonNormKernel G)).obj
        (SmoothRep.toRep.obj ρ)))

end Langlands.CuspidalSupport
