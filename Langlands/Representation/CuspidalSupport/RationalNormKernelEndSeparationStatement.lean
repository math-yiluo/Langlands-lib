import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorStatement

/-! Renard VI.4.3, Lemma: the endomorphism ring of the compact induction of an
irreducible representation of the common norm kernel is separated by its simple
right modules. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open GroupScheme Induction

/-- VI.4.3, Lemma: for an irreducible smooth ρ of the common norm kernel H⁰ and
R = End(ind_{H⁰}^G ρ), an element of R acting as zero on every simple right
R-module is zero; that is, R → ∏_M End_ℂ(M) over the simple right R-modules M
is injective. Right R-modules are modules over Rᵐᵒᵖ. -/
def RationalNormKernelEndSeparationStatement : Prop :=
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
      let I := (compactInductionFunctor (rationalCommonNormKernel G)).obj (SmoothRep.toRep.obj ρ)
      ∀ α : End I,
        (∀ (M : Type (max uF uV)) [AddCommGroup M] [Module (End I)ᵐᵒᵖ M],
          IsSimpleModule (End I)ᵐᵒᵖ M → ∀ m : M, MulOpposite.op α • m = 0) →
        α = 0

end Langlands.CuspidalSupport
