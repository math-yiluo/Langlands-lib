import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! # A Bernstein block as a module category (Renard VI.10.2, Theorem)

For the induced progenerator `Π_Ω` of a Bernstein block `M(G)_Ω` (VI.10.1) and
`R_Ω = End_G(Π_Ω)`, the functor `π ↦ Hom_G(Π_Ω, π)` is an equivalence of `M(G)_Ω` with the
category of unital right `R_Ω`-modules.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.10.2, Theorem, for the actual standard cuspidal data of a standard family: with
`Π_Ω` the normalized induction of `Π_D = ind_{⁰M(F)}^{M(F)} ρ₀` along the standard parabolic
of a cuspidal datum `a`, as in `BernsteinInducedProgeneratorStatement`, `Π_Ω` lies in the
Bernstein block `M(G)_Ω` of the inertial class of `a`, and `Hom(Π_Ω, •)` is an equivalence
from that block to unital modules over `(End Π_Ω)ᵐᵒᵖ`, i.e. unital right `R_Ω`-modules. -/
def BernsteinBlockHomEquivalenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν)
      (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family),
      haveI : IsClosedImmersion (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left :=
        Standard.isClosedSubgroup_leviHom i ν (rootSet i ν a.roots)
      haveI : IsAffine (bernsteinLeviScheme i ν a.roots).X.left :=
        isAffine_of_isAffineHom (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.left
      haveI : LocallyOfFiniteType (bernsteinLeviScheme i ν a.roots).X.hom := by
        rw [← (Standard.leviHom i ν (rootSet i ν a.roots)).hom.hom.w]
        infer_instance
      letI : TopologicalSpace (rationalPoints (bernsteinLeviScheme i ν a.roots)) :=
        rationalPointTopology F (bernsteinLeviScheme i ν a.roots).X
      ∀ ρ₀ : SmoothRep.{0, uF, max uF uV} ℂ
          (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots)),
        ρ₀.IsIrreducible →
        ∀ j : ρ₀ ⟶ SmoothRep.restrictSubgroup
            (Plancherel.rationalCommonNormKernel (bernsteinLeviScheme i ν a.roots))
            a.representation,
          Function.Injective (SmoothRep.hom j) →
          let piOmega : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
            (normalizedInductionFunctor (family.decomposition a.roots)
              (family.closedUnipotent a.roots)).obj
                (bernsteinLiteralLeviRep i ν a.roots
                  (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))
          ∃ hmem : bernsteinSaturatedBlockProperty i ν family
              (bernsteinInertialClass i ν family a) piOmega,
            (preadditiveCoyonedaObj
              (⟨piOmega, hmem⟩ :
                BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a))).IsEquivalence

end Langlands.CuspidalSupport
