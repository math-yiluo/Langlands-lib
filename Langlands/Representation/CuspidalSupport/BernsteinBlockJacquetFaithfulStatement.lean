import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.CuspidalSupport.RationalSummandSmallProgeneratorStatement

/-! # The Jacquet functor to the cuspidal component kills no block object (Renard VI.10.3)

For an actual standard cuspidal datum `(M, ρ)` with inertial class `𝔰` and Levi inertial class
`D`, the composite `r_D` of the normalized Jacquet functor `r_P^G` with the projection to
`M(M)_D` sends nonzero objects of the Bernstein block `M(G)_𝔰` to nonzero objects. Since
`Π_D = ind_{⁰M}^M(ρ₀)` is a progenerator of `M(M)_D`, this is stated as nonvanishing of
`Hom_M(Π_D, r_P^G(X))`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.10.3, Proposition, in derived form for the actual standard cuspidal data of a
standard family: with `a`, `ρ₀` and `Π_D = ind_{⁰M(F)}^{M(F)} ρ₀` as in
`BernsteinInducedProgeneratorStatement`, for every object `X` of the Bernstein block of the
inertial class of `a` with nonzero carrier there is a nonzero morphism from `Π_D` (transported
to the literal standard Levi) to the normalized Jacquet module of `X` along the standard
parabolic of `a.roots`. -/
def BernsteinBlockJacquetFaithfulStatement : Prop :=
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
          ∀ X : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a),
            Nontrivial X.obj →
              ∃ f : bernsteinLiteralLeviRep i ν a.roots
                    (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀) ⟶
                  (normalizedJacquetFunctor (unipotent i ν a.roots) (levi i ν a.roots)
                    (family.closedUnipotent a.roots)
                    (family.decomposition a.roots).levi_le_normalizer).obj X.obj,
                f ≠ 0

end Langlands.CuspidalSupport
