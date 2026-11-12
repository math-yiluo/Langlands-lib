import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.Aubert.General.RationalInductionStagesGeometry
import Langlands.GroupScheme.Rational.StandardLeviIntersectionProof

/-! # Bernstein decomposition, induction and restriction (Renard VI.7.3, Proposition)

For a standard parabolic `P = MN` of a standard family, and a Bernstein component `𝔱` of `G`
given by an actual standard cuspidal datum `a`, normalized induction `i_P^G` sends the smooth
representations of `M(F)` all of whose irreducible subquotients have inertial support in the
fibre `i_{MG}⁻¹(𝔱)` into the block `M(G)_𝔱`, and the normalized Jacquet functor `r_P^G` sends
`M(G)_𝔱` into those representations of `M(F)`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.7.3, Proposition, for the standard parabolics `P_J = M_J N_J` of a standard
family, at the saturated carrier universe `max uF uV`. Fix a cuspidal datum `a` of `G`, with
class `𝔱 = [a]` in `B(G)`. A smooth representation `ρ` of `M_J(F)` has *support in the fibre of
`𝔱`* when every irreducible subquotient `τ` of `ρ` is a subquotient of the normalized induction
`i^{M_J}_{L_K}(σ)`, inside `M_J`, of some cuspidal datum `b = (L_K, σ)` of `G` with `K ⊆ J`
(so that `b` is a cuspidal datum of `M_J`) that is inertially equivalent to `a` in `G`. Then:

* for every such `ρ`, `i_{P_J}^G(ρ)` lies in the Bernstein block of `𝔱`;
* for every `V` in the Bernstein block of `𝔱`, `r_{P_J}^G(V)` has support in the fibre of `𝔱`. -/
def BernsteinInductionRestrictionStatement : Prop :=
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
      (J : Finset (SimpleRoot i ν))
      (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family),
      let ind : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) ⥤
          SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
        normalizedInductionFunctor (family.decomposition J) (family.closedUnipotent J)
      let jac : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) ⥤
          SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J) :=
        normalizedJacquetFunctor (unipotent i ν J) (levi i ν J) (family.closedUnipotent J)
          (family.decomposition J).levi_le_normalizer
      let fibre : ObjectProperty (SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J)) := fun ρ =>
        ∀ τ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J),
          τ.IsIrreducible → SmoothRep.IsSubquotient τ ρ →
            ∃ (I : Finset J) (b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
              (h : leviIndex J I = b.roots),
              IsBernsteinInertiaRelated i ν family a b ∧
                SmoothRep.IsSubquotient τ
                  ((leviNormalizedInductionFunctor (family.closedLevi J)
                    (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
                      family.maximalSplitTorus family.genericCocharacter b.roots J
                      (h ▸ leviIndex_subset J I))
                    (h ▸ family.leviDecomposition J I) (family.closedUnipotent b.roots)).obj
                    (bernsteinLiteralLeviRep i ν b.roots b.representation))
      (∀ ρ : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν J), fibre ρ →
          bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a)
            (ind.obj ρ)) ∧
        ∀ V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
          bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) V →
            fibre (jac.obj V)

end Langlands.CuspidalSupport
