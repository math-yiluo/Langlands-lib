import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.Category.SmoothCoproducts

/-! # Characterizations of a Bernstein block (Renard VI.7.2, Proposition)

For an actual standard cuspidal datum `(M, ρ)` of a standard family, with standard parabolic
`P = MN` and inertial class `D = [ρ]` in `M`, a smooth representation `V` lies in the Bernstein
block `M(G)_Ω` of `(M, ρ)` if and only if (i) it embeds in a direct sum of representations
`i_P^G(τ, E)` with `(τ, E) ∈ M(M)_D`; if and only if (ii) it is a subquotient of such a sum; if and
only if (iii) for every cuspidal datum `(L, σ)` not inertially equivalent to `(M, ρ)`, with
standard parabolic `Q = LU`, the representation `σ` is not a subquotient of `r_Q^G(V)`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.7.2, Proposition, for the actual standard cuspidal data of a standard family, at
the saturated carrier universe `max uF uV`. Let `a = (M, ρ)` be a cuspidal datum, `P = MN` its
standard parabolic, `M(M)_D` the full subcategory of smooth representations of `M(F)` whose
irreducible subquotients are all unramified twists of `ρ`, and `i_P^G` normalized induction
(through the literal standard Levi). For every smooth `V`, membership of `V` in the Bernstein
block of the class of `a` is equivalent to each of:

* (i) `V` embeds in `⊕_k i_P^G(τ_k)` for some family `(τ_k)` in `M(M)_D`;
* (ii) `V` is a subquotient of such a direct sum;
* (iii) for every cuspidal datum `b = (L, σ)` not inertially equivalent to `a`, `σ` (on the
  literal standard Levi) is not a subquotient of the normalized Jacquet module `r_Q^G(V)` along
  the standard parabolic `Q = LU` of `b`. -/
def BernsteinBlockCharacterizationStatement : Prop :=
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
      let ind : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints (bernsteinLeviScheme i ν a.roots)) →
          SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) := fun τ =>
        (normalizedInductionFunctor (family.decomposition a.roots)
          (family.closedUnipotent a.roots)).obj (bernsteinLiteralLeviRep i ν a.roots τ)
      ∀ V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
        (bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) V ↔
          ∃ (κ : Type (max uF uV))
            (τ : κ → SmoothRep.{0, uF, max uF uV} ℂ
              (rationalPoints (bernsteinLeviScheme i ν a.roots))),
            (∀ k, rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots)
              a.representation (τ k)) ∧
            letI := Classical.decEq κ
            SmoothRep.IsSubrepresentation V
              (SmoothRep.directSum.{uF, max uF uV, max uF uV} fun k => ind (τ k))) ∧
        (bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) V ↔
          ∃ (κ : Type (max uF uV))
            (τ : κ → SmoothRep.{0, uF, max uF uV} ℂ
              (rationalPoints (bernsteinLeviScheme i ν a.roots))),
            (∀ k, rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots)
              a.representation (τ k)) ∧
            letI := Classical.decEq κ
            SmoothRep.IsSubquotient V
              (SmoothRep.directSum.{uF, max uF uV, max uF uV} fun k => ind (τ k))) ∧
        (bernsteinSaturatedBlockProperty i ν family (bernsteinInertialClass i ν family a) V ↔
          ∀ b : BernsteinCuspidalDatum.{uF, max uF uV} i ν family,
            ¬ IsBernsteinInertiaRelated i ν family a b →
              ¬ SmoothRep.IsSubquotient (bernsteinLiteralLeviRep i ν b.roots b.representation)
                ((normalizedJacquetFunctor (unipotent i ν b.roots) (levi i ν b.roots)
                  (family.closedUnipotent b.roots)
                  (family.decomposition b.roots).levi_le_normalizer).obj V))

end Langlands.CuspidalSupport
