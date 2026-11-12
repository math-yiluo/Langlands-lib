import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.Category.Abelian
import Langlands.Representation.Hecke.NondegenerateModuleFunctor
import Langlands.Algebra.NonUnitalModuleRestrictScalars
import Langlands.HarmonicAnalysis.GroupAction
import Mathlib.CategoryTheory.Center.Basic
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.RingTheory.NonUnitalSubring.Basic

/-! # Central idempotents of the Bernstein decomposition (Renard VI.7.4)

For the actual standard cuspidal data of a standard family of a connected reductive group over
a nonarchimedean local field: the projections onto the Bernstein blocks `M(G)_𝔰` are idempotents
`e_𝔰` of the centre of the category of smooth representations, with `Id = ∑_𝔰 e_𝔰` (finite on
each vector); the Hecke algebra is the direct sum of the two-sided ideals `e_𝔰 ∗ H(G) ∗ e_𝔰`,
and `M(G)_𝔰` is equivalent to the category of nondegenerate `e_𝔰 ∗ H(G) ∗ e_𝔰`-modules
(VI.7.4).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MeasureTheory
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.7.4, first paragraph, for the actual standard cuspidal data of a standard family:
there are idempotents `e_𝔰` of the centre of the category of smooth representations with
carriers in `Type uV`, indexed by the inertial classes `𝔰`, such that `e_𝔰` is the identity on
every object of the Bernstein block `M(G)_𝔰` and zero on every object of every other block
(so `e_𝔰` is the projection onto `M(G)_𝔰`), and `Id = ∑_𝔰 e_𝔰`: on every vector `v` only
finitely many `e_𝔰 v` are nonzero and their sum is `v`. -/
def BernsteinCentralIdempotentStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν),
      ∃ e : BernsteinInertialClass.{uF, max uF uV} i ν family →
          CatCenter (SmoothRep.{0, uF, uV} ℂ (rationalPoints G)),
        (∀ s, IsIdempotentElem (e s)) ∧
        (∀ (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
            (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)),
          bernsteinBlockProperty.{uF, uV} i ν family s V → (e s).app V = 𝟙 V) ∧
        (∀ (s t : BernsteinInertialClass.{uF, max uF uV} i ν family), s ≠ t →
          ∀ V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G),
            bernsteinBlockProperty.{uF, uV} i ν family t V → (e s).app V = 0) ∧
        ∀ (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G)) (v : V),
          (Function.support fun s => SmoothRep.hom ((e s).app V) v).Finite ∧
            ∑ᶠ s, SmoothRep.hom ((e s).app V) v = v

/-- Renard VI.7.4, decomposition of the Hecke algebra, for the actual standard cuspidal data
of a standard family, at carriers in `Type (max uF uV)`. Let `haar` be a left Haar measure on
`G(F)`, assume the left regular representation `λ` on test functions smooth (Renard III.1.2),
and let `Λ` be `λ` with carrier lifted to `Type (max uF uV)`. Let `e_𝔰` be central
endomorphisms of the identity functor that are the identity on `M(G)_𝔰` and zero on the other
blocks. Then there are nonunital subrings `S 𝔰` of `H(G)` such that

* `S 𝔰 = e_𝔰 ∗ H(G)` is the image of `H(G)` under the action of `e_𝔰` on `Λ`;
* each `S 𝔰` is a two-sided ideal of `H(G)`;
* `H(G)` is the internal direct sum of the `S 𝔰`;
* `M(G)_𝔰` is equivalent to the category of nondegenerate `S 𝔰`-modules, by an equivalence
  whose underlying functor is (up to isomorphism) the Hecke module of a smooth representation
  with its action restricted to `S 𝔰`. -/
def BernsteinHeckeIdealDecompositionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν)
      [MeasurableSpace (rationalPoints G)] [BorelSpace (rationalPoints G)]
      (haar : Measure (rationalPoints G)) [haar.IsHaarMeasure]
      (hl : IsSmooth (HarmonicAnalysis.GroupAction.leftTests (G := rationalPoints G)))
      (e : BernsteinInertialClass.{uF, max uF uV} i ν family →
        CatCenter (SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G))),
      (∀ (s : BernsteinInertialClass.{uF, max uF uV} i ν family)
          (V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G)),
        bernsteinBlockProperty.{uF, max uF uV} i ν family s V → (e s).app V = 𝟙 V) →
      (∀ (s t : BernsteinInertialClass.{uF, max uF uV} i ν family), s ≠ t →
        ∀ V : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
          bernsteinBlockProperty.{uF, max uF uV} i ν family t V → (e s).app V = 0) →
      let Λ : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
        SmoothRep.universeLift.{uV}
          (SmoothRep.of (HarmonicAnalysis.GroupAction.leftTests (G := rationalPoints G)) hl)
      ∃ S : BernsteinInertialClass.{uF, max uF uV} i ν family →
          NonUnitalSubring (Hecke.HeckeAlgebra haar),
        (∀ (s : BernsteinInertialClass.{uF, max uF uV} i ν family) (f : Hecke.HeckeAlgebra haar),
          f ∈ S s ↔ ∃ g : Hecke.HeckeAlgebra haar,
            SmoothRep.hom ((e s).app Λ) (ULift.up (Hecke.HeckeAlgebra.toTestFunction haar g)) =
              ULift.up (Hecke.HeckeAlgebra.toTestFunction haar f)) ∧
        (∀ (s : BernsteinInertialClass.{uF, max uF uV} i ν family) (a f : Hecke.HeckeAlgebra haar),
          f ∈ S s → a * f ∈ S s ∧ f * a ∈ S s) ∧
        (letI := Classical.decEq (BernsteinInertialClass.{uF, max uF uV} i ν family);
          DirectSum.IsInternal fun s => (S s).toAddSubgroup) ∧
        ∀ s : BernsteinInertialClass.{uF, max uF uV} i ν family,
          ∃ E : BernsteinBlock.{uF, max uF uV} i ν family s ≌
              Algebra.NondegenerateModuleCat.{uF, max uF uV} (S s),
            Nonempty (E.functor ⋙ Algebra.nondegenerateInclusion (S s) ≅
              (bernsteinBlockProperty.{uF, max uF uV} i ν family s).ι ⋙
                Hecke.heckeNondegenerateModuleFunctor.{uF, max uF uV} haar ⋙
                  Algebra.nondegenerateInclusion (Hecke.HeckeAlgebra haar) ⋙
                    Algebra.NonUnitalModuleRestrictScalars.functor
                      (NonUnitalSubringClass.subtype (S s)))

/-- Renard VI.7.4: the two statements above. -/
def BernsteinCentralIdempotentStatements.{uF', uV'} : Prop :=
  BernsteinCentralIdempotentStatement.{uF', uV'} ∧
    BernsteinHeckeIdealDecompositionStatement.{uF', uV'}

end Langlands.CuspidalSupport
