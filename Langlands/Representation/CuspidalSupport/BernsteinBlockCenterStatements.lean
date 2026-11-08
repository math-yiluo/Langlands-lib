import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.CategoryTheory.RenardCategoryDecomposition
import Mathlib.CategoryTheory.Center.Basic

/-! # The centre of a Bernstein block is Noetherian; blocks are indecomposable (Renard VI.10.4)

For the Bernstein block `M(G)_Ω` of an actual standard cuspidal datum, the centre
`ℨ_Ω = End(𝟭_{M(G)_Ω})` is a Noetherian ring (VI.10.4, Corollary), and `M(G)_Ω` admits no
decomposition into two nonzero full subcategories (VI.10.4, Remark 3).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.10.4, Corollary, for the actual standard cuspidal data of a standard family:
the centre `CatCenter` of the Bernstein block of the inertial class of a cuspidal datum `a`
is a Noetherian ring. -/
def BernsteinBlockCenterNoetherianStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν)
      (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family),
      IsNoetherianRing
        (CatCenter (BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)))

/-- Renard VI.10.4, Remark 3 (generalizing Corollary VI.4.5), for the actual standard
cuspidal data of a standard family: whenever the Bernstein block of the inertial class of a
cuspidal datum `a` is decomposed, in the sense of A.IX, into two full subcategories indexed by
`Bool`, one of them contains only zero objects. -/
def BernsteinBlockIndecomposableStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν)
      (a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family)
      (P : Bool → ObjectProperty
        (BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a))),
      Renard.IsCategoryDecomposition P →
        ∃ b : Bool, ∀ X : BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a),
          P b X → IsZero X

/-- The two statements above. -/
def BernsteinBlockCenterStatements.{uF', uV'} : Prop :=
  BernsteinBlockCenterNoetherianStatement.{uF', uV'} ∧
    BernsteinBlockIndecomposableStatement.{uF', uV'}

end Langlands.CuspidalSupport
