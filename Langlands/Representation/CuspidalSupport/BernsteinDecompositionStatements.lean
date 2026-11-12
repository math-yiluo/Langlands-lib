import Langlands.Representation.CuspidalSupport.BernsteinBlock
import Langlands.Representation.Category.Abelian
import Langlands.CategoryTheory.RenardCategoryDecomposition

/-! # The Bernstein decomposition theorem (Renard VI.7.2)

For the actual standard cuspidal data of a standard family of a connected reductive group over a
nonarchimedean local field: every smooth representation is split along the inertial classes, and
the category of smooth representations is the product, in the sense of A.IX, of the full Bernstein
blocks `M(G)_𝔰`, `𝔰 ∈ B(G)` (VI.7.2, Theorem and (VI.7.2.3)); a subrepresentation of a split
representation is split (VI.7.2, first Lemma); each block is an abelian category (remark after the
proof of the Theorem).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.7.2, Theorem, with (VI.7.2.2)–(VI.7.2.3), for the actual standard cuspidal data of
a standard family: the full Bernstein blocks `M(G)_𝔰`, indexed by the inertial classes `𝔰` of
cuspidal data, decompose the category of smooth representations with carriers in `Type uV` in the
sense of A.IX: every smooth representation is the vertex of a coproduct of objects of the blocks
(it is split along `Ω(G)`), and every morphism between objects of distinct blocks is zero. -/
def BernsteinDecompositionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν),
      Renard.IsCategoryDecomposition
        (fun s : BernsteinInertialClass.{uF, max uF uV} i ν family =>
          bernsteinBlockProperty.{uF, uV} i ν family s)

/-- Renard VI.7.2, first Lemma, for the actual standard cuspidal data of a standard family: if a
smooth representation `V` is split along the inertial classes (the vertex of a coproduct of
objects of the Bernstein blocks), then so is every subrepresentation of `V`. -/
def BernsteinSplitSubrepresentationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν)
      (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G))
      (S : Subrepresentation V.representation),
      Renard.IsCoproductOfComponents
          (fun s : BernsteinInertialClass.{uF, max uF uV} i ν family =>
            bernsteinBlockProperty.{uF, uV} i ν family s) V →
        Renard.IsCoproductOfComponents
          (fun s : BernsteinInertialClass.{uF, max uF uV} i ν family =>
            bernsteinBlockProperty.{uF, uV} i ν family s) (SmoothRep.subrepresentation V S)

/-- Renard VI.7.2, remark after the proof of the Theorem, for the actual standard cuspidal data of
a standard family: every full Bernstein block `M(G)_𝔰` is an abelian category, with the
preadditive structure inherited from the category of smooth representations. -/
def BernsteinBlockAbelianStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T),
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (family : BernsteinStandardFamily i ν)
      (s : BernsteinInertialClass.{uF, max uF uV} i ν family),
      ∃ h : Abelian (BernsteinBlock.{uF, uV} i ν family s),
        h.toPreadditive = (inferInstance : Preadditive (BernsteinBlock.{uF, uV} i ν family s))

/-- Renard VI.7.2: the three statements above. -/
def BernsteinDecompositionStatements.{uF', uV'} : Prop :=
  BernsteinDecompositionStatement.{uF', uV'} ∧ BernsteinSplitSubrepresentationStatement.{uF', uV'} ∧
    BernsteinBlockAbelianStatement.{uF', uV'}

end Langlands.CuspidalSupport
