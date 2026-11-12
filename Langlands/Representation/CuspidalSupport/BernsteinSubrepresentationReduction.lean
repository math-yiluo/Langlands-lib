import Langlands.Representation.CuspidalSupport.BernsteinDecompositionStatements
import Langlands.Representation.CuspidalSupport.BernsteinSupportComparison
import Langlands.Representation.Category.DisjointConstituentCoproduct

/-! # Subrepresentation splitting from the actual Bernstein support comparison -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance bernsteinSubrepresentationTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- The exact actual support-uniqueness comparison makes distinct blocks
orthogonal, without any objectwise decomposition premise. -/
theorem bernsteinBlock_offDiagonalHomsZero_of_supportUniqueness
    (hunique : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family) :
    Renard.OffDiagonalHomsZero
      (fun s : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, uV} i ν family s) := by
  intro s t hst V W hV hW f
  apply SmoothRep.hom_eq_zero_of_no_common_irreducibleSubquotient _ f
  intro π hπ hπV hπW
  exact hst (hunique _ s t (hV π hπ hπV) (hW π hπ hπW))

/-- Assuming only the named actual support-uniqueness comparison, the
inverse-image cofan of a Bernstein-block coproduct is colimiting. -/
def bernsteinSubrepresentationCofanIsColimit
    (hunique : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (A : BernsteinInertialClass.{uF, max uF uV} i ν family →
      SmoothRep.{0, uF, uV} ℂ (rationalPoints G))
    (s : Cofan A) (hs : IsColimit s)
    (hA : ∀ t, bernsteinBlockProperty i ν family t (A t))
    (S : Subrepresentation s.pt.representation) :
    IsColimit (SmoothRep.subrepresentationCofan A s S) := by
  classical
  apply SmoothRep.subrepresentationCofanIsColimit A s hs _ S
  intro t u htu π hπ hπt hπu
  exact htu (hunique _ t u (hA t π hπ hπt) (hA u π hπ hπu))

/-- The first Lemma of VI.7.2, with the still-required actual support
uniqueness retained explicitly; no partition or substitute block is used. -/
theorem bernsteinSplitSubrepresentation_of_supportUniqueness
    (hunique : BernsteinInertialSupportUniquenessStatement.{uF, uV} i ν family)
    (V : SmoothRep.{0, uF, uV} ℂ (rationalPoints G))
    (S : Subrepresentation V.representation)
    (hV : Renard.IsCoproductOfComponents
      (fun s : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, uV} i ν family s) V) :
    Renard.IsCoproductOfComponents
      (fun s : BernsteinInertialClass.{uF, max uF uV} i ν family =>
        bernsteinBlockProperty.{uF, uV} i ν family s) (SmoothRep.subrepresentation V S) := by
  apply SmoothRep.isCoproductOfComponents_subrepresentation
    (fun s π => IsBernsteinInertialSupport i ν family s (SmoothRep.universeLift.{uF} π))
    _ hV S
  intro s t hst π _ hs ht
  exact hst (hunique _ s t hs ht)

end Langlands.CuspidalSupport
