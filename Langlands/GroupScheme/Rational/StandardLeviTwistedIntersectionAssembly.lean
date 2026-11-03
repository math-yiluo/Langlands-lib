import Langlands.GroupScheme.Rational.StandardLeviCentralizerRealization
import Langlands.GroupScheme.Rational.StandardLeviTwistedRootZeros
import Langlands.GroupScheme.Rational.StandardLeviTwistedIntersectionStatement
import Langlands.GroupScheme.Rational.RelativeRootNegationStatement

/-! # Conditional all-test twisted standard-Levi assembly -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

namespace Langlands.GroupScheme

section Assembly

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
    {nu : cocharacterLattice T} {CM : CoxeterMatrix (SimpleRoot i nu)}
    {cs : CoxeterSystem CM (relativeWeylGroup i)}

/-- A supplied Coxeter realization chooses one actual cocharacter centralizer
model for each finite standard face. Connectedness and root negation remain
explicit structural inputs. -/
def standardLeviCentralizerFamilyOfCoxeterRealization
    (hConn : DynamicConnectedStatement.{u}) (hT : IsSplitTorus T.toGrp)
    (hnu : IsGenericCocharacter i nu)
    (hneg : ∀ alpha ∈ relativeRoots i, -alpha ∈ relativeRoots i)
    (hcs : IsRelativeWeylCoxeterRealization i nu cs) :
    (J : Finset (SimpleRoot i nu)) →
      {zeta : cocharacterLattice T //
        IsStandardCocharacter i nu (rootSet i nu J) zeta ∧
          standardLevi i nu (rootSet i nu J) =
            Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)} := by
  letI : Fintype (SimpleRoot i nu) := (hT.finite_simpleRelativeRoots i nu).fintype
  intro J
  exact standardLeviCentralizerModel hConn hT i nu hnu hneg _
    (hcs.exists_standardCocharacter_finset J)

/-- Given dynamic connectedness and actual-root negation, the Coxeter root
criterion proves the literal twisted standard-Levi equality for every lift
and every test scheme. -/
theorem IsRelativeWeylCoxeterRealization.isStandardLeviTwistedIntersection
    (hcs : IsRelativeWeylCoxeterRealization i nu cs)
    (hConn : DynamicConnectedStatement.{u}) (hT : IsSplitTorus T.toGrp)
    (hnu : IsGenericCocharacter i nu)
    (hneg : ∀ alpha ∈ relativeRoots i, -alpha ∈ relativeRoots i) :
    IsStandardLeviTwistedIntersection i nu cs := by
  let F := standardLeviCentralizerFamilyOfCoxeterRealization hConn hT hnu hneg hcs
  intro I J w hw n hn
  exact standardLevi_twistedIntersection_of_root_zero_iff i hConn hT nu hnu hneg
    (F I).property.1 (F J).property.1
    (F (intersectionSubset cs I J w)).property.1 n (fun _ halpha =>
      hcs.twisted_pairing_eq_zero_iff_of_lift hnu hneg (F I).property.1
        (F J).property.1 hw (F (intersectionSubset cs I J w)).property.1 n hn halpha)

end Assembly

/-- The exact published all-field target follows from the two stated global
structural propositions. This reduction does not discharge either one. -/
theorem standardLeviTwistedIntersection_of_connected_of_negation
    (hConn : DynamicConnectedStatement.{u}) (hneg : RelativeRootNegationStatement.{u}) :
    StandardLeviTwistedIntersectionStatement.{u} := by
  intro k _ G hG T i hi nu
  let := hG.smooth
  let := hG.isAffineHom
  let := hG.connectedSpace
  let := hi.isSplitSubtorus.mono
  intro hnu CM cs hcs
  exact hcs.isStandardLeviTwistedIntersection hConn hi.isSplitSubtorus.1
    hnu (hneg k G hG T i hi)

end Langlands.GroupScheme
