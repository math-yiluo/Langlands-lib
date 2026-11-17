import Langlands.GroupScheme.AutomorphismSchemeOuterLocus
import Langlands.GroupScheme.Reductive.AutomorphismSchemeStatement
import Langlands.GroupScheme.Reductive.AutomorphismSchemeGeometryStatement
import Langlands.GroupScheme.Adjoint.ReductiveRelativeExistenceStatement
import Langlands.GroupScheme.Adjoint.RelativeQuotientIsomorphism
import Langlands.GroupScheme.NormalQuotientReductiveGluing

/-! # From relative automorphism geometry to clopen inner-action loci -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace ReductiveAutomorphismSchemeGeometryStatement

/-- The full automorphism group scheme supplied by the geometry premise. -/
def automorphismScheme (h : ReductiveAutomorphismSchemeGeometryStatement.{u})
    (S : Scheme.{u}) (G : GroupScheme S) (hG : IsReductive G) :
    GroupAutomorphismScheme G :=
  (h S G hG).choose.toGroupAutomorphismScheme

/-- The inner classifier is clopen for every supplied full-centre quotient.
Existence of one reductive quotient allows comparison with the arbitrary
supplied quotient, without imposing affineness on that supplied target. -/
theorem automorphismScheme_clopen
    (h : ReductiveAutomorphismSchemeGeometryStatement.{u})
    (hex : ReductiveRelativeAdjointQuotientExistenceStatement.{u})
    (S : Scheme.{u}) (G : GroupScheme S) (hG : IsReductive G)
    (Gad : GroupScheme S) (p : G ⟶ Gad)
    (hp : RelativeRoot.IsFppfQuotient (center G) p)
    (c : AutomorphicAction Gad G)
    (hc : c.restrict p = AutomorphicAction.conjugation (𝟙 G)) :
    IsOpenImmersion ((h.automorphismScheme S G hG).classifyAction c).hom.hom.left ∧
      IsClosedImmersion ((h.automorphismScheme S G hG).classifyAction c).hom.hom.left := by
  let I := (h S G hG).choose
  obtain ⟨_, _, hI⟩ := (h S G hG).choose_spec
  obtain ⟨B, q, hq⟩ := hex S G hG
  have hGad : IsReductive Gad :=
    IsReductive.of_iso (hp.mapIso hq.isQuotient (Iso.refl G)) hq.isReductive_target
  let hp' : IsRelativeAdjointQuotient p := ⟨hG, hGad, hp⟩
  obtain ⟨O, hEt, hSep, _⟩ := hI Gad p hp'
  have hc' : c = hp'.innerAction := hp'.innerAction_unique c hc
  rw [hc']
  let := hEt
  let := hSep
  change IsOpenImmersion (I.toGroupAutomorphismScheme.classifyAction hp'.innerAction).hom.hom.left ∧
    IsClosedImmersion (I.toGroupAutomorphismScheme.classifyAction hp'.innerAction).hom.hom.left
  exact ⟨I.classifyAction_isOpenImmersion O, I.classifyAction_isClosedImmersion O⟩

end ReductiveAutomorphismSchemeGeometryStatement

/-- Relative automorphism geometry and reductive full-centre quotient existence
give the full clopen automorphism-scheme prerequisite. -/
theorem reductiveAutomorphismScheme_of_geometry
    (h : ReductiveAutomorphismSchemeGeometryStatement.{u})
    (hex : ReductiveRelativeAdjointQuotientExistenceStatement.{u}) :
    ReductiveAutomorphismSchemeStatement.{u} := by
  intro S G hG
  exact ⟨h.automorphismScheme S G hG, fun Gad p hp c hc =>
    h.automorphismScheme_clopen hex S G hG Gad p hp c hc⟩

/-- The two geometric existence premises imply the unchanged arbitrary-action
clopen-locus target, with no restriction on the supplied quotient or action. -/
theorem reductiveInnerActionLocus_of_geometry
    (h : ReductiveAutomorphismSchemeGeometryStatement.{u})
    (hex : RelativeAdjointQuotientExistenceStatement.{u}) :
    ReductiveInnerActionLocusStatement.{u} :=
  reductiveInnerActionLocus_of_automorphismScheme
    (reductiveAutomorphismScheme_of_geometry h
      (ReductiveRelativeAdjointQuotientExistenceStatement.of_affine hex))

end Langlands.GroupScheme
