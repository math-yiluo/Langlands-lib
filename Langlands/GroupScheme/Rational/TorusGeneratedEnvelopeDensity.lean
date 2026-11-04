import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeDomination
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeRationalDensityStatement
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingStatement
import Langlands.GroupScheme.Torus.RationalDensity
import Langlands.AlgebraicGeometry.PointTopology.AffineDensity

/-! # Rational density from finite Galois torus splitting -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [Infinite k]

/-- Finite Galois splitting and the norm-density theorem give density for each torus. -/
theorem IsTorus.hasDenseRationalPoints_of_finiteGaloisSplitting
    (hsplit : TorusFiniteGaloisSplittingStatement.{u})
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) :
    HasDenseRationalPoints k T.X := by
  obtain ⟨K, hK, hAlg, hfin, hgal, hsplitT⟩ := hsplit k T hT
  let := hK
  let := hAlg
  let := hfin
  let := hgal
  exact TorusDensity.dense_rationalPoints_of_isSplitTorus_baseChange T hsplitT

/-- Dominant images of tori have dense rational points under finite Galois torus splitting. -/
theorem HasPointedTorusDomination.hasDenseRationalPoints_of_finiteGaloisSplitting
    (hsplit : TorusFiniteGaloisSplittingStatement.{u})
    {H : GroupScheme (Spec (CommRingCat.of k))} (hH : HasPointedTorusDomination H) :
    HasDenseRationalPoints k H.X := by
  obtain ⟨P, p, hP, hp, -⟩ := hH
  exact hasDenseRationalPoints_of_denseRange p hp.denseRange
    (hP.hasDenseRationalPoints_of_finiteGaloisSplitting hsplit)

/-- The actual fixed torus envelope inherits rational density from its torus domination. -/
theorem TorusGeneratedEnvelope.hasDenseRationalPoints_of_finiteGaloisSplitting
    (hsplit : TorusFiniteGaloisSplittingStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (D : TorusGeneratedEnvelope G) :
    HasDenseRationalPoints k D.group.X :=
  D.hasPointedTorusDomination.hasDenseRationalPoints_of_finiteGaloisSplitting hsplit

/-- The exact envelope-density target follows from finite Galois splitting of tori. -/
theorem torusGeneratedEnvelopeRationalDensity_of_finiteGaloisSplitting
    (hsplit : TorusFiniteGaloisSplittingStatement.{u}) :
    TorusGeneratedEnvelopeRationalDensityStatement.{u} := by
  intro k _ _ G _ _ _ D
  exact D.hasDenseRationalPoints_of_finiteGaloisSplitting hsplit

/-- Choose an actual rational point meeting a given nonempty open of the fixed envelope. -/
def TorusGeneratedEnvelope.rationalPointMeetingOpenOfFiniteGaloisSplitting
    (hsplit : TorusFiniteGaloisSplittingStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (D : TorusGeneratedEnvelope G)
    (U : D.group.X.left.Opens) (hU : (U : Set D.group.X.left).Nonempty) :
    {p : RationalPoint k D.group.X // ∃ x, p.left x ∈ U} := by
  have hex : ∃ p : RationalPoint k D.group.X, ∃ x, p.left x ∈ U := by
    have hd := D.hasDenseRationalPoints_of_finiteGaloisSplitting hsplit
    obtain ⟨y, hyU, hyp⟩ := hd.inter_open_nonempty U U.isOpen hU
    obtain ⟨p, x, rfl⟩ := Set.mem_iUnion.mp hyp
    exact ⟨p, x, hyU⟩
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

end Langlands.GroupScheme
