import Langlands.GroupScheme.Reductive.RationalPointDensityStatement
import Langlands.GroupScheme.Reductive.TorusDominationStatement
import Langlands.GroupScheme.Reductive.TorusDominationProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.RationalDensity
import Langlands.AlgebraicGeometry.PointTopology.AffineDensity

/-! # Zariski density of rational points of connected reductive groups (assembly) -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- Torus domination and finite Galois splitting of tori imply density of rational points
of connected reductive groups over infinite fields. -/
theorem reductiveRationalPointDensity_of_domination_of_splitting
    (hdom : ReductiveTorusDominationStatement.{u})
    (hsplit : TorusFiniteGaloisSplittingStatement.{u}) :
    ReductiveRationalPointDensityStatement.{u} := by
  intro k _ _ G hG
  obtain ⟨T, f, hT, hf⟩ := hdom k G hG
  obtain ⟨K, _, _, _, _, hK⟩ := hsplit k T hT
  have hTd : HasDenseRationalPoints k T.X :=
    TorusDensity.dense_rationalPoints_of_isSplitTorus_baseChange (k := k) (K := K) T hK
  exact hasDenseRationalPoints_of_denseRange f hf hTd

/-- Torus domination implies density of rational points of connected reductive groups over
infinite fields, with finite Galois splitting of tori supplied by its published proof. -/
theorem reductiveRationalPointDensity_of_domination
    (hdom : ReductiveTorusDominationStatement.{u}) :
    ReductiveRationalPointDensityStatement.{u} :=
  reductiveRationalPointDensity_of_domination_of_splitting hdom torusFiniteGaloisSplitting.{u}

/-- Over an infinite field, the rational points of a connected reductive group scheme are
Zariski dense. -/
theorem reductiveRationalPointDensity : ReductiveRationalPointDensityStatement.{u} :=
  reductiveRationalPointDensity_of_domination reductiveTorusDomination.{u}

end Langlands.GroupScheme
