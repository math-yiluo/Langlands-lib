import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreEtaleLocusOpen

/-! # Murre's charts from Lemma 2

The inductive step of Murre's proof of Proposition 2 over an affine noetherian base
(`MurreNoetherianChartsStatement`) follows from Murre's Lemma 2 over such bases
(`MurreEtaleLocusOpenStatement`). This module states that implication; it proves nothing. -/

universe u v

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

/-- Murre's Lemma 2 (openness of the étale locus of a chart over the spectrum of a noetherian
ring) implies the construction of monomorphic, infinitesimally étale charts, locally of
finite type and formally unramified, through which every point of `F` with values in a field
factors. -/
def MurreChartsFromEtaleLocusStatement : Prop :=
  MurreEtaleLocusOpenStatement.{u, v} → MurreNoetherianChartsStatement.{u, v}

end Langlands.AlgebraicGeometry.UnramifiedFunctor
