# Invariant open and closed neighbourhoods of compact sets in the Lie algebra of `Aˣ`

The module `Langlands.HarmonicAnalysis.UnitConjugation.ConjugationDomainStatement` states, as
the proposition `Langlands.HarmonicAnalysis.LieAlgebraConjugationDomainStatement.{u, v}`,
Harish-Chandra's Lemma 4.3 for the Lie algebra `A` of the unit group `Aˣ` of a
finite-dimensional semisimple algebra over a nonarchimedean local field of characteristic zero.
The statement is **not** proved here.

## Statement

`LieAlgebraConjugationDomainStatement.{u, v}` quantifies over

- a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]`: a nonarchimedean local field of characteristic
  zero;
- `A : Type v` with `[Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsModuleTopology F A]`: a finite-dimensional semisimple `F`-algebra with
  its module topology; its topological ring structure is `IsModuleTopology.isTopologicalRing`,
  bound with `haveI` inside the statement;
- a compact `ω ⊆ A`.

The claim: there are a compact `ω₀ ⊆ A` and a set `D ⊆ A` such that

- `D` is open and closed (`IsClopen D`);
- `D` is invariant under conjugation: `conjugationHomeomorph u X = u X u⁻¹ ∈ D` for every unit
  `u` and every `X ∈ D`;
- `ω ⊆ D ⊆ conjugationSaturation ω₀ = ⋃_u u ω₀ u⁻¹`.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15):

- §2, printed p. 13 (PDF p. 28): "By a `G`-domain in `g`, we mean a `G`-invariant subset of `g`
  which is both open and closed."
- §4, Lemma 4.3 (Lemma 10), printed p. 31 (PDF p. 46): "Let `ω` be a compact set in `g`. Then we
  can choose another compact set `ω₀` and a `G`-domain `D` in `g` such that
  `ω₀^G ⊃ D ⊃ ω`." Here `ω₀^G = ⋃_{x ∈ G} Ad(x) ω₀` (Introduction, printed p. 2). The proof uses
  Lemma 2.6 (a `G`-domain between a semisimple element and the saturation of any of its
  neighbourhoods), the finiteness of the conjugacy classes of Cartan subalgebras and the fact
  that the closure of every orbit contains a semisimple element.

Here `G = Aˣ`, the `F`-points of the connected reductive group `GL₁(A)`, whose Lie algebra is
`A` with the adjoint action `X ↦ u X u⁻¹` (`conjugationHomeomorph`), so a `G`-domain is an open
and closed subset of `A` stable under conjugation by units, and `ω₀^G` is
`conjugationSaturation ω₀`. The statement is Lemma 4.3 in this setting, with the same
quantifiers and conclusion.

In Harish-Chandra's proof of Theorem 4.4 (1) (§4, printed p. 31, PDF p. 46), `ω ⊆ D` and the
closedness and conjugation invariance of `D` give `closure (conjugationSaturation ω) ⊆ D`. Hence
every distribution in `J(ω)` is supported in `D`, and every regular orbit in `D` is contained in
`ω₀^G`.
