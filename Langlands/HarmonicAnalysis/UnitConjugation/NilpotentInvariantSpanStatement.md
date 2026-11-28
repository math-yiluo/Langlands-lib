# Invariant distributions supported on the nilpotent cone

The module `Langlands.HarmonicAnalysis.UnitConjugation.NilpotentInvariantSpanStatement` states,
as `Langlands.HarmonicAnalysis.LieAlgebraNilpotentInvariantSpanStatement.{u, v}`, the spanning
part of Harish-Chandra's Lemma 3.3 for the Lie algebra `A` of the unit group of a
finite-dimensional semisimple algebra over a nonarchimedean local field of characteristic zero.
The statement is **not** proved here.

## Statement

For every nonarchimedean local field `F : Type u` of characteristic zero and every
finite-dimensional semisimple `F`-algebra `A : Type v` with its module topology (and a Borel
σ-algebra on `Aˣ`), writing `N = {X | IsNilpotent X}` for the nilpotent cone and
`J(N) = invariantSupportedIn N` for the conjugation-invariant distributions supported in the
closure of the saturation of `N` (which is `N`):

- `FiniteDimensional ℂ (invariantSupportedIn N)`, and
- `invariantSupportedIn N ≤ Submodule.span ℂ (nilpotentOrbitals A)`: every element of `J(N)`
  is a finite linear combination of orbital distributions of nilpotent elements, for compatible
  quotient measures with convergent orbital integrals (`nilpotentOrbitals`, module
  `Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalVanishing`).

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15),
§3.2, printed p. 19 (PDF p. 34), Lemma 3.3 (Lemma 4): "The measures `μ_O`, indexed by
`O ∈ O(0)`, form a basis for `J(N)`." The set `O(0)` of nilpotent orbits is finite, so the
statement here (the `μ_O` span the finite-dimensional space `J(N)`) is the part of Lemma 3.3
proved by Lemmas 3.4–3.7 (printed pp. 19–22); linear independence (Lemma 3.8) is not part of
it. Each `μ_O` is defined by the theorem of Deligne and Ranga Rao (§3.1, printed p. 17); the
elements of `nilpotentOrbitals A` for one orbit are the positive multiples of `μ_O` given by
the different compatible quotient measures.
