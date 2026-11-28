# Invariant distributions near the central translates of the nilpotent cone

The module `Langlands.HarmonicAnalysis.UnitConjugation.CentralNilpotentDensityStatement`
states, as `Langlands.HarmonicAnalysis.LieAlgebraCentralNilpotentDensityStatement.{u, v}`,
Harish-Chandra's Lemma 3.12 under the induction hypothesis of his proof of Theorem 3.1, for the
Lie algebra `A` of the unit group of a finite-dimensional semisimple algebra over a
nonarchimedean local field of characteristic zero, in a form that allows `A` to have a center.
The statement is **not** proved here.

## Statement

For every nonarchimedean local field `F : Type u` of characteristic zero and every
finite-dimensional semisimple `F`-algebra `A : Type v`:

- **hypothesis (induction hypothesis)**: `RegularOrbitalDensityFor F B` (Theorem 3.1 for `B`,
  module `Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalVanishing`) for every
  finite-dimensional semisimple `F`-algebra `B : Type v` with `finrank F B < finrank F A`;
- **conclusion**: for every module topology on `A`, every Borel σ-algebra on `Aˣ` and every
  Schwartz–Bruhat function `f` with `RegularOrbitalVanishing F A f` (`f ∈ D₀`) such that
  `S f = 0` for every central `Z` (`Z ∈ Subalgebra.center F A`) and every
  `S ∈ invariantSupportedIn {X | IsNilpotent (X - Z)}` (the conjugation-invariant distributions
  supported on `Z + N`, `N` the nilpotent cone), every conjugation-invariant distribution `T`
  satisfies `T f = 0`.

## Source

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, with notes by
S. DeBacker and P. J. Sally, Jr., University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15),
§§3.3–3.4, printed pp. 23–27 (PDF pp. 38–42):

- "We shall prove Theorem 3.1 by induction on `dim G`" (printed p. 23); Lemma 3.9 (Lemma 5)
  applies the induction hypothesis to the centralizer `M` of a noncentral semisimple element
  `γ`, and Corollary 3.10 concludes: "Let `f` be an element in `D₀` such that `Supp(f)` does
  not meet `z + N`. Then `T(f) = 0` for all `T ∈ J`" (printed p. 25).
- Lemma 3.11 reduces the proof to semisimple `G`, and Lemma 3.12 (Lemma 6) reads: "Suppose
  `f ∈ D₀` such that `μ_O(f) = 0` for all `O ∈ O(0)`. Then `T(f) = 0` for `T ∈ J`"
  (printed p. 26), proved through Lemmas 3.13–3.14 by induction over the nilpotent orbits
  ordered by dimension (printed pp. 26–27).

For the unit group of `A` the centralizer of a semisimple element `γ` is the unit group of the
semisimple algebra `C_A(γ)`, of smaller dimension when `γ` is not central, so Theorem 3.1 for
the algebras of smaller dimension is the induction hypothesis Harish-Chandra uses. The orbits
contained in `z + N` are the translates `Z + O` of the nilpotent orbits by central elements,
and by Lemma 3.3 the distributions `μ_{Z+O}` span the invariant distributions supported on
`Z + N`; the hypothesis on `f` here is therefore the vanishing of all orbital integrals of `f`
over orbits in `z + N`, the condition of Lemma 3.12 for a reductive group with center. The
center of `A` contains `F · 1`, so it is never zero for `A ≠ 0`; Harish-Chandra removes it by
Lemma 3.11, while here the central translates are kept in the hypothesis. The statement is a
consequence of Theorem 3.1 itself.
