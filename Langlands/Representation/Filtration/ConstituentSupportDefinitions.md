# Actual composition-factor support and multiplicity-free series

This module defines three notions in namespace `Langlands`, using the
published actual filtration and multiplicity definitions. It proves no
support transport, multiplicity independence, or lattice theorem.

## Definitions

Let `k : Type uK` be any field and `G : Type uG` any monoid. The representation
`A : Rep.{uA} k G` and a target `τ : Rep.{uT} k G` have independent carrier
universes.

- `HasJordanHolderConstituent A τ : Prop` is exactly
  `∃ m : ℕ, HasJordanHolderMultiplicity A τ m ∧ 0 < m`.
  The imported multiplicity predicate retains an actual finite filtration
  `s : ObjectRepFiltration A n`, simplicity of every graded quotient, and an
  exact count of the indices whose graded representations are equivalent to
  `τ`. Positive multiplicity therefore records occurrence in an actual finite
  simple series. No total multiplicity function or choice of series is used.
- `jordanHolderSupport A : Set (Rep.{uT} k G)` is exactly the set of targets
  satisfying `HasJordanHolderConstituent A τ`. The target universe `uT` is
  explicit in the result type and independent of `uA`, `uK`, and `uG`.
- `HasMultiplicityFreeCompositionSeries A : Prop` asserts the existence of
  `n : ℕ` and `s : ObjectRepFiltration A n` with `s.HasSimpleFactors`, such
  that for every `i j : Fin n`, a nonempty `Representation.Equiv` between
  `(s.gradedRepresentation i).ρ` and `(s.gradedRepresentation j).ρ` implies
  `i = j`. The condition compares the actual successive quotient
  representations, including all their occurrences.

The length `n` may be zero. An empty filtration has both endpoints equal,
so the imported filtration laws force its ambient representation to be zero;
the simple-factor and pairwise conditions then quantify over `Fin 0`.
Thus the definitions retain the zero representation and empty series. There
is no group, smoothness, admissibility, finite-dimensionality, or nonzero
ambient hypothesis.

## Actual representations and equivalence classes

The support is a set of actual representations in the specified target
carrier universe. Once transport under representation equivalence is
proved, it is saturated under that equivalence: an equivalent target in the
same target universe has the same membership. Targets in different carrier
universes belong to different sets, whose membership may likewise be
compared by a transport theorem. Such a transport theorem is not supplied
by this module.

Even a single equivalence class can contain many actual representations.
Consequently this support is usually not a finite set of actual
representatives. Finite support in the composition-factor sense concerns
equivalence classes. Neither a composition series nor a representative
of any class is chosen here.

These definitions alone do not show that targets in an arbitrary independent
carrier universe detect inclusion of submodules. A planned support-lattice
statement will specialize the target carrier universe to that of the ambient
representation. No lattice embedding, finiteness theorem for actual
representatives, additivity, multiplicity independence, or segment
constituent result is asserted here.

## Source and provenance

Provenance: derived, internal actual-series encoding.

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
§2.4, Proposition, printed p.177 / PDF page 14. Literature ID:
`zelevinsky-1980-induced-ii`. Retained original SHA-256:
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The original printed pp.176–178 / PDF pages 13–15 were read directly.
No source-specific project erratum was found.

Proposition 2.4 uses the composition-factor support of a multiplicity-free
module to embed its submodule lattice in the subsets of that support.
The preceding §2.1(c), printed p.176 / PDF page 13, describes multiplicity-free
representations by requiring each composition factor to occur with
multiplicity one. The present module supplies only the underlying finite
series and support vocabulary. Its positive-multiplicity predicate reuses
`HasJordanHolderMultiplicity` from `Filtration.MultiplicityStatement`;
its pairwise condition uses the graded objects of
`Filtration.ObjectDefinitions`.

The use of arbitrary fields, monoids, independent carrier universes, and
existential actual simple series is an internal algebraic presentation.
It does not extend Zelevinsky's representation-theoretic conclusions to
that generality.
