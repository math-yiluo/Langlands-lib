# Comparison with the regular-local Koszul resolution

Author: Worker 1015.

This internal construction chooses generators of the maximal ideal of a regular
local ring and compares finite free residue-field resolutions with the subset
Koszul cochain complex. The finite-length acyclicity proposition is an explicit
input throughout the resolution comparison.

For a commutative regular local ring `R : Type u` and a natural number `g` with
`ringKrullDim R = g`, regularity identifies the minimal number of maximal-ideal
generators with `g`. Noetherianity and
`Submodule.FG.exists_span_finset_card_eq_spanFinrank` give a generating finset of
that cardinality. Enumerating it by `Fin g` gives the chosen family
`regularLocalParameters R g hdim`; its span is exactly `maximalIdeal R`.
The construction also covers `g = 0`.

Given `RegularLocalFiniteLengthAcyclicityStatement.{u}`, the Koszul complex for
any such generating family has zero homology in every degree other than `g`.
Indeed, its parameter ideal annihilates every homology module by
`FiniteKoszulCochain`, so acyclicity applies below `g` with exponent one.
The existing strict upper term bound gives vanishing above `g`.
`FiniteKoszulEnds` supplies its homology isomorphism with the residue field in
degree `g`.

Two general constructions implement the comparison. For an integer cochain
complex `K` of `R`-modules with homology concentrated at `n`,
`derivedIsoOfHomologyConcentrated` constructs an isomorphism from its derived
image to the single complex on `K.homology n` in degree `n`. The proof obtains
both derived truncation bounds by transporting homology vanishing across the
canonical comparison between complex and derived homology, then uses the
existing single-homology isomorphism. For two strictly perfect complexes with
homology concentrated at the same degree and an isomorphism of those homology
modules, `homotopyEquivOfSingleHomology` composes these derived isomorphisms and
lifts the result using `homotopyEquivOfDerivedIso`.

Finally, `regularLocalKoszulResolutionComparison` takes a finite free complex
`C`, its homology vanishing away from `g`, and an isomorphism
`C.homology g ≅ R/m`. It returns a homotopy equivalence from `C` to the Koszul
complex on the chosen parameters. Finite freeness makes both complexes strictly
perfect, and their displayed residue-field isomorphisms supply the required
homology identification.

The provenance is a direct derivation from the existing generator-count,
Koszul, derived-category and strictly perfect comparison APIs. This unit does
not prove its acyclicity input, reverse-dual compatibility, residue-resolution
duality, or the punctual perfect complex proposition.
