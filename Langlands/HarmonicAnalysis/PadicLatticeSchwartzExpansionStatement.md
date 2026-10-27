# Single-lattice coset expansions of p-adic Schwartz–Bruhat functions

Worker 739 authored this focused proposition definition.
`Langlands.HarmonicAnalysis.PadicLatticeSchwartzExpansionStatement.{u}` has
implicit parameters `{p : ℕ}` and `[Fact p.Prime]`, followed by explicit
parameters `(F : Langlands.PadicField.{u} p)` and `(T : F.TopologicalData)`.
It returns `Prop` for arbitrary field universe `u` and every supplied `T`.
The module supplies no proof.

## Exact scope

The proposition installs `T.topology`, `T.valuativeRel` and `T.localField`.
The test-function space `SchwartzBruhat F.Carrier` from [Basic](Basic.md) is
formed in the supplied topology `T.topology`, so local constancy and compact
support refer to that topology and to no other. The valuation and local-field
instances are the supplied ones; no part of the statement replaces them.

For every `f : SchwartzBruhat F.Carrier` the proposition asserts that there exist
`m : ℤ`, `N : ℕ`, `c : Fin N → ℂ` and `a : Fin N → F.Carrier` such that

```text
∀ x : F.Carrier,
  f x = ∑ i : Fin N, c i *
    ({z : F.Carrier | z - a i ∈ T.additiveLattice m}.indicator (fun _ => (1 : ℂ))) x.
```

- The lattice level `m`, the number of terms `N`, the coefficients `c` and the
  representatives `a` are all chosen after `f` and before the point `x`. They
  may depend on `p`, `F`, `T` and `f`, but not on `x`.
- There is one common level `m` for every term. Each term is the indicator of a
  single coset `a i + T.additiveLattice m`, written as the set of `z` with
  `z - a i ∈ T.additiveLattice m`; the indicator takes the value `1 : ℂ` on the
  coset and `0` off it.
- The identity is pointwise at every `x : F.Carrier` for the original function
  `f`. It is not an almost-everywhere statement and involves no measure.
- `N = 0` is allowed; the empty sum is `0`, which covers the zero function.
- The coefficients are arbitrary complex numbers. The statement does not
  require the cosets to be distinct or disjoint, and does not require the
  coefficients to be values of `f`. A proof may supply such stronger data, but
  only this direct identity is asserted.

The only properties of `f` available are those bundled in `SchwartzBruhat`:
local constancy and compact support. No common lattice of invariance, support
bound or finite coset partition is a hypothesis. No Haar measure, additive
character, Fourier transform or alternative test-function definition occurs.

## The lattice convention

`T.additiveLattice m` is the published additive subgroup
`{x | T.discreteValuation x ≤ WithZero.exp m}` from
[Conductor](Conductor.md), in the namespace
`Langlands.PadicField.TopologicalData`. Its published API identifies it with the
fractional ideal `π^(-m) O` for the chosen uniformizer `π = T.uniformizer` and
the integer ring `O = T.Integers`
(`mem_additiveLattice_iff_div_mem_integers`), shows that level `0` is `O`
(`mem_additiveLattice_zero`), and shows that the lattices increase with `m`
(`additiveLattice_mono`). Thus a small lattice has a very negative level, and
`exists_additiveLattice_subset` shows that every neighborhood of zero in the
supplied topology contains one of these lattices.

## Relation to the existing finite expansion theorem

`Langlands.HarmonicAnalysis.exists_compactCosetExpansion` in
[CompactCosetExpansion](CompactCosetExpansion.md) assumes a family invariant
under one supplied compact open additive subgroup and supported in one compact
set. Its Schwartz functions are indicators of whole fibers of that family; it
does not say that each is the indicator of a single coset, and it does not prove
that an arbitrary test function is invariant under a common lattice. The present
proposition assumes neither invariance nor a support bound and asks for
single-coset indicators of a valuation lattice. That theorem can contribute to a
proof only within its actual scope, after a common invariance lattice and a
support lattice have been derived.

## Original source and derivation

- André Weil, *Basic Number Theory*, second edition, Springer, 1973.
  Registered source `weil-1973-basic-number-theory`; retained file
  `/home/taskhub/central-library/Weil--Basic number theory (book, 2nd edition)--1973.pdf`,
  SHA-256 `32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`
  (verified on 2026-10-27).
  - Chapter VII §2, Definition 1, printed p.106 / PDF p.123: a standard function
    on a finite-dimensional vector space `E` over a p-field `K` is a
    complex-valued locally constant function with compact support. This is the
    `SchwartzBruhat` space for `E = K = F.Carrier`.
  - Chapter VII §2, Proposition 2 and its proof, printed p.107 / PDF p.124: a
    function is standard if and only if there are `K`-lattices `L ⊃ M` such that
    it vanishes outside `L` and is constant on cosets modulo `M` in `L`. The proof
    observes that `L` is the union of finitely many cosets `e_i + M`, on each of
    which the function is constant, which gives
    `Φ = ∑ i, Φ(e_i) · 1_{e_i + M}`.
  - Chapter II §2, Definition 2 and the preceding paragraph, printed p.28 /
    PDF p.45: a `K`-lattice is a compact open `R`-module, and in `K` itself every
    nonzero `R`-module other than `K` is one of the sets `P^n`. Hence for `E = K`
    the lattice `M` is `P^n = π^n O`, which is `T.additiveLattice (-n)`.

Worker 739 read PDF pp.123–125 and the Chapter II §2 lattice definition on
PDF p.45, and visually inspected PDF p.124. The proposition is a derived internal statement:
it records only the finite single-level coset expansion implicit in Weil's proof
of Proposition 2, for `E = F.Carrier`, and drops the outer lattice `L` and the
Fourier-transform half of that proposition. It is not quoted verbatim. No
errata for Weil's book was found in the project literature index or the public
notes (checked on 2026-10-27).

## Consumer and remaining proof obligation

This prerequisite was split by Worker 688 from task
`2be3a65c-9439-43c6-be52-368dd3a8bf98`, whose target is
`Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsStatement` in
[PadicSelfDualMeasureExistsStatement](PadicSelfDualMeasureExistsStatement.md).
This proposition neither proves nor assumes self-dual measure existence.

A future proof must establish the proposition from local constancy and compact
support in the supplied topology. One possible route: local constancy and
compactness of the support give a common lattice `T.additiveLattice m` under
whose translations `f` is invariant, using `exists_additiveLattice_subset`;
compact support gives a larger lattice containing the support; the quotient of
the larger lattice by the smaller one is finite, and coset representatives with
the sampled values `f (a i)` give the expansion. This route is a suggestion and
is not implemented or assumed. Compilation checks only that the declaration is a
well-formed proposition; it does not establish the mathematical claim.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
