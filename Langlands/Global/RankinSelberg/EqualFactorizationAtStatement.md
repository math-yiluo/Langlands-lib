# Equal-rank partial Whittaker factorization at one number field

Module `Langlands.Global.RankinSelberg.EqualFactorizationAtStatement`, namespace
`Langlands.Global.RankinSelbergGlobal`. All five declarations return `Prop`, with independent
universes `u` for number fields and `uQ` for the spectral presentations. They are companions
to the unrestricted statements, which are unchanged.

## The two bodies at `F`

`EqualArchimedeanFactorizationAt F` is the body of
[`EqualArchimedeanFactorizationStatement`](ArchimedeanFactorizationStatement.md) after its
field and instance binders. `EqualPointwiseFactorizationAt F` is the body of
[`EqualPointwiseFactorizationStatement`](EqualArchimedeanFactorizationReduction.md) after its
same binders. Both take `F : Type u` with `[Field F]`, `[NumberField F]` and
`[CompactSpace (AdeleQuotient F)]`. Quantifying either body over those binders gives the
corresponding original proposition by definitional equality.

Both bodies quantify over an adelic additive character trivial on the diagonal field, every
rank `r + 1` (including rank one), two cuspidal realizations and their contragredients,
spectral presentations with irreducible admissible local components, and a finite set `S`
containing the exceptional sets and supporting the finite additive character. They retain
all hypotheses on the real and complex additive components and parameters, and on the
canonical finite additive characters and their self-dual measures.

Both give vectors spherical outside `S` and a Schwartz–Bruhat function `Φ` standard outside
`S`. The local data comprise real and complex Whittaker restrictions, Schwartz functions and
quotient measures, and `EqualLocalTestData` for the actual finite components at `S` with the
canonical topologies. Both require the two exact row-function product formulas: `Φ` is the
product of these local Schwartz factors with the integrality indicator outside `S`, and its
positive-sign global Fourier transform `Φhat` is the product of their local Fourier transforms
with the same indicator. Neither formula has a scalar prefactor. The local Fourier transforms
use the given characters and their self-dual measures.

- The integrated body asks for the two partial global integral identities on one right
  half-plane, for the ordinary data and for the dual Whittaker functions with `Φhat`. Each
  integral is the product of the archimedean integrals and the local integrals at `S`, times
  the same nonzero constant `c`.
- The pointwise body instead gives, for every complex `s` and every integral quotient class,
  the ordinary and dual integrand products at that class's projections, with one nonzero
  constant `κ` for both identities. For each `v : S` and `s`, the finite factors `fS v s` and
  `gS v s` integrate to the ordinary and dual test integrals of `D v` against the published
  `equalPadicQuotientMeasure`. It does not assert the two global integral identities.

In both bodies the two archimedean products, and each ordinary and dual integral at each
`v : S`, have a nonzero value in every right half-plane. These assertions may choose different
arguments `s`. The group-scheme smoothness and affineness instances and the archimedean and
rectangular measurable-space instances used to elaborate the bodies are local to this module
and agree with the choices in the source definitions.

## Totally complex fields and integration

`EqualArchimedeanFactorizationTCStatement` and `EqualPointwiseFactorizationTCStatement` close
the corresponding body over `F` and its instances with `[NumberField.IsTotallyComplex F]`
inserted after `[NumberField F]`. In these two statements the subtype of real places is empty:
`IsTotallyComplex.isComplex` and `InfinitePlace.not_isReal_iff_isComplex` exclude each real
place. Thus the real-place families in the bodies have no entries, their place-specific
conditions are vacuous, and their products are one. The complex-place tests, finite-place
conditions, and both row-function product formulas remain.

`EqualArchimedeanFactorizationAtReductionStatement` says that at each number field `F` with
compact `AdeleQuotient F`, `EqualPointwiseFactorizationAt F` implies
`EqualArchimedeanFactorizationAt F`. It does not assume pointwise factorization at every field.
The published `equalArchimedeanFactorizationReduction` uses its pointwise hypothesis only at
its current field `F`. Its two integrations use the same quotient-product measure identity,
now available as `UnipotentClass.unipotentClassProductStatement` in
[`UnipotentClassProductProof`](UnipotentClassProductProof.md). The separate rectangular Tate
identity used for unequal ranks is not an input of the equal-rank integration argument. The
same-field target itself does not require total complexity and can be applied to the
pointwise TC wrapper at any totally complex `F`.

## Source and proof boundary

J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in J. Bernstein and S. Gelbart
(eds.), *An Introduction to the Langlands Program*, Birkhäuser, 2004, pp. 197–228,
`cogdell-2004-analytic-theory-gln`, proof of Theorem 4.1, printed pp. 219–220 (PDF pp. 222–223).
Page 219 gives the equal-rank product with suitable cuspidal vectors and a Schwartz function;
p. 220 treats the ordinary and dual products for the functional equation, explicitly leaving
the equal-rank case analogous. The Library separates the infinite places from the finite set
`S` and states the precise normalizations and test data in the two parent propositions. The
single-field quantifiers, the totally complex wrappers, and the integration target are
derived Library interfaces, not separately numbered theorems in Cogdell.

This module states the propositions only. It does not prove the slice comparison, the local
tests, the pointwise or integrated factorization, the integration implication, or any
functional equation. The unrestricted equal-rank work in Task 7397 remains unchanged.
