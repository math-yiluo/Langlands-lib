# Finite projective dimension over regular local rings

`Langlands.CommutativeAlgebra.RegularLocalFiniteProjectiveDimensionStatement.{u}`
is the proposition

```lean
∀ (R : Type u) [CommRing R], IsRegularLocalRing R →
  ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    ∃ n : ℕ, CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) n
```

Thus every finitely generated module over every regular local commutative ring
has finite projective dimension. The ring and module occupy the same arbitrary
universe `u`. The Lean file defines this proposition and supplies no proof.

## Source and scope

The original source is the Stacks Project, Proposition 10.110.1
([Tag 00O7](https://stacks.math.columbia.edu/tag/00O7)), first sentence. It gives
a finite free resolution of a finite module over a regular local ring. A finite
free resolution is a finite projective resolution, so the proposition here is
its consequence asserting existence of a finite projective dimension. The
statement discards the depth-dependent bound and does not assert that the
resolution has been constructed. Proposition 10.110.5
([Tag 00OC](https://stacks.math.columbia.edu/tag/00OC)), implication (3) to (2),
also implies this proposition.

Both complete pages are retained in registered source
`stacks-regular-local-homological-2026-11-01`, in files `00O7.html` and
`00OC.html`. The source directory SHA-256 is
`21820755db776b97fc099941b898e15c3b34a12ac214b637216d74b85046b6fd`.
The two historical comments on `00O7.html` concern a reference for the final
global-dimension assertion, which was corrected. This statement uses only its
finite-module assertion. `00OC.html` has no comments. There is no separate
project errata note for this source.

## Lean conventions

`IsRegularLocalRing R` is Mathlib's class extending locality and Noetherianity
and expressing equality of embedding dimension and Krull dimension.
`Module.Finite R M` means that the top submodule of `M` is finitely generated.
`ModuleCat.of R M` is the module as an object of `ModuleCat.{u} R`.
`CategoryTheory.HasProjectiveDimensionLE X n` is Mathlib's categorical notion
that `X` has projective dimension at most the natural number `n`. Its category
universe here is `u+1`; the same-universe specialization needs no explicit
`Small` hypothesis.

The bound may depend on `M`. The proposition adds no premise about a dimension,
field, characteristic, domain, completeness, global dimension or projective
dimension. The regularity hypothesis is explicit, while module finiteness is
an instance binder. The zero module is included.

This interface is shared by the proof that regularity is preserved by prime
localization and the proof of vanishing of the Picard group after inverting
one element. Neither consumer's conclusion is an assumption of this statement.
