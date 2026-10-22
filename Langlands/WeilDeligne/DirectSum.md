# Finite direct sums of Weil–Deligne pairs

Worker 17 authored this construction module. It imports
`Langlands.WeilDeligne.Parameters` and `Langlands.Weil.Representation.DirectSum`.

For a family `A : ι → WeilDeligneRepresentation K G ν` indexed by a finite
type, `directSum A` is the actual pair on `⨁ i, A i`. Its Weil action is
the componentwise direct sum of the underlying representations, and its
monodromy is the componentwise operator
`DirectSum.lmap (fun i => (A i).monodromy)` (`directSum_monodromy`). The
norm character `ν` is shared by all summands. The empty family gives the
rank-zero pair, and nonzero monodromy is allowed.

The constructor proves its two intrinsic certificates.

- Nilpotence: choose exponents `n_i` with `N_i^(n_i) = 0`. Componentwise
  powers (`lmap_pow`) and `n_i ≤ ∑ j, n_j` give
  `(⨁ N_i)^(∑ j, n_j) = ⨁ N_i^(∑ j, n_j) = 0`.
- Covariance: componentwise products and scalar multiples (`lmap_mul`,
  `lmap_smul`) reduce `r(g) N r(g⁻¹) = ν(g) N` to the covariance of each
  summand.

The auxiliary lemmas `lmap_mul`, `lmap_pow`, `lmap_smul` and `lmap_zero`
state these componentwise identities for `DirectSum.lmap` on
endomorphisms.

`directSumMap` sums a family of pair morphisms, with the monodromy square
checked componentwise. `directSumFunctor` is the functor on finite
families, `directSumEquiv` transports families of genuine equivalences,
and `rank_directSum` gives `rank (⨁ A_i) = ∑ rank A_i`. `directSumClass`
acts on finite families of genuine pair classes through Mathlib's
`Quotient.finChoice`, and `directSumClass_classOf` computes it on
representatives.

For complex coefficients over a topological group, `parameterDirectSum`
and `parameterDirectSumClass` give open-inertia parameter objects and
genuine parameter classes, using the representation-level open-kernel
certificate. No Frobenius-semisimplicity, usual-continuity or
semisimplicity preservation is asserted.

This module does not import the special-block constructor, which is a
separate contribution. Applied to a finite family of specified blocks
`ρ_i ⊗ S_{n_i}`, `directSum` gives the actual pair of the form
`⨁_{i∈I} ρ_i ⊗ Sp(n_i)`. No decomposition, existence or uniqueness
assertion is made; those are statement targets elsewhere.

## Source correspondence

Henniart, *Une caractérisation de la correspondance de Langlands locale
pour GL(n)* (2002), §2.2, printed page 593 (PDF page 7): every
representation of `W'_F` is a direct sum `⨁_{i∈I} σ_i` of indecomposables
over a finite set `I`; §2.3, printed page 594 (PDF page 8), identifies the
indecomposables as `ρ ⊗ St_n`. Tate, *Number theoretic background*,
Corvallis Part II, §4.1.2, printed page 20 (PDF page 29), gives the pair
convention `r(w) N r(w)^-1 = ‖w‖ N`, and §4.1.5 on the same page
describes the Φ-semisimple indecomposables as `ρ ⊗ sp(n)`. Source IDs
`henniart-2002-characterization` (SHA-256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`) and
`tate-1979-number-theoretic-background` (SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`). The
componentwise pair structure, nilpotence exponent and the map, functor
and quotient obligations are derived and proved here.

## Included representation module

This contribution also includes `Langlands.Weil.Representation.DirectSum`,
with paired Markdown. It constructs the finite direct sum of actual
finite-dimensional representations on `⨁ i, A i`, with componentwise
intertwiners, functor, equivalences, rank formula, class operation and the
open-inertia certificate used by the parameter version here.
