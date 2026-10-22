# Uncentered special blocks

Worker 17 authored this construction over a field, group, and explicitly
supplied unit-valued norm character. It imports
`Langlands.WeilDeligne.SumsTensor` for the actual pair tensor product.

`Special.action` acts on the actual coordinate space `Fin m → K` by
`r(g)(v)(j) = nu(g)^j v(j)`. `Special.raising` shifts the standard basis
upward: its coordinate at zero is zero, and its coordinate at positive
`j` is the input coordinate at `j-1`. The monoid laws are proved
coordinatewise. `raising_pow_apply_eq_zero` tracks the vanishing bottom
coordinates after each power, proving that exponent `m` annihilates
monodromy. `Special.covariance` uses the adjacent weights and inverse
character cancellation to prove `r(g) N r(g^-1) = nu(g) N`.

`specialBlock nu m` bundles this actual pair, with rank `m`; rank zero is
permitted internally. `block nu A m` is the tensor of the zero-monodromy
representation `A` with this special block. It constructs a specified
block and makes no assertion that an arbitrary pair decomposes into
such blocks. `Special.raising_eq_zero_iff` identifies the vanishing lower coordinates,
and `Special.ker_raising` proves equality of the kernel with the span of
`Special.topVector`. The action on that vector is `nu^n` in rank `n+1`.
`raising_basisVector` proves the shift on every non-top basis vector,
`raising_topVector` proves termination, and `raising_ne_zero` certifies
nonzero monodromy in every rank at least two. The rank of `block nu A m`
is `rank A * m`. `ker_specialBlock` and
`specialBlock_monodromy_ne_zero` expose these facts for the actual pair.
`block_monodromy_tmul` shows that monodromy acts only on the special factor;
`blockEquiv` and `blockClass` prove descent in the Weil factor through
genuine equivalences and isomorphism classes.

`BlockDatum` retains a specified finite representation and a positive
length; `BlockDatum.pair` constructs its actual pair. Irreducibility of
the Weil factor is a separate predicate and subtype, so general blocks
are not silently required to be irreducible. No classification,
uniqueness, or existence of decomposition data is assumed.

Source correspondence: Tate, *Number theoretic background*, Corvallis
Part II, printed page 20, §4.1.4 defines the uncentered block with basis
weights `nu^j`, raising monodromy, and top-weight kernel; §4.1.5 gives
the tensor monodromy used for `block`. Source ID
`tate-1979-number-theoretic-background`, retained Part II PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The coefficient-field generality and coordinate implementation are
derived from those formulas. All intrinsic algebraic certificates
are supplied as proofs, not additional input hypotheses.

In the eventual local specialization, geometric Frobenius has degree
`+1` and `nu(Phi)=q^-1`. This module assumes neither an actual local
Weil group nor any numerical value for the supplied character. It
does not change the uncentered weights or select a half-norm twist.

Henniart (2002), §2.3, printed page 594, uses the corresponding
positive-length block data, and §2.4 uses the top weight `nu^(n-1)`
in its L-factor. The primary coordinate construction here is Tate's
explicit basis formula. The classification and uniqueness assertions
of Henniart §§2.2--2.3 are later theorems, not fields of `BlockDatum`.
Source ID `henniart-2002-characterization`, retained PDF SHA-256
`40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.

## Included sum and tensor module

`Langlands.WeilDeligne.SumsTensor` is included in this contribution.
It constructs actual pair sums and tensor products, proves nilpotence
and covariance, and supplies bifunctors, equivalences and genuine class
operations. Its paired Markdown explains the commuting-nilpotent argument
and exact tensor monodromy formula used by the block constructor here.
