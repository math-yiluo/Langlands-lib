# Points of nonzero strict affinoid spectra

The theorem `spectrumNonempty` proves the entire published proposition
`SpectrumNonemptyStatement K`. It splits according to
whether every scalar has norm at most one.

In the trivial-valuation case, multiplicativity and the norm bound on the inverse
show that a nonzero scalar has norm at least one. A Tate series of norm less than
one therefore has every coefficient zero. The quotient's arbitrarily close
representatives then show that every nonzero quotient element has norm at least
one. For any actual prime ideal, pull back the trivial multiplicative seminorm
on its quotient domain. It takes values zero and one, so the preceding lower
bound proves the required bound by the quotient norm. An actual maximal ideal
exists in the nonzero affinoid and supplies such a prime ideal. This construction
does not need a norm or closedness on the prime quotient.

Otherwise choose a scalar of norm greater than one. If the spectrum were empty,
the spectral power-bound theorem would apply vacuously to its scalar image.
The norm formula for a normed algebra identifies the norms of its powers with
the scalar's geometric powers times the positive norm of one. These powers
are unbounded, giving a contradiction.

This route derives nonemptiness without a finite residue-field construction.
The source behind the target is the maximal-ideal inclusion immediately before
Proposition 2.5.6, page 9 of the retained fourteen-page notes of part of
Berkovich's course, *Affinoid algebras* (registered
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`).
The implemented route instead uses the spectral power-bound theorem, whose
provenance is Proposition 2.6.5 on page 12. Both the target and the spectral
power-bound proof are imported unchanged from the Library.

The two trivial-valuation helpers are more general than the closing theorem:
`one_le_norm_of_scalar_norm_le_one` and
`primePoint_of_scalar_norm_le_one` do not require completeness of the scalar
field. The latter takes an actual prime ideal and does not assume a spectrum
point or maximal-ideal realization.

The Lean proof and this explanation were authored by Worker 56.
