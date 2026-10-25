# Conditional bounds for actual mirabolic restrictions

This internal adapter connects the finite-length functional argument to the
actual mirabolic subgroup and to the spectral normalization needed by
`EqualRankTrilinearAssembly`. It leaves both mirabolic finite length and
irreducible-pair rigidity as explicit hypotheses. It does not prove the parent
trilinear uniqueness statement.

`shiftedSpectralExceptions q hq u E` is the image of the finite set `E` under
multiplication by the inverse of `spectralPoint q u`. The published
`spectralShiftUnit` supplies its nonzeroness for `1 < q`.
`not_mem_of_not_mem_shiftedSpectralExceptions` uses
`spectralPoint q (s + u) = spectralPoint q u * spectralPoint q s` to show that
avoiding this image implies that the translated parameter avoids `E`.
`exists_finite_exception_shift` applies this to an arbitrary proposition-valued
predicate of the complex parameter. The new finite set is chosen before the
parameter.

`mirabolic_exists_exception_length_le_one` takes smooth representations of
`GeneralLinear (n + 1) F.Carrier`, with independent carrier universes and the
supplied topology `T`. For each representation it assumes that its full
functional space for a specified upper-unipotent character is linearly
equivalent to the complex numbers, and that its actual restriction to
`mirabolic n F.Carrier` has finite group-algebra length. The two characters may
differ. In the intended application they are the standard and inverse standard
characters.

The remaining premise controls each pair of smooth irreducible mirabolic
representations, without an admissibility assumption on those representations.
Outside a finite set of spectral points chosen for the pair, nonzero length
of the full twisted bilinear space forces both transported character functionals
to exist; when they both exist that bilinear space has length at most one.
The covariance is `determinantWeight (normalizedAbsoluteValue T) g.val (-s)`.
The conclusion bounds the full bilinear space for the two original restricted
representations by one outside a single finite exceptional set. Here length
means extended-natural complex module length, so infinite-dimensional spaces
are not mistaken for zero-dimensional ones.

The proof transports the full functional spaces using
`Whittaker.mirabolicFunctionalsEquiv`, transfers smoothness along the subgroup
inclusion, and obtains nonzero functionals from the supplied linear
equivalences. Smoothness and those nonzero functionals imply local constancy of
the two scalar characters. Actual upper-unipotent compact containment is
provided by `Mirabolic.upperUnipotent_isLimitOfCompactSubgroups`. These facts
discharge all ancillary hypotheses of the finite-length bilinear bound.
That theorem chooses actual composition filtrations and takes the finite union
over their graded-position pairs. No classification or finite-length theorem
is supplied by this adapter.

`mirabolic_shift_length_bound` translates the parameter by `-1`, turning the
weight `-s` into `1 - s`. It uses the generic exception-set translation and
`T.residueCardinality_gt_one`. This yields precisely the bound required by the
Frobenius input in `EqualRankTrilinearAssembly`. It makes no assertion that the
Frobenius equivalence itself exists.

The provenance is internal specialization of the functional, filtration and
spectral-translation lemmas cited by Lean name above. The rank-one case is
retained without an additional positivity hypothesis on `n`. The functional
equivalences are strong enough to exclude zero source representations; the
separate trilinear assembly still allows zero coefficient models arising from
zero chosen functionals. All substantive representation-theoretic premises
remain visible and unproved here.
