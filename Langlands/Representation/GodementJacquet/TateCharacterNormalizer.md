# Actual scalar character normalization

For every prime `p`, every `F : PadicField.{uF} p`, every supplied
`T : F.TopologicalData` and every continuous quasicharacter `χ` of the actual
multiplicative group, `scalarMellin_character_isNormalizedGenerator` proves
that `PadicAbelian.lPolynomial T χ` is the normalized generator of the Laurent
span of `scalarMellinRationalValues` with weight one. The actual integrand is
`Φ(a) χ(a) |a|^s`; the multiplicative Haar measure gives integral units mass
one. The topology, valuation, conductor and normalized absolute value all
come from the supplied `T`.

`characterIntegerRingTest` constructs the genuine Schwartz–Bruhat indicator
of the valuation integer ring. The integer ring is clopen, and compactness is
the local-field compact closed-ball theorem at radius one.
`characterIntegerRingTest_shell` proves that its actual integral-unit shell
coefficient is `χ(π)^n` for nonnegative integers `n` and zero for negative
`n`, for every specified order-one element `π`, when the conductor is zero.
The order of `π^n u` is `n` for an integral unit `u`. Integer-ring membership
is therefore equivalent to nonnegative `n`. The character is trivial on
integral units and their multiplicative Haar mass is one.

`characterIntegerRingTest_tsum` sums those exact coefficients on
`‖χ(π) z‖ < 1`. The published bilateral-sum splitting theorem with both
cutoffs zero removes the negative terms and leaves the ordinary geometric
series. Its sum is `(1 - χ(π) z)⁻¹`.
`characterIntegerRingTest_continuation` then uses the actual shell integral
identity from `finiteFunctionShellSeries`. Its bound `B` and the nonzero
character value give a positive radius
`min(1/B, 1/‖χ(π)‖)`. Since the residue cardinality is greater than one,
`spectralPoint q s = q^(-s)` lies in this radius on a right half-plane.
The elementary complex-power identity identifies `|a|^s` with
`(q^(-s))^(ord a)`. Thus the actual Mellin integral equals the geometric
reciprocal there. Uniformizer independence identifies its denominator with
the specified abelian Euler polynomial. The norm bound excludes its zeros,
and `regular_and_eval_div` gives both the reduced rational denominator guard
and the expected evaluation. This proves the existing guarded
`HasRationalContinuation` predicate, without relying on evaluation at poles.

`exists_scalarMellinIntegral_one` treats every continuous character, without
a conductor premise. Intersect the open character kernel with the compact
open integral-unit group. This intersection is compact and open. Its image
in the field under the open embedding of units is compact and open, and
hence defines a genuine Schwartz–Bruhat characteristic function. Divide
that test by the positive finite multiplicative Haar mass of the subgroup.
The character and absolute-value weight are one on its support, so the
actual integrand is the normalized subgroup indicator. It is integrable and
has integral one for every complex parameter.
`one_mem_scalarMellinRationalValues` records that one is attained before
taking any Laurent span.

`rationalLFactor_mem_scalarMellinRationalValues` combines the conductor
branches. In conductor zero, the integer-ring test attains the reciprocal
Euler polynomial by the continuation just proved. In nonzero conductor,
that polynomial is one, so the normalized compact-open test attains its
reciprocal. Finally, `isNormalizedGenerator_iff` applies: the polynomial has
constant term one; `scalarMellin_character_denominator` clears every actual
rational value; and the attained reciprocal belongs to their Laurent span.
This establishes the full normalized-generator assertion for these scalar
character integrals.

This is an internal derivation from the Library's actual test functions,
character conductor, normalized Haar measures, shell formulas, geometric
series and Laurent-module criterion. The compact-open normalization proof
specializes `MatrixUnitValueProof`, authored by Worker 704. The public
complex-power and spectral-threshold helpers are reused from the published
`TateCharacterDenominator` arguments of Workers 357 and 656, retaining
Worker 235's attribution for the elementary complex-power argument. The
separately reviewed shell and denominator results retain their statements and proofs;
the denominator helpers are now public for this reuse.

The result proves scalar normalized generation. It does not assert a JPSS
pair-factor comparison, an epsilon-factor comparison, full abelian Tate
local analysis, or the closed supercuspidal correspondence.

The identical helper proofs are reused from `Langlands.Representation.GodementJacquet.TateCharacterDenominator`; their local copies have been removed.
