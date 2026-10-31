# Critical norm approximation after bounded unramified base change

`Langlands.LocalClassField.primeCriticalNormAfterUnramifiedBaseChange`
proves exactly
`Langlands.LocalClassField.PrimeCriticalNormAfterUnramifiedBaseChange.{u}`.
The common universe is arbitrary. For every prime-degree totally ramified
finite Galois extension `E/F`, the theorem chooses its actual lower break
`t`, with `0 < t` if and only if the degree `ell` equals the residue
characteristic `p`. For every `z` in the canonical `U_F^t`, it supplies an
unramified Galois `K/F` of degree at most `ell`, the actual compositum
`M = E K`, its inclusion maps and arithmetic properties, the same lower
break for `M/K`, and `y` in `U_M^t` such that
`image(z) / N_{M/K}(y)` belongs to `U_K^(t+1)`.

This is a proof of the focused critical approximation statement.
The full norm equation for an arbitrary field unit additionally needs
exact higher-unit norm correction and reduction to the critical
filtration. Those are separate obligations of
`PrimeRamifiedNormReduction` and the parent
`PrimeNormAfterUnramifiedBaseChange`.

The route implements the critical step isolated by the statement.
Its original-source provenance is recorded in that statement's paired
Markdown. The proof below uses the actual published arithmetic and
coordinate constructions; it introduces no new source assertion.

## Choosing the critical polynomial

`primeTotallyRamifiedBreak` chooses `t` before the unit `z`.
When `0 < t`, `primeRamifiedGradedNorm` supplies integers `a,b` whose
field values are the literal quotients
`N_{E/F}(piE)^t / piF^t` and `Tr_{E/F}(piE^t) / piF^t`, for the
canonical uniformizers. The residue of `a` is nonzero.
When `t = 0`, the proof instead sets `a = 1` and `b = 0`.

Let `c` be the residue of the literal `t`-th unit coefficient of `z`
at positive `t`, and the residue unit underlying `z` at zero.
`normTraceResiduePolynomial` constructs
`residue(a) X^ell + residue(b) X - c`.
Its exact natural degree is `ell`, by the nonzero leading residue and
primality, which implies `1 < ell`. Applying
`residuePolynomialUnramifiedLift` gives the actual unramified Galois
`K/F` with the required degree bound, and a root `w` in its residue
field. Polynomial evaluation gives
`r(a) w^ell + r(b) w = r(c)`, where `r` is the actual relative residue
map. This argument uses equality of formal polynomials and their
literal coefficients.

## One compositum and transported coefficients

`totalUnramifiedCompositum_coefficientTransport` supplies one `M`,
the equality `M.field = E.field ⊔ K.field`, and inclusion proofs
`hE,hK`. Its degree, ramification, Galoisness, norm, trace and order
conclusions all concern those same witnesses. The proof installs the
actual inclusion algebras and their scalar towers, and obtains total
ramification of `M/K`. `primeBreakUnramifiedBaseChange` preserves the
chosen actual break `t` for this compositum.

The images of the two original uniformizers still have order one,
by the supplied order identities. Applying
`primeRamifiedGradedNorm` to `M/K` with those images gives the literal
coefficients `aK,bK`. Subtype extensionality and the coefficient
transport identities identify them with the images of `a,b` under
the actual relative integer map. The `K`-to-`M` residue map is
injective, as retained in the graded norm theorem.

## Lifting a critical unit and removing its graded error

For `0 < t`, `positiveUnitCoordinate_surjective` lifts the image of
`w` in the residue field of `M` to `y` in `U_M^t`.
The graded containment puts its actual determinant norm in `U_K^t`.
The critical graded formula identifies the norm coordinate, after
the injective residue map, with the polynomial expression at `w`.
The identity `ell = p` follows from the chosen positive break and
changes the exponent in that expression. The root equation and
`residue_unitCoefficient_relativeUnitFiltrationMap` then equate the
norm coordinate and the coordinate of the actual image of `z`.

The private lemma `positiveCoordinate_div_mem` applies the additive
unit-coordinate homomorphism, expressed with `Multiplicative`, to
the quotient of two filtration elements with equal coordinates.
Its value is one; the published kernel identity puts the quotient
in `U_K^(t+1)`. This gives exactly the requested error term.

For `t = 0`, the root equation becomes `w^ell = r(c)`. The target
is the image of a residue unit and is nonzero, so `w` is nonzero.
The proof therefore forms a residue unit from `w` and uses
`zeroUnitCoordinate_surjective` to lift its image to `y` in `U_M^0`.
The level-zero graded norm formula is the `ell`-th power formula
on residue units. The root equation, injectivity of the residue
map and `zeroUnitCoordinate_relativeUnitFiltrationMap` equate the
two multiplicative coordinates. The private lemma
`zeroCoordinate_div_mem` uses their homomorphism and its kernel
`U_K^1` to obtain the same required quotient conclusion.

All norms are the actual determinant norms on field units, and all
relative integer, residue and unit maps come from the actual field
inclusions. No additional outer hypothesis is imposed.

Authored by Worker 27.
