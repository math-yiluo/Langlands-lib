# Assembly of compact equal-rank JPSS test data

Author: Worker 408.

This internal helper identifies the actual equal-rank integrand with the
indicator of an explicitly defined subset of the actual left-unipotent
quotient. It proves a conditional assembly step; it does not construct the
mirabolic tests, lift them to coefficient vectors, or prove the parent
`EqualRankUnitValueStatement`.

## Objects and exact hypotheses

For every field with a supplied topology and every rank `n+1`, including
rank one, let `P` be the existing actual mirabolic matrix subgroup, `N` the
existing upper-unipotent subgroup, and `q` the published left quotient map.
For a set `C` in `P` and a subgroup `J` in the actual general linear group,
`equalRankCompactSet C J` is exactly `q '' (C_ambient * J)`, where
`C_ambient` is the image of `C` under the subtype inclusion. It is not a
subgroup assertion. No subgroup is assumed to normalize another.

The proposition definition `IsEqualRankCompactTest` records six sufficient
conditions on actual Whittaker functions `W`, `W'` and a Schwartz--Bruhat
function `Phi`:

1. On `P`, their product is exactly the indicator of `q '' C_ambient`,
   evaluated at the coset of the argument.
2. Their product is right invariant under `J`.
3. `Phi` is exactly the indicator of `lastRow '' J` on the full row space.
4. Membership of `lastRow g` in that row set is equivalent to an actual
   factorization `g=p*j`, with `p` in `P` and `j` in `J`.
5. The supplied determinant absolute value is one on `C`.
6. It is one on `J`.

These are explicit hypotheses, not new existence results. The predicate is
for the integral assembly step and does not replace the separate shared
mirabolic test-function interface. In particular compactness and openness
are not hidden in its name: they are assumptions of separate topological
lemmas. The absolute value and all measures remain supplied.

## Implemented proof

The quotient set contains `q '' J` if `C` contains the identity. If `C` and
`J` are compact, their ambient product is compact and so is its continuous
quotient image. If `J` is open, the ambient product is a union of left
translates of `J`, hence open; the existing open quotient map gives openness
of the quotient image. These topological claims require a topological ring
structure on the field; the algebraic assembly does not.

`IsEqualRankCompactTest.integrand_eq` proves that the existing
`equalRankIntegrand` is the indicator of `equalRankCompactSet C J` for every
complex spectral parameter. On that quotient set, use a representative
`c*j`. Right invariance reduces the product to its value at `c`, which is
one. The row factorization makes the Schwartz factor one. Multiplicativity
of determinant and absolute value makes the spectral weight one.

Outside the quotient set, the Schwartz factor is zero unless a representative
has a factorization `p*j`. For such a factorization, the coset of `p` cannot
lie in `q '' C_ambient`: otherwise the algebraic right-coset relation for
that coset identity would place the original coset in the thickened quotient
set. The calculation is `(p*j)*(c*j)⁻¹ = p*c⁻¹`; it uses no continuity
assumption. The mirabolic product hypothesis and right invariance therefore
make the product zero. This argument never assumes a unique factorization
or a normality relation between compact subgroups.

`integral_eq` integrates the indicator to the complex image of the real
quotient mass. It is an identity for the total Bochner integral, including
its usual zero convention if the indicator is not integrable. The separate
`converges` theorem assumes a measurable set with finite mass and proves
absolute convergence for these particular tests at every parameter.

Finally `one_mem_equalRankRationalValues_of_compact_test` applies this
calculation to vectors in the two specified actual coefficient images.
Measurability and positive finite quotient mass are explicit hypotheses.
Their real mass is then nonzero, so the published scalar-normalization
helper rescales the first vector inside its fixed coefficient image. The
same Schwartz function and fixed vectors give constant integral one and
hence literal membership of rational one in the existing rational-value
set. The two representation carrier universes are independent. No
irreducibility, general analyticity, or scalar central action is used.

## Provenance and remaining obligations

This is an internal deduction from the existing actual quotient integrand,
actual mirabolic subgroup, open quotient map, Bochner indicator integration,
and `EqualRankUnitNormalization`. It implements an alternative final assembly
of the test data used in JPSS (1983), printed page 393. The source context is
explained in the paired `EqualRankUnitValueStatement` documentation; the
present quotient-thickening proof is an internal derivation and is not
attributed as a theorem stated verbatim in that paper.

The opposite compact mirabolic functions, their Kirillov lifts for every
supplied topology, an exact row-orbit Schwartz indicator, a common right
stabilizer in determinant norm one, and positivity of the resulting quotient
volume remain necessary inputs. In particular this module does not prove
any of their existence statements or the final parent theorem. Its candidate
must be reviewed as conditional infrastructure, not as a proof of
`EqualRankUnitValueStatement`.
