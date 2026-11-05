# Compact-picture compression families of the actual standard operator

Author: Worker 1615.

This module is a supporting construction for the host task proving
`Langlands.Plancherel.ConditionalParabolicIntertwiningStatement`. It connects
the published compact picture of actual Levi-normalized unramified induction
with the truncation and compression identities of
`StandardIntertwiningTruncation`. It then applies the regular stable-limit
principle of `UnramifiedStableLimit`. Its main theorem is
`exists_regular_compactIdentityValue_numerator`.

Fix the following data:

- an admissible smooth representation `A` of the closed Levi `M`;
- a compact open `K` with the published Iwasawa hypotheses;
- a compact open subgroup `H ≤ K`;
- an explicit `Jacquet.IsIwahoriContraction H U' M O a` for a second radical
  `U'` normalized by `M`;
- any set `Ω` of unramified parameters at which the actual standard-integral
  domain is the whole source.

Then there is one nonzero element `b` of the concrete regular algebra
`unramifiedRegularFunctions ν` such that, for every compact section fixed by
`H`, `χ ↦ b(χ) •` (the value at the identity of the actual standard integral)
is a finite expansion with regular coefficients on `Ω`. The scalar `b` is
chosen before the section. It may depend on `H`, so uniformity over all
compact sections is not claimed.

## General helpers

- `averageMap_eq_finiteMean_cosets`: the published compact average of a vector
  equals the finite mean over cosets of any subgroup `L` of the averaging group
  that fixes the vector. The published `Compact.finiteMean_comp` is applied to
  the equivariant map from cosets onto the orbit.
- `averageMap_apply_subgroup'`: the compact average is invariant under the
  averaging subgroup, because both orbits are equal.
- `isPolynomialOn_pi`, `IsPolynomialOn.const_smul`, `isPolynomialOn_end_of_apply`:
  closure of the published polynomial-family predicate under finite products,
  constant multiples, and passage from all vectors to the endomorphism family
  of a finite-dimensional space. The last one expands an endomorphism in a
  basis through `coord j` and `smulRight`.

## Fixed compact-picture vectors

`compactPictureAction` is the published right action of `K` on the compact
picture. `unramifiedLeviInductionCompactEquiv_translate` shows that the
published restriction equivalence intertwines right translation by `K` at
every parameter. `CompactFixedVectors h K A H` consists of the compact sections
fixed by `H ∩ K`. For `H ≤ K`, `compactFixedEquiv χ` identifies it with the
`H`-fixed vectors of the actual induction at the parameter `χ`.

`eval_mem_fixedVectors_leviConj` shows that the value of a fixed section at
`x ∈ K` is fixed by `M ∩ x H x⁻¹`, using the actual covariance and
`projection_levi`. Together with the injective evaluation at coset
representatives (`compactFixedEval`, `compactFixedEval_injective`), this gives
`finiteDimensional_compactFixedVectors` from admissibility.
`isPolynomialOn_compactFixed_of_eval` states that a family of fixed sections is
polynomial when each value is polynomial. The proof descends through the
injective evaluation map with the published
`isPolynomialOn_of_linearMap_injective`.

## The compression family

`compactCompression χ` transports the published
`Jacquet.compressedAction … H hH a` of the actual induction at `χ` to the
fixed compact picture. `compressionStabilizer H a` is the subgroup
`{x ∈ H | a⁻¹ x a ∈ H}`, which has finite index (`finite_compressionStabilizer`).
`eval_compactCompression` expresses each value of the compression as the
finite mean over its cosets of values of the actual covariant extension at
`k x a`. These values are polynomial in the parameter by the published
`unramifiedCompactExtension_eval_isPolynomialOn`. Hence
`isPolynomialOn_compactCompression` holds: the compression is a polynomial
endomorphism family on the finite-dimensional fixed compact picture.

## The dual side

`leviPartOpen H` is `H ∩ M` as an open subgroup of `M`, and `LeviFixedDual A H`
is the space of algebraic functionals fixed by it.

- `unramified_eq_one_of_mem_compact`: an unramified character is `1` on Levi
  elements of `K`. This is the published
  `unramifiedPullback_eq_one_of_mem_conjOpenSubgroup`.
- `leviFixedDualSmooth`: Levi-fixed functionals are smooth functionals of
  every unramified twist.
- `finiteDimensional_leviFixedDual`: restriction to the finite-dimensional
  fixed vectors is injective, by averaging over the compact group `H ∩ M`.
  This uses closedness of `M`.
- `leviDualShift`: the contragredient action of a Levi element normalizing
  `H ∩ M`, restricted to Levi-fixed functionals. A constant times an
  evaluation times it is a polynomial family (`isPolynomialOn_leviDualShift`).
- `leviFixedPairing_injective`: Levi-fixed functionals separate Levi-fixed
  vectors. An arbitrary algebraic functional composed with the compact
  average is Levi-fixed.

## Forms, parameter independence and convergence

`compactIdentityValue χ hfull` is the linear map sending a compact section to
the published `operator` of its extension, evaluated at the identity.
`compactLimitForm` pairs it with Levi-fixed functionals.
`compactTruncationForm χ₁` is the truncation of
`StandardIntertwiningTruncation` over `compactRadicalPiece U' H` at one
parameter `χ₁` of full convergence, paired with Levi-fixed functionals. Its
additivity in the functional uses integrability on the actual domain
(`truncatedIntegral_add_functional'`).

`truncatedIntegral_compactRadicalPiece_eq` proves that on the compact radical
piece the truncated integrand of a compact section does not depend on the
parameter. Every point there has a representative in `H ⊆ K`, where the
covariant extension takes the compact-picture value (published
`unramifiedLeviInductionCompactEquiv_eval`).

`compactDualShift χ` is the inverse Levi factor times `χ(a⁻¹)` times the Levi
dual shift of the contracting element. It is a polynomial family
(`isPolynomialOn_compactDualShift`). It corresponds to the published
`dualCompressionShift` of the twisted representation
(`leviFixedDualSmooth_compactDualShift` and its power version). Powers of the
compact compression correspond to powers of the actual compression
(`compactFixedEquiv_compactCompression_pow`).

`tendsto_compactTruncationForm`: for every parameter `χ` of full convergence,
`compactTruncationForm χ₁ (Tⁿ w) (Sⁿ y)` tends to `compactLimitForm χ w y`,
where `T` is the compression and `S` the dual shift at `χ`. The proof first
replaces `χ₁` by `χ` using parameter independence. It then transports both
iterates and applies `tendsto_compressedTruncation` from
`StandardIntertwiningTruncation`.

## Levi-fixed identity values

`exists_pos_leviShiftFactor_eq` writes the actual Levi factor as a positive real
number. This uses the published formula `complexCharacter_apply` for the
half-character and positivity of the quotient-conjugation modulus.

`compactIdentityValue_mem_fixedVectors`: the identity value `x` of a fixed
section is fixed by `H ∩ M`. For `m ∈ H ∩ M`, the published `operator_levi_mul`
and `operator_preserves_stabilizer` give `x = r • A(m) x` with `r > 0`. Here the
twist acts trivially, by `unramified_eq_one_of_mem_compact`. Smoothness of `A`
gives an open subgroup fixing `x`. The published Mathlib lemma
`Subgroup.exists_pow_mem_of_relIndex_ne_zero`, applied in the compact group
`H ∩ M`, gives `n > 0` with `mⁿ` in that subgroup. If `x ≠ 0` this forces
`r⁻ⁿ = 1`, hence `r = 1`.

## The regular numerator theorem

`exists_regular_compactIdentityValue_numerator` applies the published
`exists_regular_bilinear_stableLimit_numerator` to the compression family `T`
on the fixed compact picture and the dual shift family `S` on Levi-fixed
functionals. Both spaces are finite-dimensional. If `Ω` is empty the claim is
vacuous. Otherwise one parameter `χ₁ ∈ Ω` defines the starting form. The
resulting `b ≠ 0` makes `χ ↦ b(χ) •` (the limit form) polynomial. Evaluating at
a section, the Levi-fixedness of identity values and the injective pairing then
descend this to the identity values in `A`.

## Scope and provenance

The module does not construct the compact subgroup, the contracting element or
the Iwahori contraction for the host's radicals. It does not make `b`
independent of `H`, treat values at points of `K` other than the identity, or
treat sections not fixed by `H`. It also does not prove full convergence,
domination, local divisibility of the denominator or the host theorem. These
remain separate obligations. All steps are internal compositions of the
published Library declarations named above, of `StandardIntertwiningTruncation`
and of `UnramifiedStableLimit`. No literature theorem replaces a proof.
Waldspurger 2003, IV.1, printed pp.280–282, proves rationality by a
Jacquet-module filtration instead; that route is not used.
