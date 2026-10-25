# Positive-root unitary cuspidal support of product-Levi discrete series

`Langlands.GLDiscreteSeriesPositiveRootSupportStatement.{uF,uV}` is a closed
proposition definition. It states the fine-to-middle support step used on
Silberger 1978, p.99, for actual standard product Levis of GL_n. This file
provides no proof of that proposition or of any analytic comparison below.

## Scope and analytic hypothesis

The statement quantifies over every prime `p`, p-adic field
`F : PadicField.{uF} p`, supplied compatible local-field realization
`T : F.TopologicalData`, positive natural rank `n`, ordered block shape
`D : BlockShape n`, and actual complex representation
`σ : Rep.{uV} ℂ (D.Levi F.Carrier)`. The group `D.Levi F.Carrier` is the
product of the general linear groups of the block sizes of `D`.

The only representation hypotheses are irreducibility of `σ.ρ` and
`RelativeRegularComparison.IsLeviSquareIntegrable T D σ`. The latter uses
`T`'s topology and the actual quotient of the whole product Levi by its full
center. It quantifies over every measurable structure making that quotient a
Borel space and every Borel Haar measure on it. For each such measure,
`IsSquareIntegrableModCenter` requires admissibility and a smooth unitary
scalar central character whose descended absolute matrix coefficients lie in
`MemLp ... 2` for every smooth-dual functional and every representation vector.
Admissibility includes smoothness. No separate chosen central character,
tensor presentation, critical exponent, opposite embedding, or quotient map
is supplied. In particular, this is not a condition on the quotient by only
the diagonal center of the surrounding GL_n.

## Actual support data and map

The conclusion supplies an actual `R : BlockRefinement D`, a fine
representation `ω` of `C.Levi F.Carrier` for `C = D.flatten R`, and a real
vector `v₀ : Fin C.length → ℝ`. It requires that `ω.ρ` be irreducible,
`CuspidalSupport.IsLeviCuspidal C ω.ρ`, and `IsUnitarizable ω.ρ`.
Cuspidality means admissibility and vanishing of the actual unipotent
coinvariants for every proper standard refinement of `C`. Unitarizability
means existence of an invariant positive definite Hermitian form; no norm,
topology, completion, or finite-dimensionality condition on the carrier is
an input.

The subgroup `refinedParabolic F.Carrier D R` is the product, inside
`D.Levi F.Carrier`, of the upper block parabolics specified by `R i`.
Its actual Levi subgroup is `refinedLevi F.Carrier D R`. The constructed
`flattenedLeviEquiv F.Carrier D R` identifies `C.Levi F.Carrier` with this
subgroup. These are existing constructions, not additional certificates or
arbitrary group equivalences.

`RelativeJacquetMultiplicity.fineTwist T D R ω v₀ 0` first twists `ω` on
the flattened Levi by

`∏ k |det(m_k)|^(-v₀(k))`

and then pulls the action back along the inverse of `flattenedLeviEquiv`.
The coarse real parameter is the zero function, so the definition's general
exponent `-v₀(k) + t(parent(k))` is exactly `-v₀(k)` here. The absolute value
is the residue-normalized `q^(-valuation)`.

`RelativeJacquetMultiplicity.innerInduced T D R` applies the existing
`T.normalizedRefinedInduced`: inflate through the actual refined Levi
projection, multiply the covariance by the positive half modulus, and use
smooth induction with right translation on functions. The conclusion supplies
an actual complex-linear intertwiner `q` from this representation to the
original `σ.ρ`, together with `Function.Surjective q`. It asserts a quotient,
without a section, a Langlands head, or any uniqueness assertion.

## Strict root cone and universes

The required `RelativeRegularComparison.IsPositiveRootParameter D R v₀`
is reused unchanged. In a block `i` of `D`, write the fine sizes as
`d₀,...,d_(r-1)`. There is a strictly positive real coefficient `c_j` for
**every** adjacent scalar root, and the restriction of `v₀` to this block is

`∑ j < r-1, c_j * (e_j / d_j - e_(j+1) / d_(j+1))`.

The coordinates are transported to the flattened index set by
`D.flattenBlockEquiv R`. The reciprocal sizes convert scalar-block roots to
determinant exponents, since `|det(z I_d)|^a = |z|^(d*a)`. This expansion has
zero size-weighted sum in each original block. It is a positive-root cone,
not a condition that the entries themselves be positive or strictly ordered.
Nonnegative coefficients would weaken the specified cone. An unrefined block
has `r = 1`: the root sum is empty, and its parameter is zero. Such blocks,
including a wholly unrefined Levi, are allowed.

The field and original representation universes `uF` and `uV` are independent.
The existential fine representation has carrier in `Type (max uF uV)`.
Its twist has the same carrier universe, and its induced carrier also lies in
`Type (max uF uV)`. The surjective intertwiner targets the given carrier in
`Type uV`; no equality of these universes or cardinality restriction is
assumed. This universe allowance supports actual quotient and induction
constructions without prescribing a small representative in advance.

## Originals and derived provenance

The direct source is A. J. Silberger, *The Langlands Quotient Theorem for
p-adic Groups*, Math. Ann. 236 (1978), 95–104 (S78), especially the proof setup
for Proposition 5.1 on p.99. There the middle discrete-series representation
is a quotient of induction from a unitary cuspidal representation with a
positive-root parameter. The preceding support step, from discrete series
to tempered representations, is a different assertion. S78 p.96 fixes the
positive-half-modulus normalization; its source twist `+i v₀` on p.99
corresponds to the negative determinant exponent used here.

The retained S78 original is
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`,
registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Worker 125 read pp.96 and 99 (PDF pp.2 and 5), checking the p.99 formula image.

S78 cites A. J. Silberger, *Introduction to Harmonic Analysis on Reductive
p-adic Groups* (1979) (S79), Corollary 2.4.2 and Theorem 4.4.4 for this step.
The retained original is
`/home/taskhub/central-library/Silberger--Introduction to harmonic analysis on reductive p-adic groups (book)--1979.pdf`,
registered as `silberger-1979-harmonic-analysis`, SHA256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
Worker 125 read section 2.4 through Corollary 2.4.2, printed pp.90–92
(PDF pp.96–98), and Theorem 4.4.4 with its proof, printed pp.177–180
(PDF pp.183–186), checking all these page images. No relevant retained errata
file was found in the project notes.

This is a derived GL product-Levi specialization of the S78 support step,
not a literal restatement of either S79 result. Corollary 2.4.2 starts with a
critical pair and exponent and embeds the original representation in
**opposite** normalized induction from irreducible admissible
J-supercuspidal data. It does not itself assert the required upper quotient
or unitarity of the cuspidal data. Theorem 4.4.4 concerns coefficient functions
integrable on bounded central strips; clause (4) says that their real
exponent plus a strictly positive combination of simple roots lies in the
central dual. It does not directly assert this Lean modulo-center hypothesis
or an induction map.

## Proof obligations

A future proof must justify the GL product-Levi specialization and each
comparison needed to realize the S78 support step with these actual objects:

- Extract suitable cuspidal support without assuming a critical exponent or
  a support map. Relate J-supercuspidality to the actual admissible
  coinvariant-vanishing predicate used here.
- Compare analytic square-integrability for all Haar measures on the full
  central quotient with the bounded-central-strip coefficient condition,
  and identify coefficient exponents with the appropriate normalized
  Jacquet exponents. Apply the strict exponent criterion with the correct
  scalar-root coordinates.
- Separate the real unramified part of the cuspidal central character and
  realize the remaining cuspidal representation by an invariant positive
  definite form. A unitary central character alone is not the definition of
  `IsUnitarizable`.
- Use the unitary central character of the square-integrable input to remove
  the remaining real central direction in each block of `D`, so the final
  parameter lies in the stated root span with zero size-weighted block sums.
  This removal is an argument to prove, not an extra central-character premise.
- Supply the normalized opposite/upper and smooth-duality transports needed
  to obtain a surjection onto the original `σ`. This includes the actual
  modulus factors, parabolic conjugations or block reversals when used,
  contragredient inversion of twists, admissible biduality, and the analytic
  properties needed for any dual input. An embedding into opposite induction
  cannot simply be relabeled as a quotient of upper induction.
- Transport the data and maps through the constructed flattened-Levi
  equivalence and realize them in the permitted carrier universes. A proof
  using tensor factorization must also establish the necessary analytic
  tensor comparisons and recover the given product-Levi representation.

No item in this list is proved by this statement module. Regular Langlands
classification, tempered exhaustion, square-integrable Langlands
classification, and the desired support quotient are not premises. The joint
fine/middle/coarse assembly and the head conclusion of
`GLRelativeRegularComparisonStatement` remain separate work.
