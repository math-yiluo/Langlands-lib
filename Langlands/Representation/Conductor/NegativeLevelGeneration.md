# Elementary generation at a negative Jacquet level

This module constructs the two concrete Jacquet groups used at a negative
level, proves that they generate every elementary root subgroup and contain
the determinant-one subgroup, and proves the resulting Whittaker vanishing
obstruction. All declarations are in `Langlands.Conductor`.

The source is Jacquet–Piatetski-Shapiro–Shalika, *Conducteur des
représentations du groupe linéaire* (1981), Section 5.2, printed page 211,
and Section 5.3, printed page 213; registered source
`jpss-1981-conductor`, SHA256
`986b06d6c16221fd55f04480604a1b17bf11004a704ab16b78acdd131ae6d49d`.
The group constructions follow its displayed matrices. The generation and
vanishing proofs below are direct algebraic derivations.

## Concrete groups and conventions

Let `F : Type uF` be a field, let `O` be a subring of `F`, and let the
matrix rank be `n + 1`. The definitions do not require a valuation or topology.
For `q : Fˣ`, `jacquetRowDilation n q` is the actual diagonal matrix
`D = diag(1,...,1,q)` in the field general linear group.
`fieldJacquetMirabolic O n` is
`integralSubgroup O n ⊓ mirabolic n F`. Thus its matrices have block form
`[[h,u],[0,1]]`, with `h` invertible over `O` and `u` integral. This is the
field realization of the source's `H(0)`.

`scaledOppositeJacquetMirabolic O n q` consists of the matrices `g` for
which `D*g*D⁻¹` belongs to
`integralSubgroup O n ⊓ oppositeMirabolic n F`. In block coordinates these
are `[[h,0],[v,1]]`, with `h` invertible over `O` and `q*v` integral.
The definition uses subgroup comap under the actual conjugation
automorphism, so both the matrix and inverse integrality conditions are
retained. The private `dilation_conjugate_lowerRoot` verifies the scaling
on the lower root elements used in the proof.

For a uniformizer `ϖ` and an integer `a < 0`, take `q = ϖ^(-a)`, regarded
as a field unit. Then `q⁻¹ O = ϖ^a O`, and the second group is the source's
transpose of `H(a)`. JPSS uses plain transpose here. For a subgroup the
transpose image equals the inverse-transpose image because inversion
preserves the subgroup; no Weyl conjugation is involved.
`jacquetNegativeGenerated O n q` is the subgroup supremum of these two
groups, meaning the ordinary generated subgroup without a topological
closure.

## Generation results

The generation theorems assume `[ValuativeRel F]`,
`[ValuativeRel.IsRankLeOne F]`, and `v(q) < 1`, where
`v = ValuativeRel.valuation F` and `O = v.integer`. They do not require
local compactness, discreteness, characteristic zero, or a topology.

`exists_integral_power_multiple` proves that, for every `c : F`, there is
`k : ℕ` with `(q*q)^k*c ∈ O`. The zero case is immediate; otherwise the
proof uses the multiplicative Archimedean property of the rank-at-most-one
value group and `exists_pow_lt₀` to make `v(q*q)^k` smaller than `v(c)⁻¹`.

`upperRoot_mem_jacquetNegativeGenerated` and
`lowerRoot_mem_jacquetNegativeGenerated` prove membership of
`I + c E_(i,last)` and `I + c E_(last,i)` for every `i ≠ last` and
every field coefficient `c`. For the upper roots, integral upper roots
and lower roots with `q*c ∈ O` first give the root Weyl elements at `q`
and `-1`. Their product is the determinant-one root diagonal with entries
`q,q⁻¹`. The imported root-diagonal conjugation formula scales an upper
coefficient by `q²`. Repeated inverse conjugation therefore takes the
integral coefficient `(q²)^k*c` to the desired `c`. Once all upper roots
are available, the proof repeats this construction with the two
coordinates reversed to obtain all lower roots.

`transvection_mem_jacquetNegativeGenerated` obtains every root
`I + c E_(i,j)` with `i ≠ j`. Roots meeting the final coordinate are the
preceding cases. For two other coordinates the private matrix calculation
uses the product
`U_(i,last)(c) U_(last,j)(1) U_(i,last)(-c) U_(last,j)(-1) = U_(i,j)(c)`.

For `0 < n`, `det_ker_le_jacquetNegativeGenerated` proves containment of
the actual kernel of `Matrix.GeneralLinearGroup.det : GL_(n+1)(F) →* Fˣ`.
The proof identifies it with the image of `SL_(n+1)(F)` and applies
Mathlib's `SpecialLinearGroup.diagonal_transvection_induction'`.
Transvections belong by the preceding theorem; the diagonal generators
are identified with the imported `rootDiagonal`, a product of root
elements already in the generated subgroup.

## Whittaker vanishing

`whittaker_eq_zero_of_negativeLevel_invariant` additionally assumes
`[TopologicalSpace F]`, `0 < n`, a bundled nontrivial unitary additive
character `ψ`, and an element `W` of the actual standard-character
equivariant function submodule on `GL_(n+1)(F)`. Its two hypotheses are
global right invariance under the two concrete groups: for every element
`h` of either group and every `g`, `W(g*h) = W(g)`. The conclusion is
`W = 0`. No smoothness, representation irreducibility, essential-vector
identity, or epsilon-factor hypothesis is used.

The proof forms the right stabilizer subgroup of `W`; it contains the
generated subgroup and hence every determinant-one matrix. Nontriviality
of `ψ` supplies `c` with `ψ.complex(c) ≠ 1`. A private adjacent upper root
`u = I + c E_(i,i+1)` has determinant one and standard Whittaker character
`ψ.complex(c)`, as verified by the sum of its simple-root entries.
For every `g`, the conjugate `g⁻¹*u*g` has determinant one, so right
invariance gives `W(u*g) = W(g)`. Left Whittaker equivariance gives
`W(u*g) = ψ.complex(c)*W(g)`. Cancellation forces `W(g) = 0`.

## Source correction and remaining obligations

The printed Section 5.3 says that the two groups generate the full field
general linear group when the level is negative. That assertion is too
strong: the displayed groups have integral-unit determinants, and
conjugation preserves determinant. The implemented replacement is the
determinant-one containment and the Whittaker obstruction proved above;
it makes no claim of full general linear group generation.

This is an auxiliary group construction and vanishing unit. To use it in
the conductor theorem one must still derive the two invariances for a
nonzero Whittaker function from the actual analytic identities, and relate
the scaling parameter to the epsilon exponent. The module proves neither
those analytic identities nor essential-vector existence, the minimal
fixed level, fixed-space dimension, or an L- or epsilon-factor comparison.
The published `EssentialConductorStatement` and its import closure are
unchanged.
