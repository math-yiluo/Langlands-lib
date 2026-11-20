# Frobenius comparison for the Harris CM tower

`CMHarrisKottwitzTraceComparisonStatement` isolates the comparison needed at
Kottwitz (1992), §5. It uses the hypotheses of
`CMHarrisKottwitzLambdaAdicStatement`, including the division hypothesis, the
reflex field condition, the absolute irreducibility hypotheses, the central
weight convention, and admissibility. The level, coefficient system and
cohomology are the Library's actual Harris CM constructions. The statement
retains the two derived-category universes `wS` and `wR`.

## Degreewise comparison and virtual polynomial

`CMHarrisKottwitzFrobeniusComparison` relates a family `H` of polynomials over
`K_λ` to the actual geometric Frobenius action at a place `v` of `F`. In degrees
`0` through `2(n − 1)` the level cohomology is unramified at `v`. Given the
fixed-vector comparison in degree `i`, the actual
`cmHarrisLambdaTowerHeckeMultiplicity` in that degree is finite-dimensional
and `H i` is the characteristic polynomial of the chosen geometric Frobenius
lift on it. The lift uses the completion at `v` and the chosen embedding of
algebraic closures. The polynomial can later be used with the continuous
`cmHarrisLambdaHeckeMultiplicityObjects` via the published Euler polynomial
transport theorem.

`CMHarrisKottwitzVirtualIdentity` requires monic polynomials at a complex
realization, whose degree-`i` roots are Weil numbers of weight `i + w` for the
residue cardinality at `v`. Its equation is the signed product of those
polynomials in the field of rational functions, equal to `P^a` at the same
embedding of `K`. The input `H` over `K_λ` is mapped along a field embedding
`j : K_λ →+* ℂ`, and `P` is mapped along the restriction of `j` to `K`.

## Quantifiers and source

One integer `a` and one finite set `S` of exceptional rational primes serve
all coefficient places. For each coefficient place, the first clause gives
an auxiliary place of `F` away from the coefficient prime, with the
comparison and the virtual identity for a monic polynomial of positive
degree. If the signed multiplicity vanishes, the identity has right side `1`
and a polynomial such as `X` suffices. If the signed multiplicity is nonzero,
the source supplies a positive-degree unramified polynomial at an auxiliary
good place. The same clause gives vanishing of the actual multiplicity above
`2(n − 1)` under the fixed-vector comparison in the degree in question. These
are inputs for deducing the nonzero-occurrence criterion by weight separation.

At each prime outside `S` satisfying the unramifiedness, chart, level and
local-component hypotheses of the target, nonzero `a` gives spherical
irreducibility. At each `vθ` the comparison uses the polynomial `P` in
`IsKottwitzPolynomial` for the given chart, component and square root. A
coefficient place away from the rational prime, with Mathlib's standard
derived categories, supplies the complex comparison for this `P`. This
witness supplies the purity calculation for the factorization over `K`,
which is required before the target quantifies over the other derived-category
instances. The comparison with the actual cohomology for every allowed
coefficient place is stated at the target's two universes, with a fixed-vector
hypothesis in the degree used.

The comparison is a derived formulation of the original paper. Section 1,
printed pp. 654–657, gives the Hecke projection, the exceptional primes, the
normalization of `P` and the signed integer. Lemma 4.2, pp. 660–661, gives
automorphic support when the signed integer is nonzero. The first paragraph
of §5, p. 661, uses the smooth projective integral model, extension of the
coefficient sheaf, smooth proper specialization and Deligne purity. Equations
(5.1)–(5.5), pp. 661–663, compare the Hecke-projected geometric traces to the
local parameter, and (5.6), p. 663, gives their virtual characteristic
rational function. The alternating product and its degree range are displayed
in (6.1), p. 664.

To prove this formulation, compare the canonical model for Kottwitz's
`(G, [h₀⁻¹])` with `cmSchemeTower` after transporting the reflex field by
`Φ τ₁`. The comparison with the smooth projective hyperspecial PEL model
must identify its generic fibre and Hecke correspondences with the Harris
tower. The coefficient sheaf `F_ξ` must be identified with the tower's
`cmHarrisGeometricCoefficientSystem` built from torsion on the universal
abelian scheme, after passing to the Library's `λ`-adic cohomology. The
specialization and purity arguments then apply to the action used in
`CMHarrisKottwitzFrobeniusComparison`. The trace comparison at chart places
must also identify the local parameter normalization in §5 with
`IsKottwitzPolynomial`. The virtual identity is stated before degree
separation, so the occurrence criterion, pure factors over `K` and the
individual `|a|`-power identities remain to be deduced.

R. E. Kottwitz, *On the λ-adic representations associated to some simple
Shimura varieties*, Invent. Math. 108 (1992), pp. 653–665. Registered source
`kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.
