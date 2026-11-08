# Integrated weighted minuscule translation

This internal unit integrates the weighted inverse minuscule quotient integrand
identity using the actual Jacquet quotient measure. It then constructs the
restricted action on actual finite-support model vectors and proves equivariance
of their numerator map.

The field `F` is an arbitrary nonarchimedean local field with its valuative
relation and topology. The representation `π` of `GL_(n+2)(F)` on a complex
vector space is smooth and has a specified Whittaker functional `ℓ` for the
unitary additive character `ψ`. No irreducibility or nonzero-functional
hypothesis is needed. The smaller group and its upper unipotent subgroup have
measurable structures with their Borel-space instances. The actual unipotent
quotients in rank `n+1` and rank one have measurable structures.

The normalization `h : IsJacquetNormalization q ψ abv ϖ μ` supplies the residue
cardinality, a uniformizing unit `ϖ`, absolute-value normalization, integer
conductor of `ψ`, compatibility of the actual quotient measure with the group
and unipotent Haar measures, and Borel-space instances on both quotients.
The uniformizing condition means `v(ϖ) < 1` and realization of every nonzero
field valuation as an integer power of `v(ϖ)`. The absolute value has
`abv(ϖ) = q⁻¹` and value one on valuation units. Integer conductor means
triviality on the integers and that any `x` with `ψ(x*y) = 1` for every
integral `y` is itself integral.

The finite-sum results retain the following explicit data and hypotheses:

- `q > 0` and a finite label type `Λ` with cardinality `q`;
- integral lifts `σ : Λ → F`, distinct modulo the maximal ideal
  (`v(σ x - σ y) < 1` implies `x = y`), covering all integral residues
  (for every integral `z`, some `x` has `v(z - σ x) < 1`);
- for each adjacent root, an `x` with `v(x) v(ϖ) ≤ 1` on which the inverse
  standard unipotent character has value different from one.

Here `v` is `ValuativeRel.valuation F`. These residue-lift and root witnesses
are supplied explicitly rather than constructed in this unit. The field,
representation-space and label-type universes are independent.

Let `T_k` be the actual weighted inverse minuscule model operator defined in
`SphericalMinusculeTranslation`, and let `C_k` be
`symmetricTorusHeckeScalar n q k`, namely
`sqrt(q)^(k*(n+1-k))` times the elementary symmetric Laurent polynomial `e_k`.
For every actual model vector `w` and integer `d`, the proved coefficient identity
is `coefficient(T_k w,d) = C_k * coefficient(w,d-k)`.

The proof first uses complex linearity to expand the finite sum of translated
vectors. Every evaluated degree integrand is integrable by smoothness. Each
representative's right translation preserves the actual quotient measure, so
a separate change of variables puts all integrals into the form used by
`sum_degreeCorankOnePolynomialIntegrand_inverseTranslate`. Integrability permits
the finite sum to pass through the integral. Unit-tuple evaluation separates
elements of the symmetric Laurent algebra and proves the coefficient identity
in that algebra.

Coefficientwise equality then gives
`series(T_k w) = single(k,C_k) * series(w)`. For every complex polynomial `P`,
associativity gives the same identity for the product with the coordinate
denominator constructed from `P`. A monomial shifts support and can remove
coefficients, so this identity preserves finiteness of the actual support.

`corankOneFiniteSupportMinusculeTranslate` is the resulting complex linear
endomorphism of `corankOneFiniteSupportModelVectors h π hπ ℓ P`. It applies the
actual model operator and proves its output has finite denominator product;
it does not enlarge the vector space or replace it by an algebraic closure.
The numerator, which sums the finitely many actual coefficients, satisfies
`numerator(T_k w) = C_k * numerator(w)`. This is also stated as equivariance of
`corankOneModelNumeratorLinearMap` on the restricted endomorphism.

Taking the image of this actual numerator map proves stability under `C_k`.
Since `q > 0`, its square-root power normalization is nonzero; complex linearity
absorbs its inverse and proves stability under every `e_k`. The conclusions
hold for all natural `k` and all `P`, and assume finite support only when a
numerator is formed.

The provenance is internal: this unit combines the actual quotient-integrand
identity, smooth-model integrability, right-invariance of the compatible Jacquet
measure, linearity of the established coefficient construction and finite
coefficient reindexing under monomial multiplication. It does not prove that
all model vectors have finite denominator product, supply a standard
L-polynomial, or prove essential-vector existence or conductor conclusions.
