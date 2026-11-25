# Polynomial coordinates for section jets over a commutative ring

The namespace `Algebra.SectionJet.Coordinates` works with an arbitrary
commutative base ring `k`, a commutative `k`-algebra `A`, and an augmentation
`ε : A →ₐ[k] k`. Write `I = ker ε` and `J = idealOfVars σ k`. The ring, algebra,
and index type have independent universes. Fix a basis
`b : Module.Basis σ k I.Cotangent`, and lifts `z : σ → A` satisfying
`ε (z s) = 0` and `AugmentedAlgebra.classMap ε (z s) = b s`.
No finiteness assumption is imposed on this basis.

The definition `truncEval z hz N` is the algebra map
`k[σ]/J^N → A/I^N` induced by actual evaluation at `z`.
`truncEval_mk` computes it on every polynomial representative.
`quotientMap_aeval_surjective` proves that it is surjective without
formal smoothness. Under `Algebra.FormallySmooth k A`,
`quotientMap_aeval_injective` proves injectivity.
`exists_truncated_section` packages its inverse composed with the quotient
map from `A`: if `x - aeval z p ∈ I^N`, its value on `x` is the class of `p`.
The assertions include `N = 0`, where both quotient rings are zero rings.

The definition `jetEquiv z b hz hzb n` is the resulting actual algebra
isomorphism

`k[σ]/J^(n+1) ≃ₐ[k] Algebra.SectionJet.Quotient ε n`.

Its forward map is evaluation, as recorded by `jetEquiv_mk`.
`truncate_jetEquiv` states that on each polynomial representative it
commutes with the actual section-jet truncation from order `n+1` to `n`.
The definition `monomialBasis` transports Mathlib's bounded-support
monomial basis through `quotientIdealOfVarsPowEquiv` and `jetEquiv`.
Its indices are the finitely supported exponent vectors of total degree
at most `n`. The theorem `exists_basis_lifts` proves that every specified
cotangent basis has such lifts by surjectivity of `I.toCotangent`.
The coordinates depend on those chosen lifts.

The implemented proof first expands an element of `I` in the cotangent
basis, giving an approximation modulo `I²`. Induction on ideal powers,
using ideal-product induction and multiplication of approximations,
gives polynomial approximation modulo every `I^N` and hence
surjectivity. For injectivity, `exists_lift_of_cotangent` constructs the
first-order algebra map given by the augmentation plus a linear
cotangent map with square-zero image. Formal smoothness lifts it through
a nilpotent ideal. Applied to the truncated polynomial ring, this gives
a map `ψ` that sends `z s` to the variable `X s` modulo the square of the
variable ideal and sends `I` into that variable ideal. Thus `ψ` kills
`I^N`. The existing nilpotent polynomial-substitution lemma
`TorusUnipotence.mem_pow_of_eq_zero` shows that a polynomial whose
evaluation lies in `I^N` must lie in `J^N`. This proves injectivity.
The helper `mem_pow_of_map_eq_zero` records the corresponding kernel
criterion for any such first-order map.

This is an internal generalization of the approximation and lifting
parts of the Library's
`Langlands.GroupScheme.Rational.TorusUnipotence.TruncatedSection`, which
assumes a field. Here the ring-generic augmentation class map from
`CoordinateCotangentDualityProof` replaces its field-specific cotangent
map; the polynomial-substitution lemma in `Truncation` already works
over a commutative ring. No external theorem is asserted as the source
of these interfaces. No finite type, noetherian, field, or fixed finite
rank hypothesis is added. This module supplies local algebra coordinates;
it does not construct sheaf gluing, higher symmetric-power comparisons,
a determinant-power formula, or ampleness.
