# Weyl factorization from opposite-cell contractions

This internal reduction defines `HasNormalizerProductContractions i ν`.
For each actual normalizing rational point `n` and each point of `U(χ)`,
where `χ` is the image of `ν`, its contraction must factor through the
product of `U(-ψ)` and `P(ψ)` with `ψ = Int(n)χ`. This is an explicit
geometric input, not an unconditional existence assertion.

The module shows that this input gives `HasUnipotentWeylFactorization i ν`,
provided opposite-cell multiplication is injective on all test schemes for
each torus cocharacter and `Z(χ)` is the whole-torus centralizer.
The normalizer action expresses `ψ` as another cocharacter of the same
commutative group. The common-group normalization lemmas and contraction
splitting then produce `u = a b` with both factors in `U(χ)`, the first in
`U(-ψ)` and the second in `P(ψ)`.

The whole-torus centralizer is preserved by normalizing points on every
test scheme. Dynamic centralizer functoriality therefore identifies
`Z(ψ)` with `Z(χ)`. The mixed-limit theorem upgrades the second factor
to `U(ψ)`. Conjugation by `n` is then undone to give precisely
`n⁻¹ a n ∈ U(-χ)` and `n⁻¹ b n ∈ U(χ)`.

The next helper combines this factorization with the all-test
normalizer-intersection theorem to establish
`HasUnipotentNormalizerSeparation`. The final helper reuses the published
unipotent covering-and-separation assembly. Its conclusion is the actual
`HasRationalBruhatDecomposition i ν` with `P(k)` double cosets and the
actual quotient `N(k)/Z(k)`. It retains four inputs: the centralizer
identity, unipotent covering, all-test opposite-cell injectivity for each
cocharacter, and the product-contraction condition.

The first centralizer-transport lemmas hold over an arbitrary base scheme.
The factorization theorem uses an arbitrary field in universe `u`, an
affine ambient group and a commutative source group, with the displayed
geometric inputs. It assumes no splitness, root cardinality, field size,
smoothness or reductivity. The eventual reductive application must still
establish these inputs and the covering and minimal-parabolic assertions
required for the exact rational Bruhat theorem.

The provenance is internal composition of the existing normalizer action,
all-test torus-centralizer normalization, dynamic functoriality,
`Dynamic.NormalizedLimits` and `Dynamic.OppositeCellContraction`.
