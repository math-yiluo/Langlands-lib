# Unitarity under normalized mirabolic Phi-minus

Worker 596. This module states
`Langlands.Derivative.MirabolicPhiMinusUnitarity.{uF, uV} F T`.
It is a Prop-valued definition, with no proof or assumed result.

Fix a p-adic field `F : PadicField.{uF} p` and its supplied topological data
`T`. For every nontrivial unitary additive character `ψ`, every `n : ℕ`,
and every actual smooth complex representation `X` of `P_(n+2)`, the
statement says that unitarizability of `X` implies unitarizability of
normalized `Φ⁻ X` on `P_(n+1)`. The carrier universe is
`Type (max uF uV)`, with independent `uF` and `uV`. There is no
irreducibility, admissibility, finite-length or homogeneity hypothesis.
The zero output is allowed: the Library's positive-definite-form definition
also applies to the zero vector space.

The Library calls `P_(n+1)` `GeneralLinear.Mirabolic.mirabolic n F.Carrier`.
`Mirabolic.phiMinus T ψ n` first takes the actual twisted coinvariant
quotient by the radical of `P_(n+2)`, then twists its descended
`P_(n+1)` action by `|det|^(-1/2)`. This is the normalized functor of
Bernstein §9.2, not the unnormalized twisted quotient.
`IsUnitarizable` means existence of an invariant positive definite
Hermitian form on the actual carrier.

The source is J. N. Bernstein, *P-invariant distributions on GL(N) and the
classification of unitary representations of GL(N) (non-archimedean case)*,
LNM 1041 (1984), §9.2, printed pp.95–96, and §9.3(ii), printed p.97.
The registered source is `bernstein-1984-p-invariant`, SHA-256
`b050423087ee36592c4747ba6f3c9a9fdef9c8e4b8919e3737cf7ecdfcc94ab2`,
at
`/home/taskhub/central-library/Bernstein--P-invariant distributions on GL(N) and the classification of unitary representations of GL(N) (Non-archimedean case)--1983.pdf`.
PDF page indices are printed pages minus 49. The rendered p.97 was checked.
No source errata entry was found in the public notes.

This is a derived consequence of the source's form correspondence, rather
than the whole criterion of §9.1. In §9.2 the open-orbit section space
`E₀` is a subrepresentation of `X`; the fiber at a nonzero character is
normalized `Φ⁻ X`. In §9.3(ii), invariant Hermitian forms on that fiber
correspond bijectively to invariant Hermitian forms on `E₀`, and positive
definiteness is preserved in both directions. Restricting a positive
invariant form on `X` to `E₀` therefore gives the claimed implication.
These two steps require neither finite length nor homogeneity. The
finite-length hypothesis stated for Proposition 9.1 belongs to its full
criterion and converse, and is not used by this forward implication.
The source fixes an additive character; the construction applies to
every unitary nontrivial choice quantified here.

The correspondence and restriction argument are proof obligations.
This module supplies only a focused prerequisite statement for the
shifted highest-derivative unitarity theorem.
