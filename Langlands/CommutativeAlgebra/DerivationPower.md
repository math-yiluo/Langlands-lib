# Prime-power iterates of derivations

This is an internal algebraic construction for the restricted-power route in
the Lie algebra of an affine group scheme. It is derived from the Leibniz rule,
the tensor product of linear maps, and the binomial identity for commuting
elements; it invokes no external structural theorem about algebraic groups.

Let `R` be a commutative ring of prime characteristic `p`, and let `A` be any
commutative `R`-algebra. No reducedness, nontriviality, finite generation, or
perfectness assumption is imposed. If `D : Derivation R A A` and `r : ℕ`,
`primePower D p r` is the derivation with underlying linear map
`D.toLinearMap ^ (p ^ r)`, where multiplication of linear endomorphisms is
composition. At `r = 0` this recovers `D`.

The proof of Leibniz writes multiplication as a linear map
`A ⊗[R] A →ₗ[R] A`. This map intertwines `D` with the sum of the actions of `D`
on the two tensor factors. Those actions commute. Their `p^r`-th power is the
sum of their `p^r`-th powers: the remaining binomial term is a multiple of `p`,
which vanishes because `R` has characteristic `p`. This argument does not
assume that the endomorphism ring of the tensor product is nontrivial.
Evaluating the iterated intertwining identity on a pure tensor proves Leibniz
for the iterate.

`primePower_naturality` shows that any `R`-linear map intertwining two derivations
also intertwines their prime-power iterates. It is the usual induction for
powers of intertwined endomorphisms.

This module does not yet construct restricted powers on actual Lie kernels
or prove semisimple replacement. Invariance under translation, compatibility
with actual algebraic representation differentials, and the characteristic-zero
argument remain separate obligations.
