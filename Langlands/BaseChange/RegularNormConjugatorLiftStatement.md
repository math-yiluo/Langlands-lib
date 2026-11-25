# Lifting a twisted conjugator with regular cyclic norm

`RegularNormConjugatorLiftStatement` concerns a surjective map of commutative
`R`-algebras `f : S → T` that reflects units. The automorphisms `σ` of `S`
and `τ` of `T` commute with `f`, and `σ ^ l = 1`. The ordered cyclic norms
of `δ, δ' ∈ GL_n(S)` have characteristic polynomial given by the image of
one polynomial `p ∈ R[X]`. The proposition lifts existence of a twisted
conjugator from `T` to `S` if `l` is a unit in `T` and the derivative of the
image of `p` evaluates to an invertible matrix at the reduced norm of `δ`.

This derived lifting input is intended for the integral part of the
adelic orbit argument in the proof of
`GeneralLinearTwistedEllipticCentralizerStatement` (module
`Langlands.TraceFormula.GeneralLinearTwistedEllipticCentralizerStatement`). At a good finite place `S` is an
integral coefficient algebra, `T` is its reduction, and a separable
residue polynomial gives the derivative condition by Bézout and
Cayley–Hamilton.

One route starts with a lift of the residue conjugator as a matrix. With
`A = N(δ)` and `B = N(δ')`, apply the divided difference of `p` to the
commuting operators of left multiplication by `A` and right
multiplication by `B`. Cayley–Hamilton makes the resulting matrix intertwine
the two norms. Its residue is `p'(Ā) x̄`. On norm intertwiners the operator
`X ↦ δ σ(X) (δ')⁻¹` has `l`th power the identity. Summing its first `l`
iterates yields a fixed matrix with residue `l p'(Ā) x̄`, which is
invertible. Unit reflection makes the fixed matrix a twisted conjugator
over `S`.
