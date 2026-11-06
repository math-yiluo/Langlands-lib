# Quasi-splitness of a supplied adjoint quotient

`AdjointQuotientQuasiSplitStatement.{u}` says that, over every field
`k : Type u`, an actual adjoint quotient `q : G → A` sends quasi-splitness
of `G` to quasi-splitness of `A`.

The quotient is supplied with the unchanged `IsAdjointQuotient q`
predicate: it is flat, surjective and locally of finite presentation, has
the full scheme-theoretic centre as its actual kernel, satisfies the group
and scheme quotient universal properties, and has an actual adjoint target.
The conclusion uses the unchanged `IsQuasiSplit`: the target is connected
reductive and has a ground-field closed Borel whose algebraic-closure
base change is also Borel. The centre is allowed to be non-smooth or
disconnected. There is no perfectness or characteristic restriction.

This is a derived specialization of Milne, *Algebraic Groups* (2017),
Proposition 17.20, printed p.357/PDF p.373, and the arbitrary-field
formulation 17.69, printed p.376/PDF p.392. A quotient map of connected
group varieties carries a Borel subgroup to a Borel subgroup. Applying
this to a ground-field geometric Borel of `G` and to its algebraic-closure
base change yields the stated conclusion; connected reductivity of the
target is already part of `IsAdjointQuotient`. In the scheme-theoretic
formulation, constructing the image, its smoothness and its Borel
maximality on both fields remain proof obligations.

The registered source is `milne-2017-algebraic-groups`, readable at
`/home/taskhub/central-library/Milne--Algebraic groups, the theory of group schemes of finite type over a field (book)--2017.pdf`,
SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

Worker 1472 identified and formulated this missing prerequisite for the
actual quasi-split inner-form construction. Worker 1459 authored the Lean
statement and this source comparison. This pair states a proposition; it
does not prove it, construct an adjoint quotient, or prove the host
norm-criterion quasi-splitness theorem.
