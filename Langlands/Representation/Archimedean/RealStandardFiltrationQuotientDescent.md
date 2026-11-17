# Replacing a filtration source by an exact quotient

This internal linear-algebra argument concerns the actual compact-finite
standard modules in arbitrary ambient rank. Let `T:R→V` intertwine modulo
a subspace `N` of the target. Let `U:R→S` be an exact surjective intertwiner.
Assume that `T(ker U)` is contained in `N`.

Choose a complex-linear section `s` of `U`. Then `q=T∘s` intertwines modulo
`N`, and `N+range(q)=N+range(T)`. Thus a last filtration source can be
replaced by this exact quotient if its kernel maps into the preceding span.

For compact translation or a real Lie derivative, compare `s` applied after
the action with the action applied after `s`. Exactness of `U` puts the
difference in its kernel. Applying `T` puts that error in `N`; the remaining
error is the known intertwining error of `T`. No equivariance of the chosen
linear section and no stability hypothesis on `N` is needed. For the span
identity, write `f=(f-s(Uf))+s(Uf)` and apply `T`.

`RealStandardFiltrationQuotientDescentStatement` universally quantifies the
ambient rank, three lists, subspace and maps with exactly these hypotheses.
`realStandardFiltrationQuotientDescent` proves it using a linear section,
which exists for every surjective linear map of complex vector spaces.

The kernel containment is an explicit hypothesis of this general helper.
Its application to the crossed quotient in the two-induced-block problem
still requires a separate proof of that actual containment.
