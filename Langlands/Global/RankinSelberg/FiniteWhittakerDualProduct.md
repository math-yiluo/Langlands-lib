# Ordinary and dual finite Whittaker products

This internal pointwise unit derives the dual finite product from the actual
ordinary paired product. It retains the same two normalized finite vectors and
the same two joint infinite residual functions. It uses the imported Library
matrix duality and finite-component results; it is not a separate direct
translation of a literature theorem.

## Statement

`FiniteWhittakerDual.OrdinaryDualFiniteProductStatement.{u,uQ}` takes two
actual cuspidal realizations of `GL_(r+1)` over a number field with compact
adelic quotient. It uses their supplied spectral presentations, assumes the
embedded finite local components irreducible and admissible, and takes a
finite set `S` containing both exceptional sets. The global unitary additive
character is trivial on the number field, and its canonical finite components
at `S` are supplied.

At each place of `S`, take a standard functional on the first supplied tensor
factor and an inverse-character functional on the second. Vectors `a0`,
`a0'` are supplied with functional value one; this explicitly implies the
functionals are nonzero. Also supply arbitrary finite vectors `a`, `a'` and
arbitrary joint infinite tensors `t`, `t'`. All four global vectors are formed
through the actual `allPlaceTensorEquiv` and the indicated finite pure tensors.
There is no hypothesis that a global Whittaker product already factors.

Let `W`, `W'` be the global Whittaker functions of the prescribed vectors, with
opposite characters. Define

```
f_v(h)  = ell_v(rho_v(h) a_v),
f'_v(h) = ell'_v(rho'_v(h) a'_v),
R(g)    = W_psi(X(a0,t))(infinitePoint S g),
R'(g)   = W_psi_inv(X'(a0',t'))(infinitePoint S g).
```

`infinitePoint S g` retains all infinite components and sets every finite
component to one. With `d(g)=w_(r+1) transpose(g^(-1))`, and with `d_v` the
same matrix formula over the completion, `PairedProducts` asserts both
identities, for every `g` in `unipotentIntegralOutside`:

```
W(g) W'(g)       = R(g) R'(g) product_{v in S} [f_v(g_v) f'_v(g_v)],
W(d(g)) W'(d(g)) = R(d(g)) R'(d(g))
                    product_{v in S} [f_v(d_v(g_v)) f'_v(d_v(g_v))].
```

The actual global `dualFunction` and local
`ArchimedeanLocal.dualFunction` express the second identity in Lean. In
particular, the residuals in the second identity are the dual transforms of
the very same functions `R` and `R'` in the first identity. Both scalars are
exactly one. `R` and `R'` use the normalized reference vectors and are not
asserted equal to the infinite restrictions of `W` and `W'`.

The statement allows empty `S`, arbitrary zero prescribed vectors or infinite
tensors, and the parameter `r=0` denoting `GL_1`. It makes no nonvanishing
claim. Both universe parameters remain free.

## Implemented proof

`finiteComponent_dualPoint` combines the published compatibility of transpose
inverse with finite and local projections with the published formula for the
finite component of the long Weyl matrix. Thus the actual global dual argument
has precisely the expected local dual argument at every finite place.

`weylLong_mem_localIntegral` uses the entrywise description of the long Weyl
matrix. Its entries, and those of its inverse, are zero or one, so it belongs
to the actual integral subgroup at every finite place.

To prove `isUnipotentIntegral_dual`, take an integral `k` for which `g*k` is
upper unitriangular. The integral subgroup is stable under transpose inverse,
so `transpose(k^(-1))*w` is integral. Multiplying the dual argument of `g` by
this element yields

```
w transpose((g*k)^(-1)) w.
```

The published `dualConjGL` lemma says this is upper unitriangular: the inverse
of `g*k` is upper unitriangular, and reversing both indices after transpose
restores the upper triangular shape. This supplies the exact witness in
`IsUnipotentIntegral`. Applying this at every place outside `S` proves
`dualPoint_mem_partial`, stability of the whole partial adelic domain.

`infiniteResidual` bundles the displayed actual normalized coefficient
function. `pair_dual_eq_product` applies the checked ordinary
`FiniteWhittakerSemilocal.pair_eq_product` at the dual point, whose domain
membership was just proved. The component formula substitutes the local dual
arguments in each finite factor. The global residual at that point is
exactly the dual transform of `infiniteResidual`, by definition.

Finally `ordinaryDualFiniteProduct` introduces the statement's data, uses
`pair_eq_product` for the ordinary member of `PairedProducts` and
`pair_dual_eq_product` for its dual member. The same normalized reference
vectors occur in both applications. No additional measure or Fourier scalar
is introduced.

## Remaining scope

This proves common normalization only for the finite product with a joint
infinite residual. Individual real and complex Whittaker factors, their
restriction identities, infinite-group tensor covariance, archimedean integral
nonvanishing, convergence and the full integral factorization remain further
work. The module uses neither algebraic archimedean Whittaker uniqueness nor
an unproved global factorization premise. The full
`ArchimedeanFactorizationStatement` remains open.

The preceding prescribed-model vector assembly supplies vectors `a`, `a'`
realizing embedded coefficient functions exactly and normalized vectors
`a0`, `a0'`. This module's primary statement takes those vectors and their
normalizations as inputs, rather than asserting an additional independent
existence or integral nonvanishing conclusion.
