# Finite tensor expansions of translation-finite functions

`Langlands.RankinSelberg.FiniteFunctionTensorStatement.{uG}` is a
Prop-valued statement; this module supplies no proof. It isolates the
finite-function tensor reduction used before display (6) on printed p. 392
of JPSS (1983). Its general monoid scope is an internal algebraic
generalization, not a theorem quoted verbatim from that source.

## Exact statement

The declaration quantifies over every `G : Type uG` with a `Monoid G`
instance and an arbitrary `TopologicalSpace G` instance, and every `r : ℕ`.
The domain `Fin r → G` has the product topology and pointwise multiplication.
For either domain, a finite function means exactly

```text
Continuous h ∧
  FiniteDimensional ℂ (Submodule.span ℂ
    (Set.range fun b => fun a => h (b * a))).
```

Thus the translates are explicitly `a ↦ h (b * a)`, and the span is the
complex linear span in the space of all functions on that domain.
Continuity uses the ordinary topology on `ℂ`. The two predicates are local
let-bindings, not additional public definitions.

For each finite function `η : (Fin r → G) → ℂ`, the conclusion supplies
`N : ℕ`, scalar coefficients `c : Fin N → ℂ`, and factors
`f : Fin N → Fin r → G → ℂ`. Every `f j i` is continuous and has
finite-dimensional complex left-translation span, and

```text
∀ a, η a = ∑ j : Fin N, c j * ∏ i : Fin r, f j i (a i).
```

This is pointwise equality for every `a`, with the same chosen finite data.
The data depend on `η` and its domain; no test function or spectral parameter
occurs in the declaration. Consequently they can be fixed before these
vary in an application to
`Langlands.RankinSelberg.FiniteFunctionMellinStatement.{uG}`, by taking
`G = F.Carrierˣ` with the supplied field topology.

The dimension `r = 0` is included: the domain is a singleton and the empty
product is one, so one summand with coefficient equal to the value of `η`
can represent any such function. Scalar coefficients are retained for
precisely this case. The zero function is also included and can be
represented by `N = 0`. Neither a positive dimension nor a nonzero function
is assumed.

No commutativity, inverses, local compactness, separation axiom, or
continuity of multiplication is assumed. In particular the usual p-adic
unit groups satisfy the stated hypotheses. There is no assumed tensor
decomposition, finite separation rank, or character decomposition.
The statement asserts no integrability, convergence, rational continuation,
or common denominator.

## Original sources and generalization

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
  Convolutions*, American Journal of Mathematics **105** (1983), 367–464,
  printed p. 392, the paragraph after display (5) and before display (6).
  Registered source `jpss-1983-rankin-selberg`, retained file
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
  SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic forms on
  GL(3) I*, Annals of Mathematics (2) **109** (1979), 169–212,
  §2, printed p. 181, the finite-function definition immediately before
  Proposition (2.2).
  Registered source `jps-1979-gl3-i`, retained file
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`,
  SHA-256 `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.

JPS defines finite functions on locally compact abelian groups by
continuity and finite-dimensional translation span. JPSS writes the
relevant finite functions on a p-adic torus as finite sums of products of
one-variable finite functions. In that passage the finite families depend
only on the fixed representations, before the varying Schwartz functions
are introduced into the one-variable integrals. This declaration extracts
only the algebraic tensor reduction. Its explicit scalar coefficients,
zero-dimensional case, and arbitrary monoid scope are derived extensions.

The reason no topological-monoid hypothesis is needed can be seen from a
prospective coordinate-slice argument. Split the product as `X × Y`,
where both factors are monoids. For a finite function `η`, each slice
`x ↦ η (x, y)` is the restriction to `(x, 1)` of the left translate of
`η` by `(1, y)`. Hence the span of all these slices is finite-dimensional.
Choose a basis from the slices. On this finite-dimensional function space,
point evaluations span the algebraic dual, so every basis-coordinate
functional is a finite linear combination of point evaluations.
The resulting coefficient functions of `y` are therefore finite linear
combinations of slices `y ↦ η (x, y)`.

Every slice is continuous because inserting fixed coordinates is
continuous for the product topology; no multiplication map is used in
this continuity argument. Its left translates lie in the image of the
original translation span under restriction: for example
`x ↦ η (b * x, y)` is the restriction of the translate by `(b, y)`.
Thus each slice, and each finite linear combination of coefficient
slices, has finite-dimensional translation span. Iterating this split
yields the asserted finite products. The singleton case starts the
induction. This explains the scope and gives a route for the separate
proof obligation; it is not a claim that this argument has been
implemented in this statement module.
