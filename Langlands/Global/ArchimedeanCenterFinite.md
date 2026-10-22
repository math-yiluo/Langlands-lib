# Center orbits of the actual archimedean differential action

For every number field K and natural rank n, `centerRepresentation` is the
multiplicative-monoid representation underlying `centerAction`. Thus all
operators come from the actual differential action of the complex universal
enveloping algebra, restricted to its algebra center.

For a smooth complex-valued function f, `centerOrbitMap` sends z to D(z)f and
is complex-linear. `centerOrbitSpan` is the complex span of this actual center
orbit, using the published generic finite-vector construction. The theorem
`centerOrbitSpan_eq_range` identifies the span with the range of the orbit
map: the center is itself a complex algebra, so this range already is a
complex subspace. The orbit contains f because the center contains the unit.

`IsCenterFinite` means that this orbit span is finite-dimensional over C.
`centerFiniteFunctions` is the actual complex subspace of functions satisfying
that condition. Its closure under addition and scalar multiplication, and
stability under the center action, use the generic finite-vector construction.
There is no assertion that an arbitrary smooth function is center-finite.

These are derived implementations of the center-finiteness condition in
Borel–Jacquet, *Automorphic forms and automorphic representations*, sections
1.3 and 4.2 (printed pages 190 and 194–195; one-based PDF pages 185 and
189–190). Registered source `borel-jacquet-1979-automorphic`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The exact orbit-map implementation and reduction to generic finite vectors
are internal derived constructions; they do not add any automorphy or
growth condition.
