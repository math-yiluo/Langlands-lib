# Field multiplication by a maximal central relative torus

This internal deduction works over every field. A closed subgroup `D` of a
connected reductive group `G` need only contain all commutators. Multiplication
of `D` with any maximal central relative torus of `G` is surjective on the
underlying scheme points. If `D` has finite full scheme-theoretic centre, the
commuting multiplication homomorphism is a central isogeny.

The proof first represents the actual derived subgroup by a closed inclusion
`e : E → G`. Minimality of the derived subgroup places its range in `D`.
The published `reductiveCentralTorusSurjectivity` produces a closed central
field torus `Z₀` whose multiplication with `E` is surjective. The field/relative
torus comparison makes `Z₀` a relative torus, so maximality places it in the
given `Z`. Factorization through represented subgroup functors gives actual
maps `Z₀ → Z` and `E → D`. Their product factors the known surjective
multiplication through `Z × D → G`, proving the latter surjective.

The second conclusion applies the one-factor finite-centre kernel theorem:
the kernel projects as a closed central subgroup of `D`, so it is finite.
The existing field isogeny theorem for commuting multiplication then gives
the central isogeny. No equality between `D` and `E`, semisimplicity of `D`,
or field splitting of the given `Z` is assumed.

`MaximalCentralTorusFieldMultiplicationStatement` packages these two conclusions,
and `maximalCentralTorusFieldMultiplication` proves it in every universe.
