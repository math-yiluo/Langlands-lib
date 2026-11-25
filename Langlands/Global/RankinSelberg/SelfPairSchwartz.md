# Nonnegative Schwartz functions standard outside a finite set

Internal test-function helper for the proof of `CuspidalSelfPairContinuationStatement`.

For any adelic row `y`, the proposition
`PositiveStandardSchwartzStatement` asserts the existence of a real-valued
nonnegative function with value one at `y`, whose complex coercion is
Schwartz--Bruhat and standard outside a finite set of finite places.
`positiveStandardSchwartz` proves this statement.

Every finite coordinate of `y` is integral at almost every finite place; a finite
union of their exceptions gives a set `S` with `y` integral outside `S`.
In fact, `exists_nonnegative_standardSchwartz_of_mem` works for every such `S`.
Choose a smooth compactly supported real bump on the archimedean row space with
values in `[0,1]` and value one at the archimedean coordinates of `y`. At the
finite adeles use the characteristic function of the coset
`finiteCoordinates(y) + latticeVec(n,0)`. This coset is compact and open by the
Library's finite-adelic lattice results. Their product is a pure
Schwartz--Bruhat function under the Library definition.

The coset condition is coordinatewise membership of `x_v - y_v` in the completed
integer ring. Outside `S`, it forces `x_v` integral. Among rows integral outside
`S`, this condition only depends on the coordinates at `S`. This proves exactly
`IsStandardOutside`, including its support and dependence clauses.

This is an internal construction from the Library Schwartz--Bruhat and
finite-lattice definitions, whose source conventions are Getz--Hahn, appendix
C.3. The only archimedean input is Mathlib's finite-dimensional smooth bump
construction. No continuation or Euler factorization is asserted.
