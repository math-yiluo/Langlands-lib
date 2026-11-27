# Arithmetic finiteness from adelic rational finiteness

`ArithmeticHarishChandraFinitenessReductionStatement` is the implication from
`RationalHarishChandraFinitenessStatement` to the actual
`ArithmeticHarishChandraFinitenessStatement` in the same universe. For the
connected reductive number-field group and the given compact open finite
level `L`, a function on the arithmetic slice at `b` is invariant under the
infinite images of rational points whose finite components stabilize `b L`.
The proof `arithmeticHarishChandraFiniteness_of_rational` uses
`extendArithmeticPlotSmooth` to extend it by zero to the other finite double
cosets. The extension is rationally invariant and right fixed by `L`.

Each nonzero slice is a left pullback of the input. The actual enveloping
action commutes with these pullbacks, since the infinitesimal operators
differentiate the right orbit. Passing from generators to the enveloping
algebra proves that every slice is annihilated by the original cofinite
ideal. Associativity puts every translated profile on the supplied maximal
compact in the original finite-dimensional profile space.

The bound on the normalized adelic height at `(x,1)` gives a polynomial bound
for the archimedean matrix height. Choose a positive-dimensional closed
representation for the application of adelic rational finiteness. Comparison
of matrix heights transports the polynomial bound to this representation.
Submultiplicativity preserves polynomial growth of each fixed left pullback.
The slice-to-adelic growth theorem then bounds the extension on the whole
adelic group. This argument includes the original representation of rank zero.

The restriction map from the finite-dimensional adelic span at `b` contains
every generator of the arithmetic span in its range, because extension
recovers the given function at `b`. Its range therefore bounds the dimension
of the arithmetic span.

This is the direction of the fixed-data decomposition of Borel–Jacquet,
*Automorphic forms and automorphic representations* (1979), §4.3 (1)–(2),
printed p. 195, PDF p. 190 of `borel-jacquet-1979-automorphic`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`, obtained by
extending one summand and using the adelic bound.
