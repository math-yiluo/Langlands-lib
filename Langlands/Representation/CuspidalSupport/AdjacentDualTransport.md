# Actual adjacent dual transport

This internal unit supplies actual smooth-duality transport for the two
adjacent factors. It identifies the dual of an actual simple
subrepresentation with a quotient by an actual nonzero proper kernel,
identifies two-factor product duals without reversing their order, and
reverses the positive adjacent class relation.

`quotientKernelEquiv` is the first isomorphism theorem for a supplied
surjective intertwiner of smooth complex representations of any topological
group. It uses the actual module quotient by the intertwiner's kernel.
The linear equivalence is `LinearMap.quotKerEquivOfSurjective`; equivariance
follows by checking on images of source vectors in the quotient.

For `dualSubrepresentation_exists_quotient`, suppose compact open
subgroups are cofinal, \(P\) is admissible and reducible, and the actual
subrepresentation \(L=S\subset P\) is simple and admissible. A supplied
smooth isomorphism \(P^\vee\simeq R\) yields an actual surjection
\[
 R\longrightarrow P^\vee\longrightarrow L^\vee.
\]
The second arrow is restriction of smooth functionals along the actual
inclusion, and is surjective by the existing smooth-dual exactness theorem.
Let \(U\) be the kernel of the composite. If \(U=0\), this map would
identify \(R\) with the simple \(L^\vee\), and admissible duality would
force \(P\) to be simple. If \(U=R\), its surjective target would be zero,
contrary to simplicity. Thus \(U\) is nonzero and proper, and
`quotientKernelEquiv` identifies the actual \(R/U\) with \(L^\vee\).

`twoFactorProduct_admissible` applies external tensor admissibility and
the existing actual normalized induction admissibility theorem. It allows
different positive ranks and any independent carrier universe.
`twoFactorProduct_contragredientIso` uses the already proved
`TwoFactorCommutativity.productSmoothDual` and explicit factor equivalences
to identify
\[
 (A\times B)^\vee\simeq A^\vee\times B^\vee
\]
on the same literal two-block shape, in the same order, for admissible
supplied factors. Its input carriers lie in `max uF uV`.

Finally, `dualRep_adjacent_reverse` proves that \([A]=\nu[B]\) implies
\([B^\vee]=\nu[A^\vee]\) for the existing actual supercuspidal dual
representatives. Apply the class duality function to the given equality,
use its already proved compatibility with negation of determinant-power
exponents, then twist by the positive unit exponent. Additivity and the
zero-exponent law cancel the two twists.

All field-dependent results retain the supplied topological data \(T\).
The provenance is internal algebraic transport from actual smooth-dual
exactness and admissible biduality, normalized product duality,
admissibility, and determinant-twist laws. No product irreducibility input
or local triple Jacquet transfer is proved in this unit.
