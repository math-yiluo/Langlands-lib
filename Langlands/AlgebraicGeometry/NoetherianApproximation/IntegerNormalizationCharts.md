# Polynomial charts for finite normalization

`closedFiberNormalizationTools` proves exactly
`ClosedFiberNormalizationToolsStatement` at independent universes. It combines
two algebraic tools for lifting closed-fibre Noether normalization to a finite
type integer domain.

The first lemma proves injectivity of a homomorphism from a noetherian
domain when its kernel is contained in a proper principal ideal `(r)`
and the image of `r` is nonzero in the target domain. Dividing a kernel
element by `r` gives another kernel element. Iteration puts the kernel
in every power of `(r)`, and Krull intersection makes it zero.

The second lemma says that a finite type algebra is quasi-finite at a
prime if a quotient by an ideal contained in the extended contracted
prime is module-finite over the base. The quotient defining the fibre
is then a quotient of a finite module, hence quasi-finite. The weak
quasi-finiteness criterion in algebraic Zariski's Main Theorem gives
quasi-finiteness at the original prime.

Both lemmas are internal derivations from Mathlib. The exact proof theorem
packages them as the two conjuncts of the statement. This contribution proves
these auxiliary tools; the global finite-normalization target is separate.
