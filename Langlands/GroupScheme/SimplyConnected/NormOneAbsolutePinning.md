# The actual absolute pinning of the reduced-norm-one group

For a finite-dimensional central simple algebra `A` over a field `k`,
`normOne_isSimplyConnected` applies the actual group-scheme isomorphism
from the unconditional separable-closure matrix chart. The target is
a special linear group. The positive reduced degree supplies the
nonempty matrix index required by its simple-connectedness theorem.
The Library's algebraic-extension reflection theorem transfers simple
connectedness back to `SL₁(A)` over `k`.

`normOneAbsolutePinning` applies the Library's absolute pinning
construction to this group's connected reductive structure. Its torus
is defined over `k` and splits over `SeparableClosure k`, where the
chosen root datum and pinning live. Its star action has the full
absolute Galois group as domain.

This is an internal deduction from the actual norm-one splitting
isomorphism, simple connectedness of split special linear groups,
and reflection along an algebraic extension. The construction works
for `k, A : Type u` at every universe `u`, including reduced degree one
and fields where the scheme-theoretic centre is nonreduced.
