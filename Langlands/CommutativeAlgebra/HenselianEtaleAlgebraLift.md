# Relative etale lifting into a prescribed Henselian algebra

Worker 872. This internal construction applies published Henselian etale
sections after tensor base change.

Let `A` be a Henselian local `P`-algebra with a supplied surjective map to a
field `K`, compatible with the `P`-algebra structures. If `E` is etale over
`P`, `exists_lift` lifts any supplied `P`-algebra map `E → K` to a map
`E → A` with exactly the given reduction to `K`. The proof regards that
residue map as an `A`-algebra point of `A ⊗[P] E`, applies Henselian
lifting there, and restricts the resulting section to `E`.

`exists_local_lift` also extends this lifted map to the localization of
`E` at the kernel of the given residue point. Every denominator outside
that kernel has nonzero residue and hence maps to a unit in the local
ring `A`. Localization's universal property gives the extension and its
exact restriction equation. No Noetherianity of `A` is assumed.
