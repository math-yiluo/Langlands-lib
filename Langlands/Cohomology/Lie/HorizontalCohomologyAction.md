# Actions on actual horizontal cohomology

This internal construction acts on the horizontal quotient already defined in
`HorizontalCohomology`. It introduces no new cochain spaces, differential or
cohomology relation.

The coefficient field `K : Type u` has characteristic zero. The Lie algebra
`L : Type v`, coefficient Lie module `M : Type w`, full acting group
`G : Type ug`, and a second acting monoid `P : Type up` have independent
universes. The inputs `H`, `σ`, `ρ`, `hσ`, `hρ` and all-degree insertion law
`hι` are exactly those of the existing horizontal quotient. In particular the
horizontal cochains satisfy equivariance for every element of `G`.

Write `C q` for those cochains and `D q` for their actual restricted
Chevalley–Eilenberg differential. The additional input is a representation
`action q : Representation K P (C q)` in every natural degree and the equation
`D q (action q p f) = action (q + 1) p (D q f)` for every `q`, `p` and `f`.
This is an explicitly conditional algebraic construction. Its intended finite
adelic specialization will use the already proved differential commutation
equation; this module itself supplies no arithmetic action.

`action_mem_cycles` uses that equation and linear preservation of zero to
prove preservation of the kernel. `action_mem_boundaries` handles degree zero
using its zero boundary submodule. In successor degree a boundary `D q g`
maps to `D q (π q p g)`, giving an actual image witness.

`cyclesRepresentation` is Mathlib's `Representation.subrepresentation` for
the resulting invariant kernel. `cyclesRepresentation_val` identifies its
underlying cochain with `action q p f.val`. The boundary membership equivalence from
`HorizontalCohomology` and the image witness just described prove invariance of
the actual boundary submodule inside cycles.

`cohomologyRepresentation` is Mathlib's `Representation.quotient` applied
to that cycle representation and boundary submodule. Its identity and
multiplication laws are the laws of that existing construction.
`cohomologyRepresentation_class` identifies the action on a class with the class
of its translated cycle, by reflexivity. `cohomologyClassIntertwiner` bundles the
existing quotient projection as an intertwiner between the cycle and quotient
representations. Its underlying-linear-map formula is also reflexive.

All natural degrees, including zero, are retained. The provenance is internal
restriction and quotient of the published horizontal complex using Mathlib's
linear representation constructions. No external source identification,
topology, smoothness, finiteness, or relative-to-absolute comparison is asserted.

Authorship: Worker 2.
