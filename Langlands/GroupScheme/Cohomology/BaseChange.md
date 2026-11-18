# Base change of regular representations and cochains

Let `R` be a commutative ring, `K` any commutative `R`-algebra, `H` any group
scheme over `Spec R`, and `M` any `R`-module. This internal construction extends
a given regular module representation and its natural one- and two-cochains
to the actual base-changed group `H_K`, with coefficient module `K ⊗[R] M`.
No flatness, finite generation, projectivity or smoothness assumptions are used.

`restrictedTest` regards a `K`-algebra as an `R`-algebra through its structural
map. `scalarExtensionCancel` is the canonical test-algebra-linear equivalence
`A ⊗[K] (K ⊗[R] M) ≃ A ⊗[R] M`. Its naturality is proved by nested tensor
induction, with the pure-tensor case reduced to scalar linearity of the
morphism of `K`-algebras.

`ModuleRepresentation.baseChange` transports the original pointwise linear
action through coefficient cancellation and the actual affine pullback point
equivalence `Lie.affineBaseChangeEquiv`. The monoid laws follow from those of
the original action and point equivalence. Naturality follows from coefficient
cancellation and the original representation's naturality.

`OneCochain.baseChange` and `TwoCochain.baseChange` restrict the original
cochain values to the underlying `R`-algebra points and use inverse coefficient
cancellation to obtain the extended values. The final four lemmas prove that
these constructions preserve the one- and two-cocycle equations and the one-
and two-coboundary formulas. A base-module one-coboundary primitive `m` becomes
`1 ⊗ m`; a natural one-cochain primitive of a two-coboundary becomes its
base-changed cochain. Applying the cancellation equivalence reduces each
assertion to its original equation.

The provenance is derived from the project's actual group-scheme base-change
point equivalence, the natural-cochain interface and tensor scalar-extension
cancellation. This module does not claim that every cochain over `K` descends,
that cohomology vanishing ascends or descends, or that the full cohomology
complex satisfies a flat base-change theorem.
