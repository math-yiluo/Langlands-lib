# Recurrent four-crossing maps for two real induction blocks

This is an internal extension of `RealInducedSwapGeneric`, on the same actual
complex-linear standard modules of `GL_4(R)`. No nonzero-weight, exponent-order,
unlinkedness or generic-parameter hypothesis is imposed. The construction is a
prerequisite toward the exceptional integral swap and does not assert injectivity.

`Crossing x y` consists of a sequence `mu : Z -> C`, reflection symmetry for
`pairParity y x` with sign `sigma0 y x`, and recurrence for
`x.exponent - y.exponent + 1` on that parity class. `FourCrossings d e` supplies
these data independently for `BC`, `AC`, `BD`, `AD`, where
`A=chA d`, `B=chB d`, `C=chA e`, `D=chB e`.

`swapData` uses the published character-pair Frobenius construction with the
supplied symmetry. `swap_modulo` identifies the source position exponents and
uses the supplied recurrence to prove exact compact and Lie intertwining.
The local `inducedFirst_landing` and `characterFirst_landing` convert the supplied
parity classes and symmetry signs to those in the proved rank-three landing
theorem and its mirror. The exponent difference between `chA` and `chB` is the
absolute weight, so the two recurrence parameters differ by exactly that weight.

The source/target and intermediate lists, inclusions which forget one or both
Fourier conditions, and compact membership lemmas come unchanged from
`RealInducedSwapGeneric`. `rawMap` first expands the two induction blocks and
then applies `BC`, `AC`, `BD`, `AD` at positions `1,0,2,1`. The two middle maps
commute because they act on disjoint coordinate pairs; `middle_square` identifies
this path with the one at positions `1,2,0,1` using the same sequences.

`first_window_once` transfers the first induction window to position 1 by the
proved normalized-slice two-step landing lemma. `first_window` repeats that
argument on coordinates 1 through 3, giving the final first window at position 2.
`second_window_once` transfers the second window to position 1 on the alternative
path. `second_window` repeats its character-first landing on coordinates 0 through
2 and uses the middle square, giving the second window at position 0 for `rawMap`.
These proofs use only recurrence and symmetry, with no division by sequence values.

`rawMap_mem_target` combines the two compact windows with the unchanged position
characters and compact finiteness. `recurrentMap` corestricts this composite to
the actual target `[induced e, induced d]`. `rawMap_modulo` composes the four exact
intertwiners with the source inclusion. `recurrentMap_modulo` carries that property
through the corestriction without altering the underlying functions.

The provenance is internal: all results are consequences of the Library's
explicit rank-one Frobenius maps, the proved rank-three landing theorem and
normalized slicing, and disjoint multiplier commutation. This module claims
neither a normalized parameter limit nor an injective exceptional swap.
