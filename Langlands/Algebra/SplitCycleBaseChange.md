# Base change when the outgoing differential has split image

Let `f` and `g` be consecutive linear maps over a commutative ring with
`g ∘ f = 0`. Suppose the target of `g` is flat and the inclusion of
its image has a linear retraction. The image is then flat. Tensoring
the sequence from the cycles to the middle module to the image is
exact, and the image inclusion stays injective because its retraction
tensors as well. This identifies the scalar extension of the cycles
with the kernel of the scalar-extended `g`.

The cycle comparison carries the scalar-extended image of the
boundary map to the image of the new boundary map. Tensoring a quotient
and transporting it along the cycle comparison gives
`splitCohomologyBaseChange`. The comparison `cohomologyEquivOfIsos`
uses the same kernel and image descriptions for linear equivalences
intertwining consecutive differentials.
