# Relative Weyl generation from a trivial positive-root stabilizer

This internal reduction uses the actual relative Weyl quotient and actual root
vectors. Its structural hypotheses remain explicit. It does not prove geometric
reflection existence or triviality of the positive-root stabilizer.

`HasTrivialPositiveRootStabilizer i ν` means that every element of the actual
quotient preserving positivity of all actual roots under the integral pairing
with `ν` is the identity. The quotient action transports root vectors by its
permutation of actual roots. Evaluating the covector of `ν` on a transported
root vector gives the integral pairing with the transformed character, cast to
`ℚ`. An element acting trivially on the root span therefore preserves those
signs, so the stabilizer hypothesis implies faithfulness of the root-span action.

For integral normalizer reflection data `D`, a split torus and finitely many
actual roots give the evaluation root pairing already constructed in
`RootReflectionAssembly`. Let `H` be the subgroup of the actual quotient generated
by the chosen reflection representatives. The image of `H` on the root span is
the image of the abstract Weyl group of this pairing. A generic integral
cocharacter gives a regular rational covector `f`. For an arbitrary quotient
element `q`, precomposing `f` with its root-span action gives another regular
covector `g`, since `q` permutes actual roots.

Chamber alignment supplies an abstract Weyl element `w` whose contravariant
coweight action on `g` has the same signs as `f`. Lift its weight action to an
element `r` of `H`. The transpose relation of weight and coweight maps then says
that `q * r` preserves the positive roots selected by `ν`. The stabilizer
hypothesis gives `q * r = 1`, whence `q = r⁻¹` belongs to `H`. Thus `H` is the
whole quotient. Combining this generation result and the faithfulness result
with the existing assembly theorem proves `HasRelativeRootSystem i` under
these explicit inputs.

No finiteness of the actual quotient, reducedness, simple-root basis, Coxeter
realization or preexisting relative-root-system assertion is used. Empty root
sets are allowed. For such a root set the stabilizer hypothesis says the actual
quotient is trivial, exactly what this argument needs. The results are internal
consequences of the imported root-pairing chamber alignment and reflection
assembly; they do not discharge the remaining geometric hypotheses of the
unrestricted `RelativeRootSystemStatement`.
