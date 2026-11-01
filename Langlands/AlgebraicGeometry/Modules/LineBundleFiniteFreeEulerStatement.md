# Euler characteristics of a line bundle tensored with a finite free sheaf

`LineBundleFiniteFreeEulerStatement` concerns the actual module sheaves on a
scheme `X` over an arbitrary field `K`, in universe `u`. For an actual line
bundle `L` with finite cohomology over the given structure morphism and any
natural number `r`, tensoring `L` with the free sheaf on
`ULift (Fin r)` again has finite cohomology. Its integer Euler characteristic
is `r` times that of `L`, for every supplied finiteness witness.

The statement includes `r = 0`. It requires no smoothness, properness,
ampleness, or nonempty-scheme hypothesis. Finite cohomology has its published
meaning: every actual cohomology vector space is finite dimensional and the
cohomology objects eventually vanish.

This is internal derived content. The free sheaf is the coproduct of `r`
copies of the structure module. Tensoring with a line bundle is an equivalence,
by its proved tensor invertibility, so the displayed tensor is the finite
coproduct of `r` copies of `L`. Actual relative cohomology is additive and
preserves this finite coproduct. Thus each cohomology vector space is a
product of `r` copies of the original one, which gives finite cohomology and
the factor `r` in the alternating dimension sum. This derivation does not
assume an Euler polynomial or a numerical rank comparison.
