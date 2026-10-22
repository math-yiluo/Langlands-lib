# Character twists of Weil–Deligne pairs

Worker 17 authored this construction. `twist chi A` retains the actual
carrier and monodromy while multiplying the Weil action by `chi(g)`.
Nilpotence is inherited unchanged. The covariance proof moves the two
character scalars through linear maps and cancels `chi(g) chi(g⁻¹)=1`,
then applies the original covariance equation. The norm character
remains `nu`; no relation between `chi` and `nu` is assumed.

`twistMap` and `untwistMap` use the published forward and inverse
intertwiner constructions. Their underlying linear maps and monodromy
squares are unchanged. `twistFunctor` and `twistFullyFaithful` establish
the category and inverse-map obligations. `twistEquiv` retains a genuine
linear equivalence and gives the well-defined quotient operation
`twistClass`.

These are algebraic constructions for every field, group and finite
carrier rank, including zero and nonzero monodromy. They do not identify
the algebraic character convention with continuous complex
quasicharacters, or assert an unstated inertia condition.

Source correspondence: Henniart 2000, §1.2(2), printed page 440, fixes
the tensor-twist convention; Tate, *Number theoretic background*,
Corvallis Part II, printed page 20, §4.1.5 gives tensor monodromy.
Tensoring with a one-dimensional zero-monodromy character leaves `N`
unchanged. The scalar model and its covariance are proved directly
here. Literature IDs and exact PDF SHA-256 values are
`henniart-2000-simple-proof`,
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`,
and `tate-1979-number-theoretic-background`,
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

This pair imports `Langlands.WeilDeligne.Basic` and
`Langlands.Weil.Representation.Twist`. The latter imports Worker 4's
unchanged `Langlands.Representation.Twist.Definitions`. No earlier draft
code is copied.
