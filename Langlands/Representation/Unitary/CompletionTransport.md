# Covariance and surjectivity of completed isometries

This internal helper extends the published positive-form completion and its
form-preserving intertwiners. The group, source carrier and target carrier have
independent universes. The group is a group; the carriers are complex modules.
The input consists of invariant positive forms `b`, `c`, a representation
intertwiner `f`, and the identity `c.inner (f v) (f w) = b.inner v w`.

`completedIsometry_covariant` extends an additional algebraic covariance equation
`f (a v) = d (f v)` to the actual Hilbert completions. Its additional inputs are
complex-linear algebraic endomorphisms `a`, `d`, continuous complex-linear maps
`A`, `D` on the respective completions, and their embedded-vector formulas
`A (j_b v) = j_b (a v)` and `D (j_c w) = j_c (d w)`.
The conclusion is the equation

```text
completedIsometry b c f hf (A x) = D (completedIsometry b c f hf x)
```

for every completed vector. The proof extends equality of two continuous
compositions from the dense source carrier. The embedded-vector formulas,
the published completed-isometry formula and the supplied covariance prove
the equation there. The result constructs no extension of an unbounded or
merely algebraic operator.

`completedIsometry_surjective` assumes surjectivity of the original `f` and
proves surjectivity of the published completed isometry. Its range is closed
because it is an isometric image of a complete space. Original surjectivity
and the embedded-vector formula put the dense embedded target carrier in this
range. Dense-range induction then puts every completed target vector in it.

`completedIsometry_unique` proves equality of any continuous complex-linear
extension with the published completed isometry when the embedded-vector
formulas agree. It uses density and closedness of equality of continuous maps.
`completedRange_covariant` uses `completedIsometry_covariant` to prove stability
of the actual completed range under the target operator `D`: choose an original
preimage in the source completion and apply `A` to it. The range is the published
finite-invariant closed image, not a separately chosen subspace.

`completedEquiv` applies `LinearIsometryEquiv.ofSurjective` to the actual completed
isometry and the proved surjectivity. `completedEquiv_apply` identifies its
forward map with that isometry. `completedEquiv_toHilbert` identifies its value
on each embedded original vector with the embedded image under `f`. It is a
complex-linear isometric equivalence; no independent choice of Hilbert realization
or inverse-intertwining assumption is supplied.

These are intrinsic consequences of
`Langlands/Representation/Unitary/CompletionIntertwiner`, its actual uniform
completion, and the published density and closed-image proofs. No new original
literature identification or existence of positive forms is asserted.
