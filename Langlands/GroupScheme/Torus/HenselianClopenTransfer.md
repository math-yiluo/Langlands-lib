# Transfer of etale Hom families into a prescribed Henselian algebra

This derived construction uses relative Henselian etale lifting
and the Noetherian local clopen criterion over a residue-field extension.

Let `A` be any Henselian local `P`-algebra with a compatible field quotient
`K`, and let `E` be an etale Noetherian `P`-algebra. Let `C` be relatively
diagonalizable over `P` and `D` affine of finite type. Suppose a supplied
family `j : C_E → D_E` becomes an isomorphism at a specified point
`φ : E → K`.

`exists_clopen_evaluation` supplies a map `σ : E → A` reducing exactly to
`φ`, such that the evaluated homomorphism `C_A → D_A` is both an open and
a closed immersion. The proof lifts the residue point by Henselian etale
sections and factors this lift through the local ring `E_Q` at
`Q = ker φ`. The residue-field map on `E_Q` has maximal kernel, so the
Noetherian local clopen criterion applies to `j` localized at `Q`. The
resulting immersion properties persist after evaluation along `E_Q → A`.
Functorial evaluation identifies this map with evaluation along `σ`.

No Noetherianity of `A` is assumed. No completed lift or finite-coefficient
model is constructed here; the etale family and its isomorphic fibre are
explicit inputs.
