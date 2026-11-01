# Polynomial growth of genuine automorphic enveloping derivatives

Author: Worker 94.

`Langlands.Automorphic.automorphicDifferentialGrowth` proves the exact published
`Langlands.Automorphic.AutomorphicDifferentialGrowthStatement K n` for every
`(K : Type u) [Field K] [NumberField K]` and every natural rank `n`, including
zero. For every actual automorphic form `f` and every element `a` of the
complex enveloping algebra, it proves
`HasPolynomialGrowth K n (finiteSmoothEnvelopingAction K n a f.val).val`.
The statement module and its imported definitions are unchanged.

Fix a finite adelic slice. The existing automorphic membership equivalence
gives compact finiteness, simultaneous center finiteness of the entire smooth
slice family, and polynomial growth of the original function on this slice.
The first component of `SliceFinitenessProof.sliceFiniteness` transports the
actual simultaneous center-finite condition by evaluation of the family.
Its second component transports the finite compact group orbit to the smooth
slice. These operations use the original hypotheses and original compact and
center actions.

The supporting theorem
`ArchimedeanGL.enveloping_hasPolynomialGrowth_of_finite` now applies to this
smooth slice. It obtains an actual compact smooth reproducing kernel from
compact and center finiteness, transfers the specified enveloping derivative
to that kernel using the proved convolution differentiation theorem, retains
compact support by the proved locality theorem, and applies the proved
compact-kernel convolution growth estimate. Its paired Markdown describes
this internal assembly, including the local choice of the actual Borel
structure and Haar measure.

Finally, `finiteSmoothSlice_envelopingAction` identifies the actual finite
slice of the descended adelic enveloping differential with the archimedean
enveloping differential of the original slice. Rewriting by this equality
gives exactly the required growth predicate. The pointwise underlying
function is the original `infiniteSlice`; no alternative action or growth
condition is introduced.

This proof composes Library constructions and the supporting reproduction
development. It does not assume a reproducing kernel, derivative estimate,
analyticity assertion, or density assertion. Growth constants and exponents
are allowed to depend on the enveloping element, the form, and the finite
slice, as in the published statement. The full-parameter example checks
that no rank or number-field universe has been specialized.
