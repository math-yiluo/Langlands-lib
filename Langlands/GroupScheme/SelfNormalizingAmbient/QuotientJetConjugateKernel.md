# Actual conjugate subgroup jet and algebraic orbit kernels

Let `D : ProperQuotientJetData i Q` retain the fixed ambient algebra `B`,
subgroup ideal `I`, and quotient data for a closed actual subgroup `i:H→G` of
an affine group over `Spec R`. For any base change `b:S→Spec R`, actual section
`g` of `G_S`, order `n`, and affine open `U` of `S`, this module identifies the
kernel of actual coordinate restriction to the conjugated subgroup jet with
the algebraic orbit kernel for the actual conjugating section.

`D.conjugateOrbitMap b g n U` is the existing algebraic orbit linear map. Its
point is obtained from the actual `parameterAffinePoint` through the fixed
ambient affine-point equivalence. Its domain is `Γ(S,U) ⊗_R B/aug^(n+1)` and
its target is `Γ(S,U) ⊗_R B/(I+aug^(n+1))`.

`D.originalJetAlgebraHom` expresses the actual original jet algebra comparison
over `R`, using the actual projection algebra and the scalar tower from the
composite map to `Spec R`. Its coefficient map is exactly `projection.app U`.
The original actual affine jet point is the universal cut point transported by
this homomorphism: their classifying maps agree on every ambient coordinate.
The actual jet conjugator is the parameter point transported by this exact
coefficient map. Actual chart conjugation then shows that the actual conjugate
jet point is the transported `universalCutConj`.

Taking classifying coordinates gives the actual conjugated jet function for
every ambient coordinate. On pure tensors the algebraic orbit map has that
same coordinate formula, and the actual original jet section equivalence
preserves the coefficient scalar. Tensor induction proves
`originalBaseChangeJetEquiv_comp_conjugateOrbit`: the actual tensor restriction
for the original inclusion followed by the actual inner automorphism factors
through the algebraic orbit map and the actual original section equivalence.
The theorem `ker_conjugateTensorCoordinates` follows from injectivity of that
equivalence. Both maps and both kernels are actual maps on the common ambient
tensor module; no unspecified identification is used.

This is an internal consequence of the imported original jet section and
algebra comparisons, actual canonical affine jet points and conjugation, and
the existing algebraic orbit map. Closedness supplies source affineness. There
is no smoothness, flatness, or finite-presentation premise beyond the supplied
data. This focused unit supplies the conjugate-family calculation. Its
identification with the classified kernel on the actual homogeneous quotient,
faithfully flat descent, and the final ampleness assembly remain separate.
