# Joint admissibility from compact evaluations

`tensorFiniteAction` acts on the grouped finite slot by finite translation.
`tensorCompactEvaluation` applies the chosen scalar functional at each
archimedean place and retains the vector in the finite slot. Its translates
by the actual compact group apply the corresponding translated functional
at each place. Evaluation commutes with finite translation.

If the translates of each place functional separate its carrier, the
translates of the tensor evaluation separate the tensor. The finite-product
argument uses `RestrictedTensor.pointwiseEvaluation_injective` at the
stage containing every slot. If the finite action is admissible,
`tensor_isJointlyAdmissible` follows. Evaluating an intertwiner on the
compact identity gives a linear map into the finite-level fixed space.
The compact transformation law determines the other evaluations of the
intertwiner from this one. Their separation proves injectivity of the
map on the multiplicity space. Its codomain is finite-dimensional.

This is an internal algebraic argument for the finite-dimensional compact
and finite-level slices of an induced module used by Langlands,
*On the notion of an automorphic representation* (1979), Lemma 7,
printed pp. 205–206 (Corvallis Part I PDF pp. 200–201).
