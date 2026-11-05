# Fibrewise criteria for intrinsic evaluation generation

This internal derivation concerns the actual adjoint evaluation
`p^*M → L` for a scheme morphism `p : X → S`, a quasi-coherent module
sheaf `M` on `S`, a line bundle `L` on `X`, and a specified map
`ev : M → p_*L`. All schemes lie in the same arbitrary universe.

`fibreEvaluationAdjoint` is the actual pullback of this adjoint to the
scheme-theoretic residue-field fibre of `p` at `s`, with its source
identified as `p_s^*(κ(s)^*M)` by the canonical pullback square comparison.
It is not the evaluation of all sections on that fibre unless a further
direct-image comparison identifies the two.

`evaluationGenerates_of_residue_epi` assumes that the adjoint becomes an
epimorphism after pullback along `Spec κ(x) → X` for every point `x`.
It proves intrinsic `EvaluationGenerates`. The affine tensor-section
argument from `EvaluationAdjoint` applies to the restriction over an affine
base neighbourhood. Naturality of the residue-field maps and canonical
pullback-composition isomorphisms transfer the assumed epimorphy to the
residue point of that open subscheme. If all evaluated base sections
vanished there, tensor induction would make the resulting map zero on
all global sections. Quasi-coherent affine surjectivity and triviality of
a line bundle on a field spectrum contradict this.

`evaluationGenerates_of_fibre_epi` assumes that every
`fibreEvaluationAdjoint` is epi. The canonical `κ(x)`-point of the fibre
at `p(x)` pulls this epimorphism to the original residue point of `X`.
The preceding theorem then supplies intrinsic generation.

No direct-image rank, base-change isomorphism, fibrewise generation,
closed immersion, or ordinary moduli representability is proved here.
The statements retain their displayed fibrewise epimorphy assumptions.
