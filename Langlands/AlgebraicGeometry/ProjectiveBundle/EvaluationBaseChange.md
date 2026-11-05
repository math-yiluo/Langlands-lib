# Adjoint evaluation and canonical direct-image base change

This internal derivation relates the actual adjoint evaluation to the
specified canonical direct-image base-change morphism. It uses the mate
formula in `Modules.GeometricModuleCoalgebra`, the actual pullback-square
comparison in `Modules.DerivedRestriction`, naturality of the adjunction
and that comparison, and the criterion in `ProjectiveBundle.EvaluationFibres`.
It makes no new assertion from external literature.

Fix schemes in the same arbitrary universe, a morphism `p : X → S`, a line
bundle `L` on `X`, a module sheaf `M` on `S`, and a specified evaluation
`ev : M → p_*L`. For any commutative square
`q ≫ p = p' ≫ g`, `baseChangeEvaluation` is the morphism
`g^*M → p'_*(q^*L)` obtained by pulling back `ev` and then applying the
canonical `pushforwardBaseChange`. The square need not be Cartesian.
No base-change invertibility, quasi-coherence or flatness is needed for
this construction or its adjoint formula.

`baseChangeEvaluation_adjunct` identifies the actual adjoint with
`p'^*g^*M → q^*p^*M → q^*L`. Its first arrow is the inverse canonical
pullback-square comparison; the second is the pullback of the original
adjoint. The proof rewrites the canonical direct-image comparison as the
mate of the inverse pullback square followed by the pulled-back original
counit. Adjunction naturality and its triangle identity remove the unit.
Naturality of the pullback-square comparison then moves the pulled-back
`ev` to the required source.

For `M = p_*L` and `ev` the identity, `fibreEvaluationAdjoint_id_eq`
specializes this formula to the actual residue-field fibre. It expresses
the original fibre adjoint as the pullback of the canonical fibre
base-change map followed by full adjoint evaluation of the pulled-back
line bundle on the fibre.

`evaluationGenerates_of_fibre_baseChange_epi` assumes that `p_*L` is
quasi-coherent, that each of those specified fibre base-change maps is
epi, and that full adjoint evaluation on each fibre is epi. Pullback
preserves epimorphisms, so the factorization makes the original adjoint
epi on every fibre. `evaluationGenerates_of_fibre_epi` then gives
intrinsic generation by local sections of the original direct image.

The displayed assumptions are retained. This module proves neither
base-change epimorphy nor full fibre evaluation epimorphy for a cubic
bundle, and it constructs no ordinary moduli representation.
