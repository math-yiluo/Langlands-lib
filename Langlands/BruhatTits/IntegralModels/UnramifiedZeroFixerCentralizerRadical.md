# Independence of centralizer radical preimages

This internal supporting module proves that the intrinsic radical-preimage subgroup
of the actual integral centralizer has the same image in the specified generic
centralizer for any two characterized smooth zero-fixer models on nonempty
apartment subsets. The subsets need not belong to the same facet. The conclusion
is independent of the choice of represented radicals. The proposition
`UnramifiedZeroFixerCentralizerRadicalIndependenceStatement` and its proof retain
arbitrary universe `u`.

An isomorphism of integral models induces the actual residue-fibre isomorphism.
The greatestness characterization of represented unipotent radicals identifies
the transported radical with any supplied radical on the target. Reduction
naturality identifies membership in the two reduction preimages, and generic
compatibility identifies their images in the original generic rational-point
group. The previously constructed generic-identity-compatible centralizer
isomorphism supplies this comparison for the characterized models.

On the nonempty single-facet domain the actual ambient special fibre is
connected by the supporting connectedness theorem. Its split-torus centralizer
is connected, smooth and affine, so the proved ground-field unipotent radical
existence theorem supplies an actual represented radical of the centralizer.

The module also proves an explicitly conditional comparison with the ambient
radical preimage. Its premise is
`TorusCentralizerUnipotentRadicalStatement.{u}`. Over the algebraically closed
maximal-unramified residue field, that premise identifies the intrinsic
centralizer radical with the intersection of the ambient radical and the
centralizer on every scheme test. The closed integral centralizer inclusion
identifies its integral-point subgroup with the inverse image of the ambient
integral points. Integral-point injectivity and reduction naturality then give
an exact inverse-image equality for radical preimages in the original generic
point groups. The conditional comparison is not used to prove the unconditional
intrinsic independence proposition.

All results are derived from the published centralizer constructions, generic
rigidity, radical uniqueness and existence, and reduction naturality, together
with the model-independence and connectedness support of
`UnramifiedZeroFixerCentralizerIndependence` and `UnramifiedZeroFixerConnected`. No
root-generation or common-subgroup conclusion is asserted here. The radical
intersection premise is proved as `torusCentralizerUnipotentRadical` in
`Langlands.GroupScheme.Absolute.TorusCentralizerUnipotentRadicalProof`; with it
the conditional comparison holds without additional hypotheses.
