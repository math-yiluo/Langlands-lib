# Reductivity of full character-kernel centralizer identity components

Author: Worker 1465.

`kernelCentralizerComponentReductive` proves exactly the published proposition
`Langlands.GroupScheme.RelativeRoot.KernelCentralizerComponentReductiveStatement.{u}`
for arbitrary universe `u` and every field. Its inputs and the actual identity
component are those of the imported statement. Affineness of the supplied smooth
closed representative follows from its closed immersion into the affine ambient
group. The character need not be primitive, and its full scheme kernel, including
nonreduced structure, is retained in the all-test centralizer.

The proof extends the ground field to its algebraic closure. The published
algebraic-closure base-change theorem supplies connected reductivity of the
ambient group. Splitness of the torus is preserved, and injectivity of base change
on the actual character lattice of a split torus preserves the nonzero character.
The accompanying full-kernel base-change theorem transports the given centralizer
representative without replacing or reducing the kernel. Closedness, smoothness
and affineness are preserved by base change.

The accompanying classical theorem then proves connected reductivity of the
identity component over the algebraic closure. Its proof uses a containing split
maximal torus, actual integral root support, containment of proportional-root
centralizers and the published rootwise radical detector. It introduces no
Richardson or Haboush premise.

The published identity-component base-change isomorphism identifies that
identity component with the algebraic-closure base change of the original actual
identity component. Ground-field radical triviality for the connected reductive
group over the algebraic closure transfers along this isomorphism. This is
precisely the geometric radical condition over the original field. Smoothness,
affineness and connectedness of the original identity component are supplied by
its published construction, completing the four fields of connected reductivity.

The proof has internal provenance: it composes the published structural and
transport results with the accompanying classical and full-kernel base-change
units. It does not use a new fixed-subgroup reductivity assumption. The original
source and scope of the target are recorded in its unchanged published Markdown;
the implemented proof follows the classical maximal-torus route described above.
