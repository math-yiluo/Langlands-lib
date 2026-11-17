# Absolute multiplicative type of central residue kernels

This derived module proves a field-level input for the fibrewise
central-isogeny criterion. It uses the absolute field predicate
`Langlands.GroupScheme.IsMultiplicativeType`: the actual group becomes
diagonalizable, with finitely generated full character group, over a field
extension. The conclusion retains nonreduced and disconnected factors.

`isMultiplicativeType_of_central_closedSubgroup` concerns a central closed
subgroup of a connected reductive group over any field. The published
centre-existence theorem gives a closed representative of the full
scheme-theoretic centre. All-test centrality factors the subgroup inclusion
through that representative. The factor is a closed immersion because its
composite with the closed centre inclusion is the original closed
immersion. The published full-centre multiplicative-type theorem and the
closed-subgroup theorem give absolute multiplicative type of the original
subgroup.

`isCentral_field_baseChange_of_residue` applies to an arbitrary
homomorphism of group schemes over any scheme. Centrality of its pullback
to every canonical scheme residue field implies centrality after every
field-valued base change. The field point factors through the canonical
residue point of its image. Centrality survives the ensuing field map, and
the direct/iterated pullback comparison gives the assertion for the
original field point.

`isMultiplicativeType_kernel_fieldFiber` assumes a reductive source,
a separated target, and centrality of every actual canonical residue
kernel. The canonical kernel base-change comparison first gives centrality
of the pulled-back original inclusion. The previous result extends this to
any field-valued base change. The target's separatedness makes the original
kernel a closed subgroup, and closedness survives base change. The source
fibre is connected reductive by the published field-fibre theorem. The
central closed-subgroup result therefore gives absolute multiplicative
type of the actual pullback of the original kernel.

`multiplicativeTypeKernelFieldFiber` bundles this actual pullback with its
proof in the subtype of groups of absolute multiplicative type.
`multiplicativeTypeKernelFieldFiber_val` identifies its underlying group
with that pullback definitionally. No finite-kernel, flatness, Artinian or
local-ring hypothesis is needed for this field-level construction.

The provenance is the published centre existence and full-centre
multiplicative-type proofs, closed-subgroup presentation and
factorization, reductive field-fibre theorem, residue-point factorization
and actual kernel and iterated-pullback comparisons. This is an internal
derived result, with no additional structural theorem retained as an
unproved input. All fields and schemes range over an arbitrary universe
`u`. It supplies a residue input; it does not by itself prove centrality
over an Artinian thickening or the full fibrewise central-isogeny
criterion.
