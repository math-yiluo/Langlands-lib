# Universal unramified twists and proper rational Jacquet vanishing

Worker 1759. This internal construction applies the tensor universal property
from `Jacquet.ScalarExtension` to the existing actual universal unramified action.
It is a prerequisite of the coefficient geometric-lemma proof of Renard VI.9.2,
rather than a separate assertion attributed to the source.

For an arbitrary norm family, a homomorphism from another group, and a subgroup
whose image is in the full common norm kernel,
`universalJacquetScalarExtensionEquiv` identifies the native coefficient
character-one coinvariants with the regular algebra tensored with the original
complex coinvariants. The evaluation character is one on the subgroup, so the
universal action on pure tensors agrees with scalar extension. The original
group, pullback group, norm-index and coefficient-space universes are independent.
`subsingleton_universalJacquet` transports vanishing through this equivalence.

`unipotentPointImage_le_commonNormKernel` discharges the kernel condition for
any continuous homomorphism from the rational points of an affine unipotent
group of finite type over the given nonarchimedean local field. The published
compact-subgroup containment theorem puts each singleton in a compact subgroup.
Each continuous positive norm, composed with the homomorphism, is one on that
compact subgroup.

For an actual parabolic in the inducing Levi and its represented geometric
radical, closedness of both embeddings supplies an affine source and smoothness
of the radical supplies finite type. Applying the preceding argument through
the canonical Levi-point homeomorphism proves
`properRadical_le_commonNormKernel` for the complete rational norm family.
No properness assumption is needed for this kernel inclusion.

`universalProperJacquetScalarExtensionEquiv` constructs the comparison for
these actual quotients. For a proper parabolic, the original quotient vanishes
by the existing actual-Levi supercuspidality predicate. The theorem
`universalRepresentation_properJacquet_subsingleton` therefore proves vanishing
over the complete native coefficient algebra without an added kernel,
finiteness or filtration premise. The field/group and inducing-carrier
universes remain independent.

This unit does not construct the Jacquet filtration of the induced family or
prove its compact-open fixed-module finiteness. Those remain obligations of
the full VI.9.2 proof.
