# Scalar extension of actual split pinnings

Worker 1317. This is internal support for arbitrary-field descent in the split
Steinberg quotient task. It is derived from the published actual weight-space
base-change comparison, Lie scalar extension, root-datum lattice transport,
maximal-torus base change and connected-reductive ascent. It makes no external
source claim.

For the standalone `RootPinning` helpers, let `k` and `F` be fields in the same
arbitrary universe with an `Algebra k F` structure. Assume that the actual group
scheme `G` over `k` is affine and locally of finite type. Let `T` be a commutative
group scheme over `k`, `i : T.toGrp ⟶ G` a homomorphism, `P` the supplied root
datum with base `b`, and `p : RootPinning i P b`. These ambient hypotheses remain
parameters of the helpers; a standalone `RootPinning` does not supply local
finite type or splitness of `T`.

Under this context, `baseChangeRootVector` is the image of `1 ⊗ rootVector` under `Lie.schemeScalarExtension` in the actual
pulled-back Lie kernel. Published weight-vector base change places it in the
correct actual weight space. Injectivity of Lie scalar extension, faithful
flatness of field extension and nonvanishing of the original pinned vector prove
`baseChangeRootVector_ne_zero`. Neither this vector construction nor its
nonvanishing theorem requires torus splitness.

The span equality `weightSpace_baseChange_eq_span`, the new equivalence
`baseChangeTrivialization`, and its `baseChangeTrivialization_one` formula
additionally assume `hT : IsSplitTorus T.toGrp`. Under this hypothesis, the
complete weight-space comparison identifies the new weight space with the
scalar-extended span of the original one. Every original vector is a multiple
of the pinned vector by its supplied trivialization. The elementary pure-tensor
scalar identity therefore shows that the new weight space is exactly the line
spanned by the extended pinned vector. `baseChangeTrivialization` is scalar
multiplication by this vector, viewed as an actual linear equivalence from the
new field to the new weight space. Its injectivity uses the nonzero vector; its
surjectivity uses the proved span equality. Its value at one is the extended
pinned vector. These line constructions require no algebraicity assumption on
the field extension.

For a `SplitPinning`, `baseChangeRootDatum` is literally the published
`SplitRootDatum.baseChange` along the actual split character and cocharacter
lattice equivalences. `baseChangeRootDatumEquiv` retains the original root-index
type, uses the covariant character equivalence and contravariant inverse
cocharacter equivalence, and verifies their transpose relation by the published
pairing formula. `baseChangeBase` transports the supplied base through this
root-datum equivalence. Its support is the same original finite set, as proved
by `baseChangeBase_support`; `baseChangeSimpleEquiv` records the corresponding
subtype equivalence. Reducedness is preserved by injective character-lattice
transport: any dependent pair of new roots comes from a dependent pair of old
roots, hence the old equality up to sign transports to the new roots.

`SplitPinning.baseChange` constructs an actual split pinning of the actual
pulled-back group along an algebraic extension of fields. Its torus and inclusion
are the actual pullbacks; splitness and maximality follow from their published
base-change results. Connected reductivity uses the published algebraic-extension
ascent theorem. The root datum and base are the preceding transported objects,
and the Lie pinning uses the constructed weight-line trivializations, reindexed
by `baseChangeSimpleEquiv`. In this assembly the helper's local finite-type
hypothesis follows from smoothness of the supplied connected reductive group,
and its splitness hypothesis is exactly `p.isSplitTorus`. The final `baseChange_rootVector` proves the exact
normalization formula: the new pinned vector for each transported simple index
is `Lie.schemeScalarExtension (1 ⊗ original rootVector)`.

All fields have the same arbitrary universe. Algebraic closedness, infinitude,
perfectness and characteristic restrictions are absent. Algebraicity of the
extension is retained for the assembled `SplitPinning.baseChange`, including its
final root-vector formula, because that assembly uses algebraic-extension ascent.
The module does not construct base-changed normalized root parametrizations or
reflection representatives, prove their ordered-product comparison, or establish
the canonical quotient isomorphism. Those are subsequent consumer obligations.

Integration gives the local instances used here module-specific names to permit
joint imports. Their types, values, and local scopes are unchanged.
