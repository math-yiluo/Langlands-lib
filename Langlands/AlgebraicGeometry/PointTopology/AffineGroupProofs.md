# Actual affine group-point topology proofs

This proof development establishes `AffineGroupPointProperties` for the
existing actual relative points and evaluation topology of an affine group
scheme. The target is the derived group consequence of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Proposition 2.1 and its following paragraph, printed pages 2–3, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The target and the reused actual-scheme mapping proof are published. This
unit imports them by Lean name and proves the target without modifying its
Lean/Markdown pair or any of its imports.

The coefficient ring `R` and value algebra `S` are arbitrary commutative rings
in one arbitrary universe. Only `S` is topologized. The carrier is the
existing `RingPoint R G.X S`, actual morphisms from `Spec S` over `Spec R`.
The group is Mathlib's existing Hom group of the actual group object, selected
explicitly across the point alias. The topology is the existing topology
induced by the global-section point equivalence and evaluation into copies
of `S`; neither the law nor topology is a supplied package.

The Cartesian tensor product in the over category is a limiting binary
product. Its underlying scheme cone is the pullback over `Spec R`.
Affineness follows from affine base change; local finite type follows from
base change on the second projection and composition with the second
factor's structure map. These are properties of the actual chosen
categorical product, established by the public `tensor_isAffine` lemma and
the private local-finite-type tensor lemma.

`continuous_affineSchemePointPair` regards this product as a pullback over
the explicit terminal relative scheme given by the identity on `Spec R`.
The published evaluation-topology pullback theorem makes its compatible-point
comparison a homeomorphism. Every point pair is compatible since relative
morphisms to the terminal object are unique. The comparison is inducing,
and its composite with point pairing equals the continuous inclusion of the
product into this compatible-pair subtype, by the two product projection
identities. This proves pairing continuity in the actual chosen product.

`affineGroupTopological_proof` then applies published functoriality to the
actual multiplication morphism after point pairing, and to the inverse
morphism after a point. These are definitionally the existing Hom
multiplication and inverse. No Hausdorff or local-ring hypothesis is used.
Affineness and local finite type supply full finite-type scope in this
setting, as documented by the published coordinate-algebra bridge.

`affineGroupFunctorial_proof` applies the actual-scheme mapping continuity
proof to each underlying relative homomorphism. It forgets an actual group
scheme isomorphism to the over category and uses the published actual-scheme
point homeomorphism. The published application identity identifies that
homeomorphism with postcomposition by the original homomorphism.

`affineGroupClosedImmersion_proof` specializes the actual-scheme mapping
proofs to the underlying closed immersion. The domain has the subspace
topology on its image, and the image is closed when `S` is Hausdorff. The
reused mapping proof transports the surjective-coordinate-map evaluation
argument through the actual point homeomorphisms; Hausdorffness is required
only for its closed-image branch.

`affineGroupLocalCompactness_proof` keeps its hypotheses separate.
Hausdorffness follows from the actual point homeomorphism and the evaluation
embedding, without finite type or continuity of ring operations. For a
Hausdorff locally compact topological value ring and an affine group scheme
locally of finite type, the coordinate algebra is finite type. The published
algebra-point local compactness proof applies; its topology is transferred
through the actual point homeomorphism. This uses the finite-coordinate
closed embedding and imposes no finite-presentation assumption.

Finally `affineGroupPointProperties_proof` assembles these four properties,
quantifying the topological-ring hypotheses locally as in the target.
It does not prove any particular reductive or subgroup construction,
nonarchimedean group structure, second countability, compact-open subgroup
basis, or actual general linear scheme/matrix topology comparison. Those
and the rest of the five-section program remain separate obligations.
