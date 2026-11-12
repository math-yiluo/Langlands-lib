# The compact-group composite-functor identification

Author: Worker 141.

`compactGroupCompactCompositeStatement_proof` proves the published proposition
`CompactGroupCompactCompositeStatement.{w,w',u}`. It retains the independent
universes of both supplied derived-category models and of the original ring,
group and space, all original assumptions, every natural degree, and naturality
for every morphism of smooth equivariant sheaves. The argument uses the actual
published compact-section functor and derived compact-section complex.

The geometric input is proved in InjectiveAcyclic. Compact sections of the
actual degree-zero smooth Godement sheaf are identified with a cofree smooth
representation using its coinduced indexed-family model. Cofree representations
are acyclic for invariants. An injective smooth sheaf retracts off its monic
Godement coaugmentation, so its compact sections are invariants-acyclic as well.
The explicit trivial-source Hom identification, its derived natural
isomorphism and exact forgetting of the coefficient module structure give the
same positive-degree vanishing for ordinary additive Hom from the trivial
smooth representation.

Fix an injective resolution of a smooth sheaf and extend it by zero from the
natural numbers to the integers. Exact forgetting of modules and the natural
trivial-source Hom identification rewrite invariant compact cohomology as the
cohomology of termwise additive Hom into compact sections of that resolution.
The helper compactGroupResolutionIso is the composite of the published
DerivedPlus homologyIso and homologyResolutionIso. Their naturality gives the
resolution formula's naturality; the natural compact Hom complex comparison
then gives compactResolutionHomologyIso and its naturality.

Every term of the compact-section resolution image is Hom-acyclic by the first
step. AcyclicHomology therefore identifies this Hom cohomology with shifted
morphisms in the actual supplied derived category of smooth representations,
from the trivial representation in degree zero to the compact-section
resolution image. DerivedPlus.derivedComplexIso identifies that image with the
published derived compact-section complex. Transport along this isomorphism
produces compactCompositeAddEquiv.

For naturality, the implementation chooses the published lift of a sheaf
morphism to the two injective resolutions. The cohomology/resolution formula,
the canonical acyclic Hom map and the derived compact-resolution comparison
are all natural for that chain map. Composing these three equalities and the
shifted inverse resolution isomorphisms gives precisely the published
postcomposition equation. The final theorem supplies these equivalences and
that equation under the unchanged quantifiers.

The proof introduces no joint-action continuity premise, separation or local
compactness assumption on the space, restriction on the coefficient ring, or
extra condition on the compact group. CompactAction derives joint continuity
from the original stable-neighbourhood condition, and compactness is used in
the indexed-family comparison. Standard derived-category models of abelian
groups are used only internally to relate classical derived functors to
resolution cohomology; the theorem imposes no additional supplied model.
