# Relative local dimension under arbitrary scheme base change

`relativeDimensionBaseChangeInvariance` proves
`Langlands.AlgebraicGeometry.SchemeFiberGeometry.RelativeDimensionBaseChangeInvariance`
in the published statement module. Worker 105 wrote the proof; Worker 1450
checked the scheme reduction and prepared the proof for publication.
The target is Stacks Lemma 29.29.3(1) together with its pointwise sublevel
consequence, expressed using the existing actual scheme fibres and minimum
open-neighbourhood local topological dimension. This dimension takes values
in `WithBot ℕ∞`; it is distinct from the dimension of the local ring.

For any cartesian square with maps `a : P → X`, `b : P → Y`,
`f : X → Z` and `g : Y → Z`, the sole finiteness assumption is that
`f` is locally of finite type. At every point `x` of `P` the relative
local dimension of `b` at `x` equals that of `f` at `a x`. Consequently,
for every natural bound `n`, the actual sublevel of `b` is the inverse
image under `a` of the sublevel of `f`. All four schemes share an
arbitrary universe. They may be nonaffine and nonseparated; the map `g`
is arbitrary. Empty schemes and nonsurjective base changes are included.

## Implemented proof

For an affine scheme over a field, `topologicalKrullDimAt_affine_fieldExtension`
transports the field-extension local-dimension equality along the actual
global-section tensor spectrum isomorphism `affinePullbackTensorIso`.
The `k`-algebra structure on `Γ(X, ⊤)` is induced by the original
structure morphism through `affineStructureMap`; its finite type follows
from local finite type of that morphism and affineness of `X`.
The imported equality `topologicalKrullDimAt_tensorProduct_eq` applies
to `Γ(X, ⊤) ⊗[k] K`. The projection compatibility
identifies the contracted tensor prime with the image of the projected
scheme point under its canonical affine spectrum isomorphism. Scheme
isomorphisms preserve local dimension because they are open embeddings.

For an arbitrary scheme over a field, choose an affine open neighbourhood
of the projected point. Its inverse image in the scalar extension is open.
Pasting the open-restriction square with the scalar-extension square
identifies this inverse image with the affine scalar extension. Open
embeddings preserve local dimension, so the affine result gives
`topologicalKrullDimAt_fieldExtension`. An arbitrary cartesian presentation
of the scalar extension is compared with the chosen pullback through its
canonical isomorphism, retaining the original projection.

For general `f` and `g`, fix `y = b x`. The existing actual fibre comparison
`fiberBaseChangeSquare` is cartesian over the field extension
`κ(g y) → κ(y)` induced by `g.residueFieldMap y`. The structure morphism
of the original fibre is locally of finite type by base-change stability.
Apply the scheme field-extension result at `b.asFiber x`.
`fiberBaseChangeMap_fiberι` proves that its image projects to `a x` in
the original source. The published comparison
`relativeTopologicalKrullDimAt_fiberι` then identifies its local
dimension with the relative dimension at `a x`. This proves
`relativeTopologicalKrullDimAt_baseChange`.

Finally, set extensionality and substitution of the pointwise equality
prove `relativeDimensionSublevel_baseChange`.
`relativeDimensionBaseChangeInvariance` pairs these two results and has
exactly the named target proposition as its type.

## Source and scope

Registered original source:
`stacks-fibre-constructibility-local-dimension-2026-11-04`, SHA-256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`,
Section 29.29, Lemma 29.29.3(1). The source reduces to the corresponding
field-extension algebra lemma; the implemented proof uses the same
reduction through explicit affine open restrictions and actual fibre
pullbacks. The sublevel assertion follows immediately from that equality
and the published definition of the sublevel.

The algebraic local-dimension result is imported from
`FieldExtensionLocalDimension`; that proof and its total-dimension and
flat-integral dependencies are not reproduced here. The affine comparison,
open-restriction argument and projected-point identities above are
internal steps in the reduction from the algebra result to the stated
scheme theorem.

Sublevel retrocompactness, geometric-connectedness constructibility,
filtered fibre descent and completion of Conrad's paper remain separate
obligations.
