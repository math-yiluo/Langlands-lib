# Actual jet tensor coordinates under subgroup-family evaluation

For an actual relative parameter map `a:T→M` over `Spec R`,
`familyCoefficientHom a U V hVU` is precisely pullback of functions along `a`
on arbitrary compatible opens `U` and `V`, with `V ≤ a.left ⁻¹ᵁ U`, as an
`R`-algebra map for the actual induced coefficient algebras. The compatibility
with `R` follows from composition of scheme function pullback and the map's
equation over `Spec R`. This coefficient map does not require affine opens.

For an affine ambient group scheme `G` over `Spec R` and an actual subgroup
family `h:K→G_M`, `familyAmbientProjection` identifies the ambient projection
of the evaluated inclusion `familyHom h a` with the original projection
composed with the actual group pullback projection.

For a group scheme `K` affine over its base, `baseChangeSectionsRingMap_smul`
shows that actual jet pullback preserves coefficient multiplication through
the actual section-ring map on the bases. The base opens here may be arbitrary
compatible opens. The proof uses the actual cartesian jet projection square.

`ambientTensorCoordinates_family_baseChange` assumes that the ambient group
`G` over `Spec R` is affine and that `K` is affine over `M`. It takes affine
opens `U` in `M` and `V` in `T`, with `V ≤ a.left ⁻¹ᵁ U`, and proves that
actual tensor restriction commutes with subgroup-family evaluation. Its
coefficient tensor map is the right tensor extension of `familyCoefficientHom`,
and its section map is the actual `baseChangeSectionsRingMap`. The proof checks
pure tensors using literal coordinate-function pullback and the cartesian
projection law, then extends by additivity. The formula uses the actual
pullback map.

`homSections_ambientTensorCoordinates` assumes that the ambient group `G`
over `Spec R` is affine, that both source groups `K` and `L` are affine over
the common base `S`, and that `U` is an affine open of `S`. For an actual
source group homomorphism `f:L→K` and an inclusion `h:K→G_S`, it proves
compatibility of ambient tensor restriction with the actual jet section map
`homSections f`. On coordinate generators this is pullback of the actual
ambient function composed with `f`. Tensor induction extends the formula.
In particular, under these hypotheses, actual inclusion-compatible source
isomorphisms preserve the resulting kernels.

This is an internal consequence of the imported actual jet base change,
coordinate naturality, group-homomorphism section maps, tensor generators and
subgroup-family evaluation APIs. In addition to the individual affineness and
open hypotheses specified above, the formulas impose no smoothness, flatness
or finite-presentation premise. Kernel reflection along faithfully flat covers
is separate.
