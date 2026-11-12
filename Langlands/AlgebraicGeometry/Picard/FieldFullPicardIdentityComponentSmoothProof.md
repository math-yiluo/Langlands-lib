# Smoothness of a supplied full Picard identity-component open over a field

`Langlands.AbelianScheme.fieldFullPicardIdentityComponentSmooth` proves exactly
`Langlands.AbelianScheme.FieldFullPicardIdentityComponentSmoothStatement.{u}`.
The universe `u` and field `k` are arbitrary. For the supplied actual abelian
scheme `A`, parameter `P`, universal rigidified family `L`, and local finite
type hypothesis on `P.hom`, the conclusion is smoothness of the actual open
subscheme `openLocusParameter P U` whenever `U` satisfies the published
`IsFullPicardIdentityComponentOpen` predicate. There are no extra premises.

## Implemented proof

The proof first installs the given local finite type hypothesis as an instance.
The published theorem
`Langlands.AbelianScheme.fieldRigidifiedPicardParameterGeometricallyReduced`,
from
`Langlands.AlgebraicGeometry.Picard.FieldRigidifiedPicardParameterGeometricallyReducedProof`,
then supplies `GeometricallyReduced P.hom` for precisely this actual family
and its universal property on all test schemes. That theorem already includes
the field extension and descent arguments required over an imperfect field.

Next, the published
`Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.universalCommGrpObj`
constructs a commutative group object on `P` from the supplied universal family.
Its inputs are all proved results from the imported Library modules:

- `pullbackTensorComparisonIsIso`;
- `pullbackTensorUnitCoherence`;
- `explicitPullbackTensorAssociativity`;
- `tensorMonoidalLeftUnitorComparison`;
- `pullbackTensorSymmetry`;
- `locallyFreeRankOneIffTensorInvertible`;
- `pullbackTensorComposition`.

The tensor and coherence declarations are in `Langlands.Scheme.Modules`;
the local rank-one comparison is in `Langlands.AlgebraicGeometry.Picard`.
The construction transports the tensor group of rigidified classes through
the actual universal classifier. Thus its group law acts on the parameter
scheme itself. The code installs the induced `GrpObj (Over.mk P.hom)` instance,
using the canonical identification of `P` with `Over.mk P.hom`.

Mathlib's `AlgebraicGeometry.smooth_of_grpObj`, from
`Mathlib.AlgebraicGeometry.Group.Smooth`, now gives `Smooth P.hom` from the
group object, local finite type and geometric reducedness. It applies over
arbitrary fields; its proof passes to an algebraic closure and descends
smoothness.

Finally, the definition of `openLocusParameter P U` makes its structure map
`U.ι ≫ P.hom`. The open immersion `U.ι` is smooth, and smoothness is stable
under composition. The resulting smoothness concerns `U.toScheme` with the
restricted structure sheaf. The proof uses the whole ambient parameter's
smoothness, so it works for every supplied open and does not need the
identity-component carrier equality.

## Provenance and scope

Worker 2234 wrote this derived assembly, completing the earlier conditional
draft with the now-published geometric-reducedness theorem. The new content
is the composition of the published group-object construction, its proved
coherence inputs, the geometric-reducedness proof, and Mathlib's smoothness
and open-immersion results. The mathematical provenance of these inputs
remains in their respective companions; the target's literature comparison
remains in its unchanged statement companion.

The proof asserts no existence of a universal parameter or of an
identity-component open. It supplies no comparison with the chosen dual
scheme. All published statements and dependencies are used unchanged, and
the separately owned component-comparison, openness and existence workflows
are not needed in this assembly.
