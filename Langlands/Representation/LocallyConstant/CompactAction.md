# Smooth diagonal representations on locally constant functions

This internal construction extends the published compact-action locally constant
function construction to coefficients in an arbitrary smooth representation over
a commutative ring. It uses Mathlib's actual `LocallyConstant` module, linear
postcomposition and continuous pullback. It retains every locally constant
function. The entry declaration is
`Langlands.CompactAction.CompactContinuousAction.locallyConstantModuleCoefficients`.

The space, group, coefficient ring and coefficient carrier have independent
universes `uX`, `uG`, `uR` and `uV`. The function carrier lies in
`Type (max uX uV)`. The coefficient module has no topology. No Hausdorff,
local compactness, compactness of the group, field, admissibility or finite
dimensionality assumption is imposed.

## Diagonal action and smoothness

For a topological space `X` with a group action whose individual operators are
continuous, `diagonalRepresentation ρ` acts on the whole module
`LocallyConstant X V` by

```text
(g f)(x) = ρ(g)(f(g⁻¹ x)).
```

It is the composite of Mathlib's linear pullback along the continuous inverse
action map and linear postcomposition by `ρ(g)`. The identity and multiplication
laws follow pointwise from the original action and representation laws.
`pullbackIntertwiner` retains every original continuous equivariant domain map;
`coefficientIntertwiner` retains the original equivariant coefficient linear map.
These algebraic constructions do not require compactness or smoothness.

Now suppose the group is a topological group, its action on `X` is jointly
continuous, `X` is compact, and `ρ` is smooth. A locally constant function on
`X` has finite image. `commonOpenStabilizer` intersects the published open spatial
function stabilizer with the finite intersection of the actual representation
stabilizers of every value in that image. Their openness follows from the
published open-stabilizer characterization of smooth coefficient vectors.
`mem_commonOpenStabilizer` identifies exactly these two conditions.

`diagonalRepresentation_isSmooth` uses this subgroup as the fixing subgroup
of the given function. Spatial invariance under its inverse replaces
`f(g⁻¹ x)` with `f(x)`, and coefficient fixedness finishes the equation.
`smoothRepresentation` bundles the actual function module and this proof in
`SmoothRep`. The empty space and empty image are covered by the same finite
intersection construction. The common subgroup is a sufficient fixing subgroup;
no equality with the full diagonal stabilizer is asserted.

## Functors in domains and coefficients

For the published category `CompactContinuousAction G`,
`locallyConstantModuleAction S A` is this actual function module with the smooth
diagonal action of `A`. `locallyConstantModulePullback` is precomposition by
every original continuous equivariant map. Its pointwise formula is proved.
Identity and composition hold pointwise, giving
`locallyConstantModuleFunctor A` from the opposite compact-action category to
smooth representations.

`locallyConstantModuleCoefficientMap a` is pointwise postcomposition by the
original coefficient intertwiner, with its evaluation formula and naturality
under all domain maps. Identity and composition are proved pointwise, giving
`locallyConstantModuleCoefficients`, a functor from smooth coefficients to these
contravariant function functors. The function module is never replaced by a
chosen smooth submodule.

## Provenance and scope

This is internal derived mathematics from the current Library's
`Topology.GroupAction.CompactLocallyConstantFunctor`, its compact spatial
stabilizer construction, `Representation.Category.Basic` and
`Representation.Smooth.Transfer.StabilizerProof`, together with pinned Mathlib's
`Topology.LocallyConstant.Algebra`. It introduces no new original-literature
claim. The action formula, finite stabilizer intersection and functor laws are
implemented and proved here. Existing imported pairs remain unchanged.

This generic unit prepares module coefficients for geometric consumers. It
constructs no analytic or etale site, sheaf, support condition, cohomology,
arithmetic coefficient system or Harris specialization. Those require separate
constructions on their actual spaces and sites. No exactness of the function
functor or comparison theorem is claimed.
