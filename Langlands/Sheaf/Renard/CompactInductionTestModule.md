# Pointwise test modules on the original compact induction

This pair constructs the module used to define the induction sheaf in Renard
2026, III.3.2, printed pp.84–85 / PDF pp.90–91: the existing compact-induced
representation is a nondegenerate module over the existing pointwise algebra
`D(H \ G)`, with its compatible original right-translation action. The
reconstruction of a complex sheaf and the induction sheaf functor remain
subsequent obligations, using the actual II.2.5 constructions.

All names below have prefix
`Langlands.Sheaf.Renard.CompactInductionTestModule`. The group has its
original topology, is locally compact, and `H` is an explicitly closed
subgroup. The coefficient representation `σ` is any complex representation
of `H`; restricting the functor to the smooth representation category gives
Renard's intended input. No topology or finite-dimensionality is required
on its module. The group universe `uG` and coefficient-carrier universe `uV`
are independent. The actual compact-induced carrier has universe
`max uG uV`, exactly as in the published induction model. Morphisms in each
bundled category use a fixed common coefficient-carrier universe.

`productFunction H σ φ f g` is literally

`φ (quotientMap H g) • eval H σ f.val g`.

Here `f` belongs to the published `Langlands.Induction.CompactFunctions`,
and `φ` may be any locally constant complex function on the existing
`LeftQuotient H`; its compact support is not needed for this multiplier.
Covariance follows from the original subgroup covariance and constancy of
`quotientMap` under left multiplication by `H`. Local constancy follows
from local constancy of the quotient scalar and the published
`eval_isLocallyConstant` for the original smooth induced function.

The product's actual projected nonzero support is closed: covariance
identifies its preimage under the original quotient map with its nonzero
support on `G`, which is closed by local constancy. That projected support
is contained in the original vector's compact projected support. These two
facts prove compactness. `multiplier` passes this actual covariant function
to the published `compactFunctionOfLocallyConstant`, which derives a single
uniform open right stabilizer from local constancy and compact projected
support for a closed subgroup of a locally compact group. Thus the result
has the original compact-induced carrier; no parallel induction space or
assumed uniform smoothness is introduced. `multiplier_apply` records its
literal values.

`testModule` restricts this pointwise multiplication to the original
`Langlands.HarmonicAnalysis.PointwiseTestAlgebra.Carrier (LeftQuotient H)`.
The nonunital module laws hold pointwise in the original coefficient
module. This named instance-reducible definition is installed explicitly
where needed; it is not a global instance that guesses closedness of `H`.
`testModule_scalarTower` relates this action to the original complex
scalars of compact induction.

For an original compact-induced vector `f`, its own projected support is
open as well as closed: its preimage is the complement of the locally
constant evaluation function's closed zero fibre. It is already compact by
membership in `CompactFunctions`. `testModule_nondegenerate` uses the
published characteristic idempotent of this very compact-clopen support.
At a nonzero value the characteristic is one, and at a zero value its
product is zero. Hence the idempotent fixes `f`, including the zero vector
and its empty support. No assumption of nondegeneracy is supplied.
`moduleObject` bundles precisely this original carrier and action in the
published `NondegenerateModuleCat`.

`canonicalComplexModule` and `canonicalScalar_eq` prove that the canonical
complex structure recovered from this nondegenerate test module agrees
with the original complex structure of compact induction. They apply the
published `NondegenerateScalars.module_eq_of_compatible` and its scalar
formula to the actual scalar tower. `canonicalAction` retains the literal
right-translation functions and verifies linearity for these canonical
scalars, using that comparison. It does not transport the carrier or
change the action.

`action_compatible` is the original III.3 covariance law. On the quotient
we use the existing inverse right action `homogeneousAction` from
`HomogeneousSections`; its inverse pullback on tests gives

`compactInduced H σ g (φ • f) = testRepresentation g φ • compactInduced H σ g f`.

Both sides have value `φ(H k g) • f(k g)` at `k`.
`compatibleObject` therefore bundles the original module and translations
in the published `CompatibleTestAction` category, with the required
canonical complex scalar structure.

`moduleMap` is the original `compactInducedMap` on the original carrier.
It commutes with multiplication by tests because the original coefficient
intertwiner is complex-linear. `compatibleMap` also retains its original
right-translation equivariance. `functor` assembles these objects and maps
into the existing compatible-action category; its identity and composition
laws are those of the original pointwise postcomposition maps. It is
defined on all `Rep ℂ H`, so it restricts in particular to `M(H)`.

The construction's weaker group hypotheses do not alter any source theorem:
Renard's Hausdorff locally compact totally disconnected group and closed
subgroup case is included. This module starts with the concrete quotient
and asserts no identification of arbitrary transitive spaces, so its maps
do not need the separate countability-at-infinity condition. That condition
remains required for the transitive comparison in III.3.2.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.3.2, printed pp.84–85 / PDF pp.90–91,
the paragraph constructing the nondegenerate `D(H \ G)`-module by pointwise
multiplication before the induction sheaf. Source SHA256:
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
