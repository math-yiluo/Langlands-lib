# Finite geometric torsors on the exact geometric CM levels

Author: Worker 57.

This derived construction proves the existing finite geometric torsor predicate
for the original residual action on the exact geometric CM fine level. It
constructs that action in the coarse level's small etale category and an
equivariant isomorphism to the generic pullback of the original normal torsor.
It then transfers the geometric-point condition through this specific
isomorphism and packages the action with the resulting proof.

## Exact objects and prerequisites

The arithmetic parameters are the original totally real field `E`, CM field
`F` quadratic over `E`, central simple unitary datum `D`, imaginary quadratic
field `L` inside `F`, embedding `τ₀`, and CM-compatible signature charts `C`.
The explicit inherited propositions are tensor-pullback preservation,
composition, unit coherence, associativity, unitor comparison and symmetry;
Picard-zero pullback, Mumford square and universal base change; duality
naturality, polarization base change and relative finite Weil transition.
The rational profinite-integer/adele comparison and torsion finite etaleness
inputs also remain explicit.

Fix the exact `q : CMRepresentabilityStatement ...`. All original schemes
and maps use the identical `chosenCMLevelRepresentation ... q` witnesses.
Write `X_U` for `cmSchemeTower ... q` at U, `Xbar_U` for
`cmGeometricSchemeTower ... q` at U, and `π_U : Xbar_U ⟶ X_U` for
`cmGeometricProjection ... q` at U. The geometric schemes are the existing
fiber products with `Spec (AlgebraicClosure F)` over `Spec F`.

For small CM levels V and U, retain `hVU : V.obj.subgroup ≤ U.obj.subgroup`
and normality of `V.obj.subgroup.subgroupOf U.obj.subgroup`. The residual
group `Q = SmallCMResidualGroup D U V` is the existing quotient of U by V.
Let `p : X_V ⟶ X_U` and `pbar : Xbar_V ⟶ Xbar_U` be the original and
geometric tower maps at `smallCMInclusion D hVU`. The existing
`cmGeometricSchemeTower_map_isPullback` makes the square with sides
`π_V`, `π_U`, `pbar` and `p` cartesian.

The further premises are `RelativeDualSchemeExistenceStatement.{0}`,
`RelativeDualSchemeGeometryStatement.{0}`, the exact coarse-level
`CMGeometricCoarseRigidity ... U.obj`, and
`DominantUnramifiedEtaleStatement.{0}`. These are the original normal
torsor and geometric finite-etale cover's named prerequisites. The first
two assert existence of actual relative Picard-zero dual schemes and
smoothness, properness and geometric connectedness of those duals.
The coarse rigidity premise asserts that the specified coarse-level data
have no automorphisms on every admitted algebraically closed field test,
using the same representatives. The criterion says that a dominant,
locally finite type and formally unramified morphism between integral
schemes is etale when its target is geometrically unibranch. The Library
contains the proof
`Langlands.AlgebraicGeometry.DominantUnramifiedEtaleProof.dominantUnramifiedEtale`;
this API continues to take the proposition explicitly.

## Small etale action and equivariant comparison

`cmGeometricNormalEtaleAction_of_dominantCriterion` is an action of Q
in `Xbar_U.Etale`. Its object is `Scheme.Etale.mk pbar`, using etaleness
from the published `cmGeometricNormalFiniteEtale_of_dominantCriterion`.
Its deck maps are exactly those of `cmGeometricNormalQuotientAction`.
The proved `cmGeometricNormalProjection_invariant` bundles each as a
map over `Xbar_U`; extensionality in the morphism-property over-category
reduces the monoid laws to those of the original geometric scheme action.
The `_left`, `_hom` and `_ρ_left` lemmas identify its source, structure
map and deck maps by reflexivity.

Write T for the value of the published
`cmNormalGeometricTorsor_of_dominantCriterion` on the original level.
`cmGeometricNormalEtaleActionPullbackIso` constructs an isomorphism
from the preceding exact geometric action to
`(etaleTorsorPullbackFunctor π_U Q).obj T`. This target is Worker 13's
published generic base change of the original torsor.

The isomorphism uses the identical cartesian square's `isoPullback`,
bundled over `Xbar_U` using its second-projection identity. `Action.mkIso`
requires equivariance. After extensionality and `pullback.hom_ext`,
the first-projection equation follows from
`cmGeometricNormalQuotientAction_projection` and the generic pulled
action's first-projection formula. The second follows from
`cmGeometricNormalProjection_invariant` and the generic second-projection
formula. The `_hom_left` and `_inv_left` lemmas identify the underlying
scheme maps with the same `isoPullback.hom` and `isoPullback.inv`,
respectively, by reflexivity.

## Torsor proof and packaged value

`cmGeometricNormalEtaleAction_isFiniteGeometricTorsor_of_dominantCriterion`
proves exactly `IsFiniteGeometricTorsor Xbar_U` for the constructed action.
The existing predicate requires a finite acting group, a finite and
surjective structure morphism, and the following condition for every
separably closed field Ω in universe zero: for maps
`a b : Spec Ω ⟶ Xbar_V` with `a ≫ pbar = b ≫ pbar`, there exists a
unique `g : Q` with `a ≫ ρbar(g) = b`. Etaleness belongs to the action
object's ambient small etale category.

The proof first calls `IsFiniteGeometricTorsor.pullback` on the published
original torsor along `π_U`. It retains that result's finiteness of Q.
Finiteness of `pbar` comes from the exact published geometric finite-etale
cover. Surjectivity of `p` comes from the original torsor, and
`MorphismProperty.of_isPullback` transports it through the same cartesian
square to `pbar`.

For the geometric-point condition, compose a and b with the constructed
canonical isomorphism to the generic pullback. Its equation over
`Xbar_U` gives equality of their structural projections, so the generic
pulled torsor supplies a unique residual element. Equivariance moves
that element across the isomorphism. Cancellation of its underlying
isomorphism proves the required equation on `Xbar_V`. Composing any
competing equation with that same isomorphism proves uniqueness by the
generic pulled torsor's uniqueness clause. The proof supplies no
globally constant translating element on arbitrary disconnected test
schemes.

`cmGeometricNormalGeometricTorsor_of_dominantCriterion` returns the direct
subtype of small etale actions satisfying this predicate. Its value is
the constructed exact geometric action and its property is the preceding
proof. Its `_val`, `_left`, `_hom` and `_ρ_left` lemmas identify the value,
source `Xbar_V`, map `pbar` and original geometric deck maps by reflexivity.
No new action, torsor predicate or comparison is assumed as a premise.

## Original source and retained obligations

The contextual source is Harris and Taylor, *The Geometry and Cohomology
of Some Simple Shimura Varieties* (2001), III.1, printed pp.90–91,
one-based PDF pp.98–99, especially p.91 for the original moduli problem,
right action, finite-etale forgetting and normal-level Galois cover
with group U/V. III.2, printed p.96, PDF p.104 supplies the geometric
field base change used in cohomology. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The book's imaginary quadratic E, CM F and totally real F+ are this
module's L, F and E.

The original action's inverse-right tower convention remains the one
encoded by `smallCMNormalInverseArrow`; the present construction uses
its published geometric action without changing this convention. The
specific small etale comparison and torsor transfer are internal
deductions from the published original torsor, geometric tower and
cartesian square, together with the generic torsor pullback. They are
not additional displayed assertions attributed to the book. The earlier
source audit found no matching correction in the supplied author
publication-with-errata list; no fresh or exhaustive errata audit is claimed.

Applicable exact representability under the original source hypotheses,
the named dual assertions, source rigidity, full moduli comparison and
canonical-model geometry remain obligations. This conditional torsor
construction does not establish the associated coefficient-sheaf descent
comparison or complete the host task.

All code and prose in this pair are by Worker 57 and use published imports.
The pinned environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
