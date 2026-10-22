# Proof of the actual finite-quotient comparison

Authors: Worker 22 and Worker 120. Worker 22 constructed the proof in the
shared revision-3 draft of task `d00aea55-1beb-48a0-8f3c-d6c87b070309`.
Worker 120 checked that proof against the published dependencies, added
explicit forward-map identities for the linear equivalence and an unapplied
target-signature check, and prepared this contribution for independent review.
The task is `4ffc2a54-547e-47f8-99d0-c00a105dcb1c`, revision 2.

The theorem `Langlands.Continuous.finiteQuotientComparisonIsIso` proves
exactly `Langlands.Continuous.FiniteQuotientComparisonIsIso`.
The proof constructs `finiteQuotientComparisonIso`, identifies its forward
map with the named `finiteQuotientComparison`, and also provides
`finiteQuotientComparisonLinearEquiv`. Its `toLinearMap` and `apply`
identities identify the linear equivalence's forward map with that same
canonical comparison. It preserves every natural degree
and arbitrary common universe, with exactly the compactness, local
compactness and genuine discrete-module hypotheses of the statement.

## Finite descent of the actual cochains

Induction using compact-open evaluation proves that recursively evaluating
Mathlib's nested continuous functions is jointly continuous on tuples
when `G` is locally compact.

Right translations preserving a function form a subgroup. If a function
from a compact group to a discrete space is continuous, the set of pairs
on which translation changes its value is closed. Projection along the
compact factor is closed, so the stabilizer is open. The stabilizer has
finite index; its normal core is closed and of finite index and is
therefore open. Thus the function is constant on right cosets of an
open normal subgroup.

Apply this argument to the finite power `G^n`. Intersecting the inverse
images of its normal period subgroup under the coordinate insertions
gives a single open normal subgroup `N` of `G` whose power consists of
periods. Equality of quotient tuples implies that their coordinatewise
ratios lie in `N`, proving constancy on fibers. Quotient representatives
then define the continuous function on the discrete quotient tuples,
with an explicitly proved factorization identity.

For covariant cochains, each element of `N` acts trivially on every
quotient tuple. Covariance and constancy on fibers imply that it fixes
every coefficient value. The descended function therefore lies in the
actual fixed submodule `A^N`. Quotient induction proves covariance for
the actual quotient representation. The local `nestedLift_covariant` lemma
uses the published discrete `nestedLift`: equality after nested evaluation,
the evaluation/action formula and the lift/evaluation identity turn
covariance into invariance. This yields a finite-stage invariant nested
cochain, and the
resolution-map evaluation formula together with evaluation injectivity
proves that inflation returns the original cochain.

Representatives likewise prove that the actual finite-stage continuous
cochain inflation is injective. Combining this with the discrete cochain
comparison proves `finiteStageCochainMap_injective`. Finite descent proves
that those stage maps jointly exhaust the underlying continuous complex.
The filtered-colimit criterion in types, reflection by the forgetful
functor from modules, and the degreewise criterion for complexes give
`finiteStageCochainCoconeIsColimit`.

## Passage to homology

The proof includes a direct filtered-homology argument for short complexes
of modules. The actual kernel/cycle isomorphism represents a cycle by a
module element annihilated by the outgoing differential. Surjectivity of
the actual homology projection represents every class by such a cycle.
The projection/inclusion identity and the explicit module cokernel
criterion show that a projected cycle is zero exactly when its
representative is an actual incoming boundary.

For a cocone with injective component maps in the middle and outgoing
terms and joint surjectivity in the incoming and middle terms, lift a
cycle representative to a stage. Injectivity in the outgoing term
detects that its lift is a cycle, giving surjectivity on homology.
If a stage class is killed in the cocone, lift a boundary witness to a
possibly different stage. Filteredness supplies a common later stage.
Injectivity in the middle term gives the boundary equation there, so
the class is zero at that stage. Applying this to the difference of two
classes gives the filtered equality criterion. This proves
`homologyCoconeIsColimit`; exactness of the desired comparison is not
assumed.

Apply this result to the actual three-term short complex at degree `q`
of the finite-quotient cochain diagram. The finite-stage injectivity and
exhaustion just proved supply all its hypotheses. This gives
`finiteStageHomologyCoconeIsColimit`, including at degree zero through
Mathlib's actual `ComplexShape.up` short-complex construction.

The colimit universal property now gives an isomorphism from the actual
finite-quotient cohomology colimit to homology of the forgotten continuous
complex. Compose it with the actual homology-preservation isomorphism of
the topology-forgetful functor. The forward map is definitionally the
previously constructed `finiteQuotientComparison`: this equality compares
two maps, not the definitions of the two cohomology objects.
It proves the `IsIso` instance and the stated linear equivalence. The
final theorem quantifies over the exact imported proposition. An unapplied
assignment to `FiniteQuotientComparisonIsIso.{u}` checks the full theorem
signature, with no additional outer assumptions.

## Dependencies and provenance

The entry import is
`Langlands.Cohomology.Continuous.FiniteQuotientComparisonStatement`,
which imports the canonical comparison map and its published prerequisites.
The comparison map is published at
`1058c134c0d2fb45ec96d08ea2956983aaac1d80`, and the cochain-comparison
proof is published at `22b4f024e0d4218752e970d09329d1799f6d81d1`.
The exact statement, canonical map, and all their dependencies are present
unchanged in the refreshed Library base
`354dfade2c499262492d6db74cb58fd887ffed5f`.
The proof record must
set `statement_declaration` to
`Langlands.Continuous.FiniteQuotientComparisonIsIso`.

The mathematical source is Serre, *Local Fields*, Greenberg translation,
Springer (1979), X Section 3, printed pages 154–155 / PDF pages 160–161.
The nested-model compactness argument and the explicit filtered-homology
element proof above are derived implementation work. Literature ID
`serre-1979-local-fields`, PDF SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 120 read the original printed pages 154–155 (PDF pages 160–161).
The direct-limit formula and continuous-cochain assertion occur on printed
page 154. Serre states them for profinite Galois groups and discrete
topological modules. The compact locally compact formulation here is the
already published target's generalization: the right-stabilizer and
normal-core arguments above prove it without assuming total
disconnectedness or Hausdorffness. The arbitrary coefficient ring supplies
the linear structure; the descent and homology arguments apply to its
underlying additive module. This contribution reuses Worker 22's proof
draft with attribution, and imports Worker 54's published cochain proof
unchanged.

Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, version 1:
Lean 4.34.0 (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`);
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Continuous corestriction and its laws remain outside this proof.
