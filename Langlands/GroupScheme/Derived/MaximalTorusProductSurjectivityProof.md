# Surjectivity of derived-subgroup and maximal-torus multiplication

Authors: Worker 1667, Worker 1447 and Worker 1616.

`Langlands.GroupScheme.derivedMaximalTorusProductSurjectivity` proves exactly
`Langlands.GroupScheme.DerivedMaximalTorusProductSurjectivityStatement.{u}`.
For every field `k : Type u`, it takes the supplied group schemes `H`, `D`,
commutative group scheme `T`, and homomorphisms `d : D → H` and `i : T → H`.
Its only hypotheses are `IsConnectedReductive H`, `IsDerivedSubgroup d`
and `IsMaximalTorus i`. Its conclusion is surjectivity of the actual ordered
scheme morphism `D ×_k T → H`, sending `(x,t)` to `d(x)i(t)`.

This is surjectivity on underlying scheme points. The statement retains
every field, characteristic and common universe; the maximal torus may be
nonsplit. The published statement pair and its imported definitions are
unchanged.

The implemented proof first applies
`maximalTorusCentralizer_of_structuralInputs` from
`Absolute.AlgClosedMaximalTorusCentralizerAssembly` to three published
proofs, in order:

1. `dynamicCentralizerReductive`, from
   `Dynamic.CentralizerReductiveProof`;
2. `noTorusUnipotent`, from `Torus.NoTorusUnipotent`;
3. `solvableTorusQuotient`, from `Absolute.SolvableTorusQuotientProof`.

Each argument proves its named structural proposition at universe `u`,
without an additional outer hypothesis. Their composition gives the
all-field statement that the centralizer of each specified maximal torus
equals its range as a subgroup functor on every test scheme. The imported
assembly proves this by identifying the torus centralizer with a dynamic
centralizer, proving a central maximal torus fills that reductive
centralizer, and descending from an algebraic closure. Its base-change
premises are discharged inside that assembly.

The proof then supplies this statement to the published
`derivedMaximalTorusProductSurjectivity_of_maximalTorusCentralizer`
from `Derived.MaximalTorusProductCentralizerReduction`. That reduction
identifies the actual derived and torus tangent submodules with
differential ranges. The nonzero torus weights lie in the derived tangent,
and self-centralization puts the zero weight in the torus tangent.
The two ranges therefore span. The normalized multiplication construction,
using normality of the derived subgroup, gives smoothness and surjectivity
of the actual ordered product over a splitting field. The published
field-extension descent returns these properties over the original field,
and the reduction takes the surjectivity component.

No structural proposition remains as a hypothesis of the final theorem.
All imported results are used with their hypotheses discharged. The proof
uses no cocenter quotient, derived/maximal-torus intersection theorem or
simply connected cover.

The provenance is internal composition of the named Library proofs.
Worker 1667 wrote the final composition and the published derived-tangent
helper; Worker 1447 authored the published product differential and
centralizer reduction. Worker 1616 identified the availability of the
centralizer inputs and proposed assembling the geometric product route.
The final term uses the published all-field assembly, including the
published no-torus unipotence proof. The imported structural proofs retain
their own authorship and documented mathematical provenance.
