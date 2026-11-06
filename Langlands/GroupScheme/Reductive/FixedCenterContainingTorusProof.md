# A fixed split torus containing the full centre: proof

This module proves `FixedCenterContainingTorusStatement` (module
`Reductive.FixedCenterContainingTorusStatement`) in every universe `u`, with no
hypotheses. The statement says: let `k` be an algebraically closed field, `G` a
connected reductive group over `k`, `S` a commutative group scheme over `k` that is a
split torus, and `b` an automorphic action of `S` on `G`. Then there are a split torus
`T` and a closed subgroup `j : T ⟶ G` such that the scheme-theoretic centre `center G`
is contained in the range of `j`, and `b` fixes every point of `T`: for every test
object `U`, every `s : U ⟶ S` and `t : U ⟶ T`, `b.act s (t ≫ j) = t ≫ j`.

The module only combines results already in the Library. It adds no new mathematics.

## Declarations

- `fixedCenterContainingTorus_of_algClosedMaximalTorusCentralizer`: proves the target
  from `AlgClosedMaximalTorusCentralizerStatement`, the algebraically closed case of
  Milne's Corollary 17.84. That statement says a maximal torus `j : T ⟶ G` of a
  connected reductive group over an algebraically closed field is its own centralizer:
  `torusCentralizer j = SubgroupFunctor.range j`.
- `fixedCenterContainingTorus : FixedCenterContainingTorusStatement.{u}`: the
  unconditional proof of the target.

## The proof

`fixedCenterContainingTorus_of_algClosedMaximalTorusCentralizer hcent` applies the
Library reduction `fixedCenterContainingTorusSemidirectReduction` (module
`Reductive.FixedCenterContainingTorusSemidirect`) to two arguments:

1. `hcent`, the algebraically closed self-centralization statement;
2. reductivity of semidirect products, which the reduction quantifies over all `k`,
   `G`, `S` and `b`. For each instance this is the Library theorem
   `AutomorphicAction.isConnectedReductive_semidirectProduct_of_isAlgClosed hS hG`
   (module `AutomorphicAction.SemidirectReductive`). It says that `G ⋊_b S`
   (`b.semidirectProduct`) is connected reductive when `k` is algebraically closed,
   `S` is a split torus and `G` is connected reductive.

`fixedCenterContainingTorus` then supplies `hcent` as
`algClosedMaximalTorusCentralizer_fromQuotient dynamicCentralizerReductive
solvableTorusQuotient`. All three of these are Library theorems:

- `algClosedMaximalTorusCentralizer_fromQuotient` (module
  `Absolute.MaximalTorusCentralizerFromQuotient`) proves
  `AlgClosedMaximalTorusCentralizerStatement` from two statements:
  `DynamicCentralizerReductiveStatement` and `SolvableTorusQuotientStatement`.
- `dynamicCentralizerReductive` (module `Dynamic.CentralizerReductiveProof`) proves
  the first of them. It says that, over any field, a closed subgroup representing the
  centralizer of a cocharacter in a connected reductive group is connected reductive.
- `solvableTorusQuotient` (module `Absolute.SolvableTorusQuotientProof`) proves the
  second. It says that a smooth connected affine solvable group over an algebraically
  closed field has a smooth connected unipotent normal closed subgroup whose fppf
  quotient is a split torus.

The full arbitrary-field Corollary 17.84 (`MaximalTorusCentralizerStatement`) is not
used. Torus conjugacy (`MaximalTorusConjugacyStatement`) is not used either; the
companion reduction `Reductive.FixedCenterContainingTorusReduction` would need it.

## How the reduction works

The route below is implemented in the Library module
`Reductive.FixedCenterContainingTorusSemidirect` and is summarized here for
orientation. Let `H = G ⋊_b S`, which is connected reductive by the
second argument above.

1. `AutomorphicAction.exists_maximalTorus_with_fixed_intersection` gives a maximal
   torus `M` of `H` through which `S` factors. Its intersection `T₀` with the normal
   factor `G` is a closed torus of `G` whose points `S` fixes. `T₀` is split because
   every torus over an algebraically closed field is split. `T₀` is the witness.
2. `G` is a normal closed subgroup of the connected reductive group `H`. With the
   self-centralization statement, the Library theorem
   `center_le_comap_of_normal_of_algClosedMaximalTorusCentralizer` shows that the centre
   of `G` lies in the centre of `H`.
3. The centre of `H` lies in the centralizer of `M`. By the self-centralization
   statement, applied to `H` and `M`, that centralizer is `M`.
4. A central point of `G` therefore lies in both `M` and `G` inside `H`. So it lies in
   their intersection `T₀`.

This route does not use conjugacy of maximal tori. Worker 1334 proposed it.

## Axioms

`lean_check` reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
