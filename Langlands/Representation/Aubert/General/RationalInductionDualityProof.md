# Natural same-parabolic induction duality on the actual rational-point group

Module `Langlands.Representation.Aubert.General.RationalInductionDualityProof`,
namespace `Langlands.Aubert.General.RationalPointFamily`.

## Result

`rationalNaturalInductionDuality : RationalNaturalInductionDualityStatement.{u, v}`
proves the published proposition
`Langlands.Aubert.General.RationalPointFamily.RationalNaturalInductionDualityStatement`
(module `Langlands.Representation.Aubert.General.RationalInductionDualityStatement`) in
all universes `u` and `v`, under exactly its premises. Let `k` be a nonarchimedean local
field and `G` a connected reductive group over `k`, with a maximal split torus, a generic
cocharacter and a set `I` of simple roots. Give `RationalPoint k G.X` its published point
topology and assume the statement's topological premises. Then normalized induction from
the actual standard parabolic `parabolic i ν I` commutes with the smooth contragredient.
Concretely, the theorem gives isomorphisms `(F.obj A).contragredient ≅ F.obj
A.contragredient` for admissible `A`, natural in morphisms of admissible objects.

## Proof

The proof is a term that combines three published or companion results:

1. `rationalNaturalInductionDuality_of_compact_of_modulus` (module
   `RationalInductionDualityAssembly`) reduces the target to
   `BruhatTits.DynamicParabolicQuotientCompactStatement` and
   `RationalParabolicModulusStatement`.
2. The first input is the published proof
   `Langlands.BruhatTits.dynamicParabolicQuotientCompact`.
3. The second input is the published reduction
   `rationalParabolicModulus_of_reductiveUnimodularity` (module
   `RationalLeviUnimodularityReduction`). It is applied to
   `rationalReductiveUnimodularity`, the companion module
   `RationalReductiveUnimodularityProof` (unimodularity of `G(k)`, proved through the
   adjoint-determinant bound on the modular character), and to the published proof
   `Langlands.GroupScheme.dynamicCentralizerReductive` (standard Levi representatives
   are connected reductive).

No premise is added, and the statement's Lean/Markdown pair and its imports are
unchanged.

## Provenance

Internal assembly of Library results. Casselman's compact-picture duality
`i(σ)∨ ≅ i(σ∨)` is the mathematics behind the published assembly; see the Markdown of
`RationalInductionDualityAssembly`.
