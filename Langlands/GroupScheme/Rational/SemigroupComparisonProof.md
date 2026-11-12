# Proof: semigroup functoriality, smooth quotients and CGP 3.3.10 intersections

Workers 4043 and 4030. This module proves the published
`Langlands.GroupScheme.RelativeRoot.SemigroupComparisonStatement.{u}` of
`Langlands.GroupScheme.Rational.SemigroupComparisonStatement` at an arbitrary
universe `u`. The theorem is

```lean
theorem semigroupComparison : SemigroupComparisonStatement.{u}
```

Its type is exactly the published proposition. That proposition is the
conjunction of three statements, each over every field `k : Type u`, with every
smoothness, affineness, connectedness, split-torus, all-test action and
representative hypothesis kept:

- `SemigroupFunctorialityStatement`: an equivariant homomorphism carries the
  actual semigroup subgroup functor into the corresponding one on every test
  scheme.
- `SemigroupSmoothQuotientStatement`: a smooth equivariant surjection, with
  smoothness and surjectivity properties of the actual scheme morphism, induces
  an actual smooth surjective morphism between arbitrary representatives of the
  two semigroup subgroup functors.
- `SemigroupIntersectionStatement`: CGP Proposition 3.3.10. The intersection
  with an invariant smooth connected closed subgroup is that subgroup's
  semigroup subgroup when zero is not in the semigroup, or when the subgroup is
  solvable, or when it is normal. Zero is allowed in the last two cases.

Source: Conrad, Gabber and Prasad, *Pseudo-reductive Groups*, 2nd edition
(2015), registered as `conrad-gabber-prasad-2015-pseudo-reductive`. The
functoriality and the smooth quotient are in the paragraph after Example 3.3.7
(printed p.111). The intersection is Proposition 3.3.10 (printed pp.112–114).

## Proof route

The proof is a composition of published Library results. It introduces no new
hypotheses and does not change any published file.

1. `semigroupComparison_of_fourPrerequisites` (module
   `Rational/SemigroupComparisonFourPrerequisites`) proves the exact target from
   `SemigroupComparisonFourPrerequisites.{u}`. That is the conjunction of
   `AdjointQuotientExistenceStatement`, `FixedCenterContainingTorusStatement`,
   `NormalAdjointEquivariantRetractionStatement` and
   `Torus.SolvableFixedContainmentConnectedStatement`. Inside that reduction,
   functoriality and the smooth quotient come from the published unconditional
   `semigroupFunctoriality` and `semigroupSmoothQuotient`. The zero-excluded
   intersection case uses the published realization and coordinate comparison.
   The solvable case with zero uses solvable fixed-containment connectedness.
   The normal case with zero follows CGP's argument. It descends from an
   algebraic closure, passes to unipotent-radical quotients and full-centre
   adjoint quotients, and finishes with the equivariant retraction onto a
   normal adjoint subgroup.
2. The fixed-torus input is the published theorem `fixedCenterContainingTorus`.
   The solvable connectedness input is the published theorem
   `Torus.solvableFixedContainmentConnected`.
3. Adjoint quotient existence (`hExist` in the proof) is assembled from the
   following published results:
   - `schemeTheoreticCenterExistence` gives a closed subgroup `z : Z ⟶ G`
     representing the full all-test centre. Its range is normal by
     `IsSchemeTheoreticCenter.isNormal`.
   - `normalSubgroupQuotientExistence` gives an affine fppf quotient
     `q : G ⟶ Q`, locally of finite type, whose actual kernel range is that
     centre.
   - `centerQuotientReductive` shows that `Q` is connected reductive.
   - `CenterQuotientCenter.center_eq_bot_of_secondCenterTrivial` shows that `Q`
     has trivial centre. Its input is
     `SecondCenter.secondCenterTrivial_of_centralDerivedProduct` applied to
     `reductiveCentralDerivedProduct`.
   - `isAdjointQuotient_of_fppf_kernel_range` turns the flatness, surjectivity,
     local finite presentation and kernel equality of `q` into
     `IsAdjointQuotient q`.
4. The normal adjoint retraction (`hRetraction` in the proof) is
   `normalAdjointEquivariantRetraction_of_semisimpleNormalComplement`, applied to
   `semisimpleNormalComplement_of_almostSimpleGeneration`. That is applied to
   `semisimpleAlmostSimpleGeneration_of_rootLines`, whose inputs are the
   published `normalReductiveCenter`, `absoluteRootVectorLine`,
   `maximalTorusConjugacy` and root generation. Root generation is
   `semisimpleRootGenerationReduction rootRankOneFactorization`, applied to the
   maximal-torus centralizer theorem
   `algClosedMaximalTorusCentralizer_fromQuotient dynamicCentralizerReductive
   solvableTorusQuotient`.

The two compositions in steps 3 and 4 are local `have` proofs. They are not
exported as theorems, because separate tasks target those two statements under
their own names. The step 3 assembly has the same form as Worker 4030's staged
proof candidate `fd359a6e-10fa-4db3-a6a8-c88973831068` for
`AdjointQuotientExistenceStatement` (Task 4030). Its text follows that
candidate, so Worker 4030 is a coauthor.
