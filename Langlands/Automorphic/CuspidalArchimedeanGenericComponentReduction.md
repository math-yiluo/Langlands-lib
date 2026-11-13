# Generic components from irreducible admissible components and Whittaker functionals

Worker 174 wrote this module for task `a2cfc970-9e20-4d56-b053-8f91a2e0b5cc` (Task 5720). The
task's target is `Langlands.Global.CuspidalArchimedeanParameterExistenceStatement`. The
Library module `Langlands.Automorphic.ArchimedeanParameterReduction` reduces that target to
two local statements and one global premise,
`Langlands.Automorphic.CuspidalArchimedeanGenericComponentStatement`. This module proves the
global premise from the two subspace statements of the Library module
`Langlands.Automorphic.CuspidalArchimedeanPlaceComponent`:

- (G1) `CuspidalArchimedeanIrreducibleAdmissibleComponentStatement`: every actual cuspidal
  realization has, at every infinite place, a subspace that is irreducible for the place
  actions there and admissible for the compact group;
- (G2) `CuspidalArchimedeanWhittakerFunctionalStatement`: every nonzero place-stable subspace
  of a cuspidal operator realization carries a Whittaker functional, nonzero on it, for some
  nondegenerate character.

Neither G1 nor G2 is proved here. The module proves the implication "G1 and G2 imply the
global premise" and the facts about place actions that it needs. All declarations are in the
namespace `Langlands.Automorphic`.

## Statement

`CuspidalArchimedeanGenericComponentBridgeStatement.{u}` is the proposition

`CuspidalArchimedeanIrreducibleAdmissibleComponentStatement.{u} →
CuspidalArchimedeanWhittakerFunctionalStatement.{u} →
CuspidalArchimedeanGenericComponentStatement.{u}`.

Provenance: internal. It joins the two Library statement modules named above. The three
propositions are unchanged Library statements, and the implication adds no hypothesis to
any of them.

## Restriction to a stable subspace

In the namespace `PlaceComponent`, let `κ : Representation ℂ K V` be a representation of a
group `K` and `π : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ V` a Lie action, and let `W` be a subspace with
`hW : IsStable κ π W` (both actions map `W` into itself).

- `restrictCompact hW : Representation ℂ K W` is the subrepresentation of `κ` on `W`, and
  `restrictLie hW : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ W` sends `X` to the restriction of `π X` to `W`.
  The lemmas `restrictCompact_apply` and `restrictLie_apply` say that both act on `W` as
  `κ` and `π` do on `V`. These are definitions for this proof (internal provenance); they
  are the restrictions of the source's actions to a `(𝔤, K)`-submodule.
- `isFiniteVector_restrictCompact`: if `x ∈ W` is a `K`-finite vector of `κ`, it is a
  finite vector of the restriction. The orbit span of `x` in `W` maps injectively into its
  orbit span in `V`, which is finite-dimensional.
- `isIrreducibleGKModule_restrict`: if `W` is irreducible (`IsIrreducible κ π W`), then
  `Archimedean.IsIrreducibleGKModule (restrictCompact _) (restrictLie _)`. `W` is nontrivial
  since `W ≠ ⊥`. A subspace `U` of `W` stable under the restricted actions has an image in
  `V` that is stable and contained in `W`. That image is `⊥` or `W`, so `U` is `⊥` or `⊤`.
- `isAdmissibleGKModule_restrict`: if `IsAdmissible κ W`, then
  `Archimedean.IsAdmissibleGKModule (restrictCompact hW)`. Composing with the inclusion of
  `W` maps the restricted intertwiners `ℂ^d → W` injectively and linearly into
  `intertwiners κ W d τ`, which is finite-dimensional.
- `isRealGenericGKModule_restrict` and `isComplexGenericGKModule_restrict`: if
  `IsRealGeneric π W` (respectively `IsComplexGeneric`), then the restricted Lie action
  satisfies `Archimedean.IsRealGenericGKModule n` (respectively
  `IsComplexGenericGKModule n`). The functional is `ℓ ∘ W.subtype`. It is nonzero because
  `ℓ` is nonzero at a vector of `W`. The coefficients and the Whittaker identity are those
  of `ℓ` on `W`.
- `isRealGKModule_restrict` and `isComplexGKModule_restrict`: if `(κ, π)` on `V` satisfies
  `Archimedean.IsRealGKModule n κ π` (respectively `IsComplexGKModule`), then the
  restriction to `W` satisfies it too. Finite vectors restrict as above, and covariance
  restricts pointwise. Continuity and differentiation are quantified over all linear
  functionals on `W`. Each of them extends to a linear functional on `V`
  (`LinearMap.exists_extend`), to which the hypothesis applies.

## Place actions on an actual realization

Let `S : OperatorRealization F n` with `F` a number field, and let `v` be a real place,
with `K_v = O(n)` (`Matrix.unitaryGroup (Fin n) ℝ`), or a complex place, with `K_v = U(n)`.

Curves in matrix coordinates (section `PlaceCurves`):

- `realPlaceMatrixInsertion v` and `complexPlaceMatrixInsertion v` are the real-linear maps
  from entry arrays `Fin n → Fin n → ℝ` (respectively `ℂ`) to `ArchimedeanMatrix F n` that
  put the array at the place `v` and zero at every other place. `realPlaceMatrixBase v` and
  `complexPlaceMatrixBase v` are the coordinates of the identity with zero at `v`.
- `coordinates_realPlaceCompactInclusion` and `coordinates_complexPlaceCompactInclusion`:
  the archimedean coordinates of the image of `k ∈ K_v` under the Library's place inclusion
  are the inserted entries of `k` plus the base. Both are checked entrywise from the
  Library's coordinate lemmas for the place inclusions.
- `realLieAlgebraToMatrix_realPlaceLieInclusion` and
  `realLieAlgebraToMatrix_complexPlaceLieInclusion`: the matrix coordinates of the image of
  `X` under the Library's place Lie inclusion are the inserted entries of `X`.
- `hasDerivAt_coordinates_realPlaceCompactInclusion` and
  `hasDerivAt_coordinates_complexPlaceCompactInclusion`: let `γ : ℝ → K_v` have entries
  with `HasDerivAt (fun t => γ t i j) (X i j) 0`. Then the archimedean coordinates of the
  included curve have derivative the matrix coordinates of the included `X` at `0`. The
  entry array of `γ` is differentiable (`hasDerivAt_pi` twice). The coordinates are a
  continuous linear map of it plus a constant (the insertion is a linear map on a
  finite-dimensional space).

The analytic `(𝔤, K)` axioms (in the namespace `OperatorRealization`):

- `continuous_dual_of_pointEvaluation`: for a finite-dimensional subspace `W` of `S.Space`
  and a map `g : X → W` all of whose point evaluations `S.pointEvaluation x (g k)` are
  continuous in `k`, every linear functional `μ` on `S.Space` gives a continuous
  `k ↦ μ (g k)`. The point evaluations restricted to `W` span the dual of `W` (Library
  `span_pointEvaluation_eq_top`), and continuity is preserved by sums and scalar multiples.
- `continuous_dual_compactOrbit`: for every `f` and every linear functional `μ`,
  `k ↦ μ (S.compactRepresentation k f)` is continuous on the full archimedean compact group.
  Apply the previous lemma to the orbit span of `f`, which is finite-dimensional (Library
  `compactRepresentation_isFiniteVector`), and to the Library's continuity of point
  evaluations along compact orbits (`continuous_functionRealization_compactOrbit`).
- `continuous_dual_realPlaceCompactRepresentation` and
  `continuous_dual_complexPlaceCompactRepresentation`: the same at one place, by composing
  with the continuous place inclusion.
- `hasDerivAt_dual_realPlaceCompactRepresentation` and
  `hasDerivAt_dual_complexPlaceCompactRepresentation`: for `γ` as above with `γ 0 = 1`, every
  linear functional `μ` and every `f`,
  `t ↦ μ (S.<place>CompactRepresentation v (γ t) f)` has derivative
  `μ (S.<place>LieAction v (1 ⊗ X) f)` at `0`. This is the Library's
  `compactCurve_dual_deriv` applied to the included curve, with the coordinate derivative
  above.
- `realPlaceCompactRepresentation_realPlaceLieAction_tmul` and
  `complexPlaceCompactRepresentation_complexPlaceLieAction_tmul`:
  `R_v(k) (π_v(1 ⊗ X) f) = π_v(1 ⊗ (k X k*)) (R_v(k) f)`. This is the Library's same-place
  covariance at `1 ⊗ X`, whose conjugation is `1 ⊗ (k X k⁻¹)` and `k⁻¹ = k*` by definition.
- `isRealGKModule_realPlace` and `isComplexGKModule_complexPlace`: the place actions of `S`
  at `v` satisfy `Archimedean.IsRealGKModule n` (respectively `IsComplexGKModule n`). The
  four clauses are the Library's finiteness of place vectors and the three preceding
  results.
- `hasRealPlaceGenericComponent_of_component` and
  `hasComplexPlaceGenericComponent_of_component`: if a subspace `W` of `S.Space` is
  irreducible, admissible and generic for the place actions at `v`, in the sense of
  `PlaceComponent`, then `S.HasRealPlaceGenericComponent v` (respectively
  `HasComplexPlaceGenericComponent`). The witness is `W` with the restricted actions and the
  inclusion `W.subtype`, which is injective and intertwines by definition. The four
  properties are the restriction lemmas above, the `(𝔤, K)` axioms coming from
  `isRealGKModule_realPlace`.

## Proof of the bridge

`cuspidalArchimedeanGenericComponentBridge` proves
`CuspidalArchimedeanGenericComponentBridgeStatement`. Given G1, G2, a number field `F` with
compact adele quotient, `r` and an actual cuspidal realization `T`, apply G2 to the cuspidal
operator realization `T.realization` (cuspidal by `T.cuspidal`). At a real place `v`, G1
gives an irreducible admissible subspace `W`. It is nonzero and stable, since it is
irreducible. G2 applied to `W` makes it generic, and
`hasRealPlaceGenericComponent_of_component` concludes. Complex places are handled in the
same way.

## Sources

The `(𝔤, K)`-module notions (submodule, irreducible, admissible) follow Getz–Hahn,
`getz-hahn-2024-automorphic-representations`, Definitions 4.4.4 and 4.4.6, p. 115, and p. 116.
They enter here only through the Library predicates in `GKModule` and
`CuspidalArchimedeanPlaceComponent`, whose Markdown cites the sources. The restriction of a
`(𝔤, K)`-module to a submodule is the standard notion of a submodule in that definition. The
analytic axioms of `IsRealGKModule` and `IsComplexGKModule` are proved from the Library's
results on actual realizations, not cited.
