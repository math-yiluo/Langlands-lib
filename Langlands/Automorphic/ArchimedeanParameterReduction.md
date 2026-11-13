# Reduction of the archimedean parameters of cuspidal realizations to local statements

Worker 20 wrote this module for task `a2cfc970-9e20-4d56-b053-8f91a2e0b5cc` (Task 5720). The
task's target is the Library's `Langlands.Global.CuspidalArchimedeanParameterExistenceStatement`
(module `Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction`). It says that every
actual cuspidal realization `T : CuspidalOperatorRealization F r` has, at every real place `v`,
some `ds` with `OperatorRealization.HasRealPlaceParameter T.realization v ds`, and, at every
complex place, some `ds` with `HasComplexPlaceParameter`. This module splits the target into
two local statements (in `Langlands.Representation.Archimedean.GKModule`) and one global
statement, and proves that they imply it. All declarations here are in the namespace
`Langlands.Automorphic`.

## Definitions

Let `S : OperatorRealization F n` and let `v` be a real place.

`OperatorRealization.HasRealPlaceGenericComponent S v` says that there are a type
`V : Type u`, with `F : Type u`, carrying a complex vector space structure, together with
`ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V`,
`π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V` and a linear map
`ι : V →ₗ[ℂ] S.Space`, such that:

1. `ι` is injective;
2. `ι(ρ(k) x) = S.realPlaceCompactRepresentation v k (ι x)` for all `k ∈ O(n)`, `x ∈ V`;
3. `ι(π(X) x) = S.realPlaceLieAction v X (ι x)` for all `X ∈ ℂ ⊗ 𝔤𝔩_n(ℝ)`, `x ∈ V`;
4. `(ρ, π)` is an irreducible admissible generic `(𝔤𝔩_n(ℝ), O(n))`-module:
   `Archimedean.IsRealGKModule n ρ π`, `Archimedean.IsIrreducibleGKModule ρ π`,
   `Archimedean.IsAdmissibleGKModule ρ` and `Archimedean.IsRealGenericGKModule n π`.

In words, `S.Space`, with its `(𝔤_v, K_v)`-module structure from the place actions at `v`,
contains a `(𝔤_v, K_v)`-submodule (the image of `ι`) that is irreducible, admissible and
generic in the algebraic sense of `GKModule`. The submodule is presented as an abstract module
with an injective intertwining map, so no restriction of the place actions to a subspace has
to be constructed. `HasComplexPlaceGenericComponent S v`, for a complex place `v`, is the same
with `U(n)`, `ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ`, the complex place actions,
`IsComplexGKModule` and `IsComplexGenericGKModule`.

Provenance: internal. The two predicates connect the Library's place actions
(`PlaceCompactAction.lean`, `PlaceLieAction.lean`) to the local predicates of `GKModule`.

## Statements

- `CuspidalArchimedeanGenericComponentStatement.{u}`: for every number field
  `F : Type u` with `[CompactSpace (AdeleQuotient F)]`, every `r` and every
  `T : CuspidalOperatorRealization F r`, `T.realization` has a real-place generic component at
  every real place and a complex-place generic component at every complex place. Here the rank
  is `n = r + 1`.
- `CuspidalArchimedeanParameterReductionStatement.{u}`: the three statements
  `Archimedean.RealGenericStandardParameterStatement.{u}`,
  `Archimedean.ComplexGenericStandardParameterStatement.{u}` and
  `CuspidalArchimedeanGenericComponentStatement.{u}` together imply
  `CuspidalArchimedeanParameterExistenceStatement.{u}`.

Provenance of the global statement (derived). An actual cuspidal realization is an irreducible
cuspidal automorphic representation. By the tensor product theorem, its archimedean component
at `v` is an irreducible admissible `(𝔤_v, K_v)`-module (Harish-Chandra admissibility of the
components of automorphic representations). It sits inside the realization as `π_v ⊗ ξ` for a
fixed vector `ξ` of the other components. Cuspidal representations of `GL_{r+1}` are globally
generic through the Whittaker expansion: for a nonzero `φ` in the component, its Whittaker
function `W_φ` is nonzero at some adelic point `g`. Write the `v`-component of `g` as `b k`
with `b` upper triangular and `k ∈ K_v` (Iwasawa decomposition). Then
`λ(φ') = W_{φ'}(b g^v)`, where `g^v` is the component of `g` away from `v`, is a linear
functional on the component that does not vanish at `k φ`. It transforms under `N(F_v)` by the
generic character conjugated by the diagonal part of `b`, which is again a nondegenerate
character. Differentiating this equivariance gives the algebraic genericity of
`IsRealGenericGKModule`, whose character is allowed to be any nondegenerate one for this
reason (Getz–Hahn, `getz-hahn-2024-automorphic-representations`, Definition 11.2.1 and
Example 11.1, pp. 294–295, for global generic characters). This is the expected route of a
proof, not a claim made by the Lean statement. Proving the statement is the global part of the
task.

## Proof of the reduction

`OperatorRealization.hasRealPlaceParameter_of_component` takes an injective `ι : V → S.Space`
that intertwines `(ρ, π)` with the place actions at the real place `v`, together with
`Archimedean.HasRealStandardParameter n ρ π ds`. It proves
`S.HasRealPlaceParameter v ds`. The rank condition is copied. The map is `ι ∘ₗ A`, which is
injective as a composite of injective maps. For `k` and `f`, the membership proof of `R(k)f` is
copied, and `ι(A(R(k)f)) = ι(ρ(k)(A f)) = S.realPlaceCompactRepresentation v k (ι(A f))` is
`congrArg ι` of the clause of `A`, followed by the compatibility of `ι`. The Lie clause is the
same. `hasComplexPlaceParameter_of_component` is the complex analogue.

`cuspidalArchimedeanParameterReduction` proves `CuspidalArchimedeanParameterReductionStatement`.
Given the three statements, `F`, `r` and `T`, fix a real place `v`. The global statement gives
`V, ρ, π, ι` with the four properties. The real local statement, applied with `n = r + 1`,
gives `ds` with `HasRealStandardParameter (r + 1) ρ π ds`, and the lemma above gives
`HasRealPlaceParameter T.realization v ds`. Complex places are treated in the same way.
