# A Casimir element adapted to a maximal compact subgroup of the infinite adelic points

Author: Worker 723.

This module states the existence of Harish-Chandra's Casimir element `ω = ω_𝔭 - ω_𝔨` on the actual
infinite adelic points of a connected reductive group. The element is written in a spanning
family of the tangent Lie algebra adapted to a given maximal compact subgroup. The statement
`AdelicAdaptedCasimirStatement` is a target for a separate proof; nothing is proved here.

## Setting

The statement quantifies over a number field `F : Type u`, an affine group scheme `G` over `F`,
a subgroup `Kinf` of the actual infinite adelic points `InfiniteAdelicGroupPoints F G`, a natural
number `d` and `hsmooth : SmoothOfRelativeDimension d G.X.hom`. It assumes
`GroupScheme.IsConnectedReductive G` and `CompactIwasawa.IsMaximalCompact Kinf`: `Kinf` is
compact, and every compact subgroup containing it equals it, for the original evaluation
topology.

Inside the statement, the local instances are exactly those of the published enveloping action
(`AdelicEnvelopingAlgebra`, module `GroupSchemeAdelicUniformGrowth`):
`InfinitePlaceGroupPoints.completionRCLike`, `smoothChartedSpace F G hsmooth`,
`smoothLieGroup F G hsmooth` and the derived `LieGroup … (minSmoothness ℝ 3)` structure. The
tangent Lie algebra is `GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)`.
The enveloping algebra is `AdelicEnvelopingAlgebra F G hsmooth`, the universal enveloping algebra
of its complexification `ℂ ⊗[ℝ] GroupLieAlgebra …`.

## The statement

There exist `n : ℕ`, `X : Fin n → GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)`
and `J : Finset (Fin n)` such that:

1. the vectors `X i` span the real tangent Lie algebra
   (`Submodule.span ℝ (Set.range X) = ⊤`);
2. for every `j ∈ J` there is a curve `c : ℝ → InfiniteAdelicGroupPoints F G`, smooth for
   `𝓘(ℝ)` and the specified atlas, with `c 0 = 1`, `c t ∈ Kinf` for every real `t`, and velocity
   `mfderiv 𝓘(ℝ) 𝓘(ℝ, smoothModel F d) c 0 1 = X j`;
3. the element

   `∑ i, ι(1 ⊗ X i) ^ 2 - (2 : ℂ) • ∑ j ∈ J, ι(1 ⊗ X j) ^ 2`

   of `AdelicEnvelopingAlgebra F G hsmooth` lies in its centre `Subalgebra.center ℂ _`. Here
   `ι = UniversalEnvelopingAlgebra.ι ℂ` and `1 ⊗ X = (1 : ℂ) ⊗ₜ[ℝ] X`.

Condition 2 makes the `X j` (`j ∈ J`) tangent to `Kinf`. Conditions 1 and 3 together say that
`ω := ∑ i, X i² - 2 ∑_{j ∈ J} X j²` is central, while `ω + 2 ∑_{j ∈ J} X j² = ∑ i, X i²` is a sum of
squares of a spanning family. That sum is the operator whose symbol `∑ i, ξ(X i)²` does not
vanish at nonzero covectors.

## Provenance

The statement is derived from Harish-Chandra, *Two theorems on semi-simple Lie groups*,
Ann. of Math. 83 (1966), §17, proof of Lemma 33 (printed p. 108). There `(X₁, …, X_r)` and
`(Y₁, …, Y_q)` are orthonormal bases of `𝔨` and `𝔭` for a `K`-invariant positive form. With
`ω_𝔨 = ∑ X_i²` and `ω_𝔭 = ∑ Y_j²`, the element `ω = -ω_𝔨 + ω_𝔭` lies in the centre, and
`u = ω + 2ω_𝔨` is elliptic. Taking the family `X` to be the union of the two bases, with `J`
indexing the basis of `𝔨`, gives exactly the element of condition 3.

Harish-Chandra's setting is a connected reductive Lie group with a Cartan decomposition
`𝔤 = 𝔨 ⊕ 𝔭`. For the present group `G(F ⊗ ℝ) = ∏_v G(F_v)` with an arbitrary maximal compact
subgroup `Kinf`, a proof needs:

- a self-adjoint matrix realization adapted to `Kinf`. Mostow, *Self-adjoint groups*, Ann. of
  Math. 62 (1955), gives the existence of a self-adjoint realization (§7) and the conjugacy of
  maximal compact subgroups (Theorem 3.1, printed p. 47). Lemma 2.2 (printed p. 46) gives the
  resulting Cartan decomposition and the trace orthogonality of `𝔨` and `𝔭`;
- the Cartan decomposition of the tangent Lie algebra, with the trace form negative definite on
  `𝔨 = Lie(Kinf)` and positive definite on `𝔭`;
- curves in `Kinf` (for example one-parameter subgroups) realizing the vectors of `𝔨`;
- centrality of the Casimir element of the invariant trace form in the actual enveloping algebra.

The Library has a closed self-adjoint realization of every connected reductive group over a real
or complex field (`connectedReductiveSelfAdjointRealizationStatement`, module
`Langlands.GroupScheme.Reductive.SelfAdjointRealizationProof`) and polar decompositions
(`Langlands.GroupScheme.AffinePolarCompact`). It has neither the conjugacy of maximal compact
subgroups nor the Casimir element of a general reductive group.

## Use

`Langlands.Automorphic.GroupSchemeFunctions.AdelicAutomorphicUniformGrowthReductionStatement`
uses this statement with the interior estimate
`Langlands.Geometry.Manifold.LieGroupEllipticInteriorEstimateStatement`. A `Kinf`-finite and
centre-finite function is annihilated by a monic polynomial in `∑ i, X i²`.
