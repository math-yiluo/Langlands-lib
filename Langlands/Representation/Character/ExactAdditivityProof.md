# Additivity of actual distribution characters on short exact sequences

Authors: Worker 34 (Lean proof and first draft) and Worker 969 (Markdown
revision and submission).

The theorem `Langlands.Character.distributionShortExactAdditivity` proves the
published proposition
`Langlands.Character.DistributionShortExactAdditivityStatement.{uG,uA,uB,uC}`
of `Langlands.Representation.Character.ExactK0Targets`. Its type is exactly
that proposition, with the group universe `uG` and the three carrier universes
`uA`, `uB`, `uC` independent. It adds no hypotheses.

## What is proved

For every Hausdorff locally compact totally disconnected topological group `G`
with Borel structure, every regular left Haar measure `μ`, all admissible
smooth complex representations `A`, `B`, `C`, and all intertwiners
`f : A → B`, `g : B → C` with `SmoothRep.IsShortExact f g`,

```
distribution μ B.representation hB =
  distribution μ A.representation hA + distribution μ C.representation hC.
```

`SmoothRep.IsShortExact f g` is the published predicate: `f` is injective, `g`
is surjective and `range f = ker g`. The sequence need not split as
representations, and the carriers may be infinite-dimensional.

## The implemented proof

1. The proof introduces all binders of the proposition and applies
   extensionality of distributions, reducing to one test function
   `φ : SchwartzBruhat G`.
2. A `change` restates both sides by the definition of `Character.distribution`
   (the same definitional identity is recorded as `Character.distribution_apply`):
   each character value is `FiniteRankEnd.trace` of
   `Character.finiteRankIntegratedAction μ _ _ φ`, whose underlying map is the
   integrated action `Hecke.integratedAction`.
3. `FiniteRankEnd.trace_shortExact`, from the supporting module
   `Langlands.LinearAlgebra.FiniteRankTraceExact`, is applied to the
   underlying linear maps `f.toLinearMap`, `g.toLinearMap` and the three
   components `h.1`, `h.2.1`, `h.2.2` of the short-exactness proof. These are
   respectively injectivity, surjectivity and `range = ker`.
4. Its two commuting hypotheses are proved pointwise by
   `Hecke.integratedAction_intertwiner`. For `f`, the identity
   `f (φ · a) = φ · (f a)` is used in reverse. For `g`, the identity
   `g (φ · b) = φ · (g b)` is used directly. Here `φ · v` denotes the integrated
   action. Smoothness of each representation is the first component `hA.1`,
   `hB.1`, `hC.1` of its admissibility proof.

Thus the middle trace equals the sum of the endpoint traces for every test
function, which is the required equality of distributions.

The supporting trace lemma splits only the underlying complex vector spaces.
No equivariant splitting is asserted or needed, so nonsplit representation
sequences are covered. The proof does not use exactness of compact-open fixed
vectors, finite-dimensional carriers or finite representation length.

## Dependencies and unused instances

Declaration-level dependencies: `Character.distribution`,
`Character.finiteRankIntegratedAction`, `FiniteRankEnd.trace`,
`FiniteRankEnd.trace_shortExact`, `Hecke.integratedAction_intertwiner` and
the definition `SmoothRep.IsShortExact`. The module imports
`Langlands.Representation.Character.ExactK0Targets` and
`Langlands.LinearAlgebra.FiniteRankTraceExact`.

The published character construction uses finiteness of `μ` on compact sets and
left invariance, both supplied by `μ.IsHaarMeasure`. The target's `μ.Regular`
instance is introduced but not used.

## Provenance

This is a derived proof. The target's paired Markdown records the original
character convention from Bernstein–Zelevinsky (1976), Section 2.17: the
character is the finite-rank trace of the integrated action. The additivity
argument itself is standard linear algebra, not an attribution of an exact-K₀
construction to that paper. It uses no Langlands classification, finite-family
character independence, geometric lemma, adjointness, cuspidal support or
assertion about reductive groups.
