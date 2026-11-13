# The fixed-Levi embedding of a Bernstein block from a Levi block projection

Worker 5352. This is a supporting reduction for Task 5352. It is not an unconditional proof of that task's target.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French version of 9 July 2026, source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The relevant passages are:

- VI.7.2, Proposition and proof, printed pp.184–185 / PDF pp.190–191;
- VI.3.3, equation VI.3.3.1, printed p.145 / PDF p.151;
- VI.10.3, Proposition, printed p.209 / PDF p.215;
- VI.4.1, Proposition, printed p.149 / PDF p.155;
- VI.3.2(ii), printed pp.143–144 / PDF pp.149–150.

## What this module does

The published reduction `BernsteinBlockCharacterizationReduction` and `BernsteinSupportJacquetPresentation` derive the VI.7.2 characterization `BernsteinBlockCharacterizationStatement` from two named inputs. This module replaces one of them, the fixed-Levi embedding `BernsteinFixedLeviBlockEmbedding` (condition (i) for block objects), with:

- a Levi-side input `BernsteinLeviBlockProjection`;
- two published but unproved statements, VI.10.3 `BernsteinBlockJacquetFaithfulStatement` and VI.4.1 `RationalSummandSmallProgeneratorStatement`;
- the proved VI.3.2 theorem `rationalNormKernelFiniteRestriction`.

The other input, the geometric exclusion `BernsteinInducedInertiaJacquetExclusion`, is unchanged. Neither `BernsteinLeviBlockProjection` nor `BernsteinInducedInertiaJacquetExclusion` is proved here, and neither is VI.10.3 or VI.4.1.

## Why the route differs from the source

The source proof, on printed p.185, obtains (i) by grouping the components of the I/R embedding `V → ⊕_Q i_Q^G(R_Q)` by conjugacy class. It then states that a factor `⊕_{(Q,D')} i_Q^G(τ_{Q,D'})` "can be rewritten" as `i_P^G(τ)` with `τ ∈ M(M)_D`, because the data `(M,D)` and `(L,D')` are conjugate. That rewriting compares induction from different standard parabolics with conjugate Levis. The current Library has no such comparison. This module therefore proves the fixed-`P` embedding directly. It applies first adjointness to a projection of `r_P^G(V)` onto its `D`-component, and uses VI.10.3 to show that the transposed map is injective.

## Declarations

### `BernsteinLeviBlockProjection` (derived Prop)

For each actual standard cuspidal datum `a` of the family, with standard Levi `M = M_{a.roots}` and `D = [a.representation]`, and for each smooth representation `W` of the literal standard Levi subgroup `levi i ν a.roots` (carrier universe `max uF uV`), it asserts the following. There exist an object `τ` of the full rational inertia block of `a.representation`, on the rational points of `bernsteinLeviScheme i ν a.roots`, and a map `p : W ⟶ bernsteinLiteralLeviRep i ν a.roots τ`. For every object `Y` of that inertia block and every nonzero `f : bernsteinLiteralLeviRep … Y ⟶ W`, the composite `f ≫ p` is nonzero.

Provenance: derived. With the VI.3.3.1 decomposition `W = W_D ⊕ W^D`, take `τ` as the transport of `W_D` and `p` as the projection onto `W_D`. A map out of a block object into `W` lands in `W_D`, because `Hom(M(M)_D, M(M)^D) = 0`, and so it is not killed by the projection. The Prop records exactly the part of VI.3.3.1 that the embedding argument uses. Worker 76 is deriving it from the published `RationalCuspidalInertiaDecompositionStatement` in separate work.

### `BernsteinLeviBlockJacquetDetection` (derived Prop)

For each datum `a` and each object `X` of the saturated Bernstein block `BernsteinSaturatedBlock i ν family (bernsteinInertialClass i ν family a)` with nontrivial carrier, it asserts the following. There exist an object `Y` of the inertia block of `a.representation` and a nonzero map from `bernsteinLiteralLeviRep … Y` to the normalized Jacquet module `(jacquetFunctor (family.decomposition a.roots) (family.closedUnipotent a.roots)).obj X.obj`. Since `jacquetFunctor` is an abbreviation, this Jacquet functor is the normalized Jacquet functor of VI.10.3.

Provenance: derived. It is VI.10.3 (`r_D(X) ≠ 0` for nonzero `X` in the block), stated through a block object mapping nonzero into `r_P^G(X)`.

### `bernsteinFixedLeviBlockEmbedding_of_projection_of_detection`

The hypotheses are `BernsteinLeviBlockProjection i ν family` and `BernsteinLeviBlockJacquetDetection i ν family`. The conclusion is `BernsteinFixedLeviBlockEmbedding i ν family`.

Proof:

1. Let `V` be in the block of `a`. Write `J = jacquetFunctor …` and `Ind = normalizedInductionFunctor …` for the standard parabolic of `a.roots`. The published adjunction `normalizedJacquetInductionAdjunction` gives `J ⊣ Ind`. Its unimodularity hypothesis comes from `standardUnipotent_isUnimodular_of_standardCocharacterStatement`.
2. Apply the projection hypothesis to `W = J(V)`. This gives `τ` in the inertia block and `p : J(V) ⟶ literal τ`. Let `φ : V ⟶ Ind(literal τ)` be the adjunction transpose of `p`.
3. Injectivity of `φ`. Suppose `φ x = 0` with `x ≠ 0`. Let `K = SmoothRep.kernel φ` with inclusion `incl = SmoothRep.kernelι φ`. Then `K` is nontrivial and `incl ≫ φ = 0`.
   - By naturality of the adjunction (`homEquiv_naturality_left_symm`) and `homEquiv_counit`, we get `J.map incl ≫ p = 0`.
   - `K` is a subrepresentation of `V`, so by `smoothSubquotientTransitivity` every irreducible subquotient of `K` is one of `V`. Hence `K` lies in the block.
   - Detection gives `Y` in the inertia block and `f ≠ 0` into `J(K)`.
   - The standard unipotent radical is a limit of compact subgroups (`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`). So `J.map incl` is injective by `normalizedJacquetFunctor_map_injective`, hence a monomorphism, and `f ≫ J.map incl ≠ 0`.
   - The projection property then gives `(f ≫ J.map incl) ≫ p ≠ 0`. But this composite is `f ≫ 0 = 0`, a contradiction.
4. Take the index type `PUnit` with the single summand `τ`, and the decidable equality `Classical.decEq` used by `BernsteinInertiaInducedEmbedding`. The map `φ ≫ directSumι _ PUnit.unit` is a monomorphism. The direct-sum inclusion is split by `directSumπ` (`directSumι_comp_π_self`). So the map is injective, which gives the required embedding into `bernsteinInertiaInducedSum`.

The `PUnit` index means a single object of `M(M)_D` already suffices for condition (i). This is consistent with the source, which allows sums.

### `bernsteinLeviBlockJacquetDetection_of_faithful`

The hypotheses are `BernsteinBlockJacquetFaithfulStatement.{uF, uV}` (VI.10.3) and `RationalSummandSmallProgeneratorStatement.{uF, max uF uV}` (VI.4.1). The conclusion is `BernsteinLeviBlockJacquetDetection i ν family`.

Proof:

1. Let `L = bernsteinLeviScheme i ν a.roots`, with the published intrinsic standard family `bernsteinLeviStandardFamily i ν family a.roots`, its torus `bernsteinLeviTorus`, and `T2Space` from `rationalPoint_t2Space`.
2. The proved VI.3.2 `rationalNormKernelFiniteRestriction`, through `rationalNormKernelConstituent_of_finiteRestriction`, gives an irreducible subrepresentation `W` of the restriction of `a.representation` to the common norm kernel `⁰M`. Let `ρ₀` be the actual subrepresentation and `j` its injective inclusion.
3. VI.10.3 applied to `a`, `ρ₀`, `j` and `X` gives a nonzero map from the literal transport of `Π_D = rationalNormKernelSummandInduction L ρ₀` into `r_P^G(X)`.
4. Membership of `Π_D` in the inertia block of `a.representation`:
   - `a.cuspidal` is transported to cuspidality of `a.representation` for `L`'s own standard data. This uses `rationalLeviCuspidalityTransport` and `SmoothRep.pullbackSymmIso`.
   - The first component of VI.4.1, applied at carrier universe `max uF uV`, puts `Π_D` in the inertia block of the universe lift `rationalInertiaBaseLift L a.representation`.
   - The universe-lift isomorphism `SmoothRep.mkIso (SmoothRep.universeLiftEquiv _)` relates that lift to `a.representation`, so `rationalInertiaBlockProperty_iff_of_related` transfers membership.

Only the membership half of VI.4.1 is used.

### `bernsteinFixedLeviBlockEmbedding_of_projection`

This is the composite of the two theorems above. From `BernsteinLeviBlockProjection i ν family`, VI.10.3 and VI.4.1 it gives `BernsteinFixedLeviBlockEmbedding i ν family`.

### `BernsteinBlockCharacterizationLeviInputs` (derived Prop) and `bernsteinBlockCharacterization_of_leviInputs`

`BernsteinBlockCharacterizationLeviInputs.{uF, uV}` states, for every field, group, torus, cocharacter and family in the unchanged setting of `BernsteinBlockCharacterizationStatement`, the conjunction `BernsteinLeviBlockProjection i ν family ∧ BernsteinInducedInertiaJacquetExclusion i ν family`. It uses the same binders and local instances as the published `BernsteinBlockCharacterizationPrerequisites`. It is a target, not an axiom.

`bernsteinBlockCharacterization_of_leviInputs` has conclusion exactly `BernsteinBlockCharacterizationStatement.{uF, uV}`. Its three hypotheses are this inputs Prop, VI.10.3 and VI.4.1, and none of them is discharged. For each family it combines the fixed-Levi embedding above with the published `bernsteinBlockCharacterization_of_embedding_and_exclusion`. Compared with the published `bernsteinBlockCharacterization_of_prerequisites`, the inputs are now VI.3.3.1-type projection, geometric exclusion, VI.10.3 and VI.4.1. They are no longer the fixed-Levi embedding and the two support targets.

## Remaining inputs

- `BernsteinLeviBlockProjection`: derived from VI.3.3.1 (`RationalCuspidalInertiaDecompositionStatement`), in separate work by Worker 76.
- `BernsteinInducedInertiaJacquetExclusion`: Task 5313.
- `BernsteinBlockJacquetFaithfulStatement` (VI.10.3) and `RationalSummandSmallProgeneratorStatement` (VI.4.1): published statements that are not yet proved.

## Local instances

The module-local instances, which are affine, closed-immersion, finite-type, point-topology, local-compactness and non-archimedean instances for `G` and the standard Levis, copy those of `BernsteinBlockCharacterizationReduction` and `BernsteinLeviInertiaCofan`. Each has an explicit module-specific name, prefixed `instFixedLeviEmbedding`. No statement or import file of the target is modified, no missing statement is assumed as an instance, and no axiom is introduced.
