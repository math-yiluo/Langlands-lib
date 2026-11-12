# Proof of the order on standard parabolics

Authors: Worker 26, with Worker 21 (standard-cocharacter existence composition).

`Langlands.GroupScheme.standardParabolicOrder` proves the exact
`StandardParabolicOrderStatement.{u}` from
[`StandardParabolicOrderStatement`](StandardParabolicOrderStatement.md).
It applies to every field `k : Type u`, connected reductive group scheme `G`
over `Spec k`, maximal split torus inclusion `i : T.toGrp ⟶ G`, and generic
cocharacter `ν`. Write `Δ = simpleRelativeRoots i ν`. For arbitrary
`J, K ⊆ Δ` it proves:

- `J ⊆ K` if and only if `standardParabolic i ν J ≤ standardParabolic i ν K`;
- if `J ⊆ K`, then `standardLevi i ν J ≤ standardLevi i ν K` and
  `standardUnipotent i ν K ≤ standardUnipotent i ν J`;
- the map from the subtype of subsets of `Δ` to `standardParabolic` is
  injective.

All inclusions are of the published `SubgroupFunctor`s, so they hold on every
test scheme over `Spec k`, including nonreduced ones. The theorem keeps the
target's universe and hypotheses. It adds no reducedness, characteristic,
perfectness, splitness or local-field assumption, and `Δ` may be empty.

## Implemented proof

The proof applies the published conditional reduction
`standardParabolic_order_of_root_comparison` from
[`StandardParabolicOrderFromRoots`](StandardParabolicOrderFromRoots.md). Its
conclusion is the target's conclusion for the fixed data. Each of its premises
is discharged by a published proved theorem, with no theorem-valued premise
left:

- Genericity `hν` is the target's own hypothesis.
- Negation stability of the actual relative roots is
  `relativeRootNegation`, from
  [`RelativeRootNegationProof`](RelativeRootNegationProof.md).
- Existence of a standard cocharacter for every `J ⊆ Δ` is the first
  conjunct of `StandardCocharacterStatement.{u}`. The proof obtains that
  statement inside the theorem by composing
  `standardCocharacterStatement_of_reflections_of_signs` from
  [`ReflectionStandardCocharacter`](ReflectionStandardCocharacter.md), its
  reflection premise `relativeRootReflectionExistence_of_rootRankOneFactorization`
  (from [`RootGeneratedCentralizerReduction`](RootGeneratedCentralizerReduction.md))
  applied to `rootRankOneFactorization` (from
  [`RootRankOneFactorizationProof`](RootRankOneFactorizationProof.md)), and
  its sign premise `relativeRootSignsDetermineDynamic` (from
  [`RelativeRootSignsProof`](RelativeRootSignsProof.md)).
- The parabolic comparison and the unipotent comparison by actual root
  signs are the two conjuncts of `relativeRootSignInclusions`, from
  [`RelativeRootSignInclusionsProof`](RelativeRootSignInclusionsProof.md).
  The first says that inclusion of two dynamic parabolics is equivalent to
  containment of the nonnegative regions on the relative roots. The second
  says that containment of the strictly positive regions implies inclusion of
  the dynamic unipotent subgroups.

The affineness instance and the monomorphism of `i` are introduced from
`hG.isAffineHom` and `hi.isSplitSubtorus.mono`, exactly as in the target's
`haveI` bindings.

The mathematical argument is in the reduction's Markdown. Briefly, choose
a standard cocharacter `ζ` for `J`. When `J ⊆ K`, nonnegativity on a relative
root for `ζ` implies nonnegativity for every standard cocharacter `η` for `K`.
The parabolic comparison then puts `P_J ≤ P(ζ)` inside every `P(η)`, hence
inside `P_K`. Conversely, suppose `P_J ≤ P_K` and `α ∈ J`. The root `-α` has
zero pairing with `ζ`. Through the realization of `P(ζ)` inside `P_J`, the
comparison forces `α` to pair nonpositively with a standard cocharacter for
`K`, so `α ∈ K`. Two of these reflections give injectivity. The Levi inclusion
is `standardLevi_mono_of_exists`. The unipotent inclusion uses the reverse
positive-support implication and the unipotent comparison.

## Provenance

This module is an internal derived assembly of published results. The proofs
and mathematical provenance of its inputs (Borel–Tits §5.12–5.14 and §4.2;
see the target's Markdown) are documented in their paired Markdown files.
The same assembly for the order statement appears inside the published
`standardLeviIntersection_of_relativeRootSystem` in
`Langlands/Representation/Jacquet/StandardFixedVectorDetectionAssembly.lean`.
There, standard-cocharacter existence comes from a separate root-system
premise. Here it comes from proved theorems. The composition for
`StandardCocharacterStatement` is the same as in Worker 21's proof candidate
`7527fdc5-e3af-450b-9b75-44133322c56b` for Task 3775. This module does not
import that unpublished candidate; it composes the published theorems
directly.
