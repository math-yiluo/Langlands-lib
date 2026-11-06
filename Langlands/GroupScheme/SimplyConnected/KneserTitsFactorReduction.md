# Conditional assembly of the local Kneser–Tits factor inclusion

Assembly author: Worker 1331, with the arithmetic interface supplied by
Worker 1756 and the normal-factor interface supplied by Worker 1371.
All imported modules are published Library modules. Dynamic-centralizer
reductivity is imported from its published proof.

This is an internal construction and conditional reduction. It does not prove the task's
unconditional `SimplyConnectedKneserTitsFactorStatement`.

`rationalPoints_range_le_of_localKneserTits` assumes
`LocalKneserTitsStatement` and works over a nonarchimedean local field of
arbitrary characteristic and universe. Its source `A` is affine, simply
connected, almost simple and isotropic. The homomorphism `a : A → G` is
arbitrary. If an abstract normal subgroup `K` of `G(F)` contains the images
of every actual parabolic geometric radical in `A`, then the whole image
of `A(F)` lies in `K`. The proof applies the local arithmetic input to
the inverse image `N` of `K` in `A(F)`. Inverse images preserve normality.
The radical-image premise puts all required generators in `N`, and
`N = ⊤` gives the claimed image inclusion. There is no extra topological
condition on `K`.

`rationalPointsToNormalSubgroupOfLocalKneserTits` constructs the group
homomorphism `A(F) → K` under exactly those same hypotheses. Its underlying
map is the actual rational-point map induced by `a`. The construction uses
`codRestrict`, with the preceding range inclusion supplying the proof that
each image belongs to `K`. Neither injectivity nor normality of `a` is
required.

`simplyConnectedKneserTitsFactor_of_localKT_and_structural_inputs` has the
exact existing factor statement as its conclusion, with these explicit
global premises:

- Local Kneser–Tits for normal generation by actual parabolic radicals.
- Semisimple normal complements over arbitrary fields, with commuting
  multiplication a central isogeny.
- Rational Bruhat decomposition and relative-root rank-one factorization.
- Parabolic-dynamic comparison and smooth maximal-split-torus conjugacy.

The proof derives disjoint positive root rays from rank-one factorization,
chooses an actual generic integral cocharacter, and uses rational Bruhat
decomposition to prove normality of the ambient root-generated subgroup.
Worker 1371's adapter applies the normal-complement premise to the actual
closed normal factor. Almost simplicity gives its smoothness and connectedness.
The central-isogeny multiplication to the simply connected ambient group is an
isomorphism, and the direct-factor theorem then proves that this factor is
simply connected. The parabolic-radical comparison puts the images of all
radicals of the source factor in the root-generated subgroup. It uses the
published `dynamicCentralizerReductive` proof, so centralizer reductivity is
no longer a premise of this assembly. The preceding inverse-image argument
then supplies the desired factor inclusion.

Every premise above remains an obligation of the main task until discharged
by an actual published proof. This module preserves the existing statement
and its imports and makes no claim of unconditional completion.

The provenance is internal: the inverse-image universal property and
codomain restriction are elementary group arguments, and the factor
reduction composes the named Library interfaces. It introduces no new
assertion from original literature and proves none of its six inputs.
