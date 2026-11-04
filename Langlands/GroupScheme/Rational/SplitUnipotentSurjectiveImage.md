# Split unipotence of smooth affine surjective images

This is an internal deduction from the published schematic-image and
split-series theorems. It works over any field `k : Type u`, at arbitrary
universe `u`, with no characteristic, perfection or infinitude restriction.

Let `U` be a smooth connected affine group scheme over `k`, let `Q` be a
smooth affine group scheme over `k`, and let `q : U → Q` be a homomorphism
whose underlying scheme map is surjective. If `U` is split unipotent in the
existing finite-series convention, then
`IsSplitUnipotent.of_surjective_to_smooth_affine` proves that `Q` is split
unipotent in exactly that convention.

The source's splitness is expressed by `HasSplitSeries n U`: a finite
normal series with actual represented fppf quotients that are
one-dimensional vector groups, terminating in an all-test trivial group.
No additional representation-theoretic `IsUnipotent U` hypothesis is used.
The conclusion uses the same series predicate on `Q`. No connectedness
hypothesis on `Q`, flatness hypothesis on `q`, or surjectivity on rational
points is added.

## The image input

`SplitSemidirect.homImageHypothesis` discharges the explicit
`SplitSemidirect.HomImageHypothesis k` of the published split-series
induction. For a homomorphism from a smooth connected affine source to a
smooth affine target, it applies `HomImage.exists_image`. Smoothness of the
target supplies its local finite-type condition. The result is a smooth
connected affine closed subgroup, a flat surjective quasi-compact
factorization onto it, and the exact factorization equation.
The stronger local finite-presentation conclusion of `exists_image` is
unused by this older input interface.

## The surjective-image proof

The proof specializes
`SplitSemidirect.isSplitUnipotent_of_surjective` with ambient group `Q`,
normal subgroup the trivial group `N`, and second group `U` mapping by `q`.
The published `trivial_isSplitCandidate Q` supplies closedness, smoothness,
connectedness, normality and the empty split series for the trivial
subgroup.

The first factor contributes the identity point on every test. Therefore
the multiplication morphism `(n,u) ↦ j(n) q(u)` is exactly the second
projection followed by `q`. The second projection is a base change of the
identity structure map of `N`, hence is surjective. Its composition with
`q` is surjective. The published split-series induction, with its image
input now discharged, yields a finite split series for `Q`.

## The entry construction

`IsSplitUnipotent.surjectiveImageSeries` returns the subtype

```text
{n : ℕ // HasSplitSeries n Q}.
```

Its value is a chosen length together with the proof of the complete
existing series predicate. This packages the existential series produced
by the preceding theorem; it does not assert a canonical length or
construct a new notion of splitness.

This result handles the smooth affine quotient models used in dimension
induction. It does not prove the broader
`SplitUnipotentFppfQuotientStatement`, whose target assumes only local
finite type and whose map is presented by local point lifting. No new
external structural theorem is assumed or cited here: all image,
normal-series and trivial-subgroup inputs are the imported published
proofs. Maximal-torus conjugacy and the remaining cocycle structural
propositions are not proved by this file.
