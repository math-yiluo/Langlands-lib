# A Fredholm envelope exact at its base point

The derived proposition `Langlands.Analysis.Meromorphic.ExactFiberFredholmCriterionStatement`
is proved by `exactFiberFredholmCriterion`. Let `S` be open in a complex manifold
with finite-dimensional model space, let `B` be a complex Hilbert space and `C`
a complex normed space, and let `A(s) : B →L[ℂ] C` be weakly holomorphic on `S`.
If `s₀ ∈ S` and `D A(s₀) − 1` is compact for a continuous linear `D : C →L[ℂ] B`,
there is an open neighbourhood `U ⊆ S` of `s₀` with a weakly holomorphic family
of injective maps `ℓ(s) : ℂⁿ →L[ℂ] B` whose ranges contain `ker A(s)` for
`s ∈ U`. At `s₀` the range is **equal** to `ker A(s₀)`. Equality at other
parameters is not asserted. No Hilbert or completeness assumption is made on `C`.

## Implemented proof

1. `FredholmCriterion.exists_comp_eq_id_sub_starProjection` starts with
   `G A₀ = 1 − F`, with `F` of finite rank, from
   `RieszFredholm.exists_leftInverse_mod_finiteRank`. On `K = ker A₀`, `F` is
   the identity, so `K` is finite-dimensional and is contained in `W = range F`.
   Let `P` be the orthogonal projection onto `Kᗮ`, and put `Q = W ∩ Kᗮ`.
   The restriction of `A₀` to `Q` is injective, with finite-dimensional range.
   Its inverse on this range is continuous, and the range has a continuous
   projection from `C`. Composing gives a left inverse `J : C →L[ℂ] Q` of
   the restriction. With the inclusion of `Q` understood, set
   `L = P G + J (1 − A₀ G)`. Indeed, `P F x ∈ Q`, `A₀ P F x = A₀ F x`,
   and `(1 − A₀ G) A₀ x = A₀ F x`. Therefore
   `L A₀ x = P G A₀ x + P F x = P x`, so `1 − L A₀` is exactly the
   orthogonal projection onto `K`.
2. `FredholmCriterion.exists_finiteType_euclidean_exact_fiber` works in the
   parameter model space. Put `X(z) = 1 + L (A(z) − A₀)`. This is weakly
   holomorphic, hence norm-continuous by `WeakHolomorphy.continuousAt_of_weak`.
   Since `X(z₀) = 1`, the locus of invertibility is a neighbourhood of `z₀`.
   A basis of `K` gives an injection `ι : ℂⁿ →L[ℂ] B` with range `K`.
   Take `ℓ(z) = X(z)⁻¹ ι`, weakly holomorphic by
   `WeakHolomorphy.differentiableOn_inverse_apply`. When `A(z) x = 0`,
   `X(z) x = (1 − L A₀) x ∈ K`, hence `x ∈ range ℓ(z)`. At `z₀` the
   inverse factor is the identity, proving the asserted equality of ranges.
3. `exactFiberFredholmCriterion` applies this construction on the chart target
   intersected with the inverse-chart preimage of `S`. It pulls the smaller
   neighbourhood and the family back through the chart, using the inverse
   identities for both kernel containment and base-point equality.

## Provenance and use

Joseph Bernstein and Erez Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §3.4, pp.194–195
(Fredholm Lemma and Corollary 3.4), and §7.6, pp.219–220 (application to local
finiteness). The correction of the finite-rank remainder is an internal
refinement of the Fredholm Lemma, not an equality of ranges asserted by that
lemma. It is intended for the analytic end of Theorem 7.2: if a Hilbert system
includes a reproducing equation, a smoothing map that is injective on the
base-point kernel is then injective on the entire base-point witness. This
module does not construct the weighted adelic Hilbert system, the smoothing
map, or the Fréchet-space witnesses.
