# Compact pushforward along nonarchimedean submersions

`compactSubmersionPushforward` proves the Library's
`CompactSubmersionPushforwardStatement` with its four universe parameters free.
Over a proper nontrivially normed field `K`, take a normed parameter space `P`,
finite-dimensional normed spaces `X` (ultrametric) and `Y` with additive Haar
measures `μ` and `ν`, a continuous `Φ : P × X → Y`, a point `p₀` and a compactly
supported locally constant density `f ≥ 0` on `X`. If at every point `x` of the
support of `f` the map `Φ` has a joint strict derivative at `(p₀, x)` that is onto
in the `X` direction, then on an open neighbourhood `U` of `p₀` the pushforwards
of `f μ` under `Φ(p, ·)` are all equal to `g ν` for one compactly supported
locally constant `g ≥ 0`.

**One ball.** The private lemma `eventually_map_restrict_of_surjective_partial`
treats one point `a` of the support. Write `d` for the surjective source
derivative and choose a continuous linear right inverse `s` of `d`. The strict
derivative makes `Φ` uniformly close to its linearization on a product of
neighbourhoods of `p₀` and `a`. On a small closed ball about `a` the map
\[
T_p(x)=x+s\bigl(\Phi(p,x)-d(x)\bigr)
\]
is the identity plus a perturbation `u_p` with Lipschitz constant below one, and
`d(T_p(x)) = Φ(p, x)`. By `map_closedBall_add_perturbation`, `T_p` sends `μ`
restricted to the ball about `a` to `μ` restricted to the ball of the same radius
about `T_p(a)`. The centre `T_p(a)` depends continuously on `p`, so for `p` near
`p₀` it stays in the ball about `T_{p₀}(a)`, and by the ultrametric property the
image ball does not depend on `p`. Then `map_restrict_closedBall_linear` shows
that `d` sends `μ` restricted to that ball to a constant multiple of `ν`
restricted to its compact open image. So the pushforward of `μ` restricted to the
ball about `a` under `Φ(p, ·)` is the same multiple of `ν` restricted to one
compact open set, for all `p` near `p₀`. The radius is also chosen so that `f` is
constant on the ball.

**The whole support.** The support of `f` is compact and clopen. A finite subcover
by such balls has its maximal balls pairwise disjoint, by the ultrametric
trichotomy of closed balls (`exists_disjoint_ball_subcover`), and they still
cover the support. Write `f` as the sum over these balls of its constant value
times their indicators. The finite intersection of the parameter neighbourhoods
works for every summand. The output densities are constant multiples of
indicators of compact open sets, so their sum `g` is locally constant and
compactly supported, and additivity of `withDensity` and of pushforward gives
the identity for the sum.

This is an additive-coordinate form of the submersion principle and the
locally constant dependence of the pushforward functions on the parameter in
Harish-Chandra, *A submersion principle and its applications*, Proc. Indian
Acad. Sci. (Math. Sci.) 90 (1981), 95–102, §§2–3, printed pp. 96–98 (§3,
Lemma 1; source `harish-chandra-1981-submersion-principle`). Harish-Chandra
defines the pushforward of a test function along a submersion by the integral
identity and proves Lemma 1 from the submersion that keeps the parameter as a
coordinate; the proof here computes the pushforward of a compactly supported
locally constant density directly, ball by ball.
