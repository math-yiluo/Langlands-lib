# Compact pushforward along a family of nonarchimedean submersions

`Langlands.HarmonicAnalysis.CompactSubmersionPushforwardStatement` is a
proposition over a proper nontrivially normed field `K`, a normed parameter space
`P` over `K`, and finite-dimensional normed spaces `X` and `Y` over `K`. The
metric on `X` is ultrametric. The measurable spaces on `X` and `Y` are Borel,
and `μ` on `X` and `ν` on `Y` are arbitrary additive Haar measures. The four
type universes are independent.

For a continuous `Φ : P × X → Y` and a compactly supported
`f : LocallyConstant X ℝ≥0`, fix `p₀ : P`. At each `x` in `tsupport f`, assume
that `Φ` has a strict Fréchet derivative `D` at `(p₀, x)` and that the
continuous linear map `x' ↦ D (0, x')` is surjective. Here `tsupport` is the
closure of the support, which is already closed by local constancy of `f`.

There exist an open neighbourhood `U` of `p₀` and a single compactly
supported `g : LocallyConstant Y ℝ≥0` such that the following equality holds
for every `p ∈ U`.

```lean
Measure.map (fun x => Φ (p, x)) (μ.withDensity (fun x => f x)) =
  ν.withDensity (fun y => g y)
```

Both witnesses may depend on the input data and the chosen measures.
`withDensity` uses the canonical coercion from `ℝ≥0` to `ℝ≥0∞`.

Harish-Chandra's §2, Theorem 1 supplies submersivity for the regular
conjugation map to the parabolic quotient. In §3, the integral identity for
the map from the group times the parabolic to the group defines a compactly
supported locally constant output for each regular parameter. Lemma 1
then proves local constancy in that parameter by applying pushforward to
the map that also retains the parameter as a coordinate. The Lean
proposition is an internal additive-coordinate formulation of the
pushforward step and its parameter dependence for a fixed nonnegative
source weight. It uses a joint strict derivative on the distinguished
slice and states the conclusion as an equality of Borel measures.
See Harish-Chandra, *A submersion principle and its applications*,
Proc. Indian Acad. Sci. (Math. Sci.) 90 (1981), 95–102, §§2–3,
printed pp. 96–98 (`harish-chandra-1981-submersion-principle`).
