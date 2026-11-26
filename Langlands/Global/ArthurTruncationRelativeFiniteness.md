# Relative finiteness and rational height invariance for Arthur truncation

For a standard parabolic `P`, `height_sub_mem_parabolicCorootSpan` uses the character
description of its real parameter space. The minimal height restricted to characters of `P`
is its Iwasawa height. The product formula makes that restriction invariant under `P(F)`.
The restricted characters of the standard Levi span the annihilator of the selected simple
coroots, and their pullbacks along the dynamic limit retraction are characters of `P`. Double
annihilation thus puts the minimal height difference in the span of those coroots. Projecting
to the level of the lower parabolic kills this difference. The weight forms indexed outside
the lower parabolic also kill it. These facts give `tau_rationalParabolic_mul` and
`tauHat_rationalParabolic_mul`. [Parabolic character spaces](ArthurParabolicSpaces.md)

`relative_tauHat_finite` reduces the finite-support question for `Q(F) \ P(F)` to
`truncationFiniteness` for `Q(F) \ G(F)`. With `x` fixed, let `z` be the projection of `H₀(x) - T`
to the common root kernel of `P`. For every `γ ∈ P(F)` the vector
`H₀(γx) - T - z` is in the coroot span of `P`. Its full weights indexed by roots of `P` agree
with the relative weights there, and the other full weights are zero. Adding the sum `w` of
all simple coroots adds one to every full weight. Thus a nonzero relative hatted cutoff gives a
nonzero full hatted cutoff at the fixed parameter `T + z - w`. The inclusion of relative cosets
is injective, and both cutoffs respect the corresponding lower parabolic on the left.
[Full finiteness](ArthurTruncationFinitenessProof.md)

`relative_tau_finite` then follows from chamber containment. The relative finiteness arguments
apply at every parameter and require only the Iwasawa hypothesis of the full finiteness
result. [Chamber containment](ArthurTruncationChambers.md)

## Sources

- J. Arthur, *An introduction to the trace formula* (2005), §§4–5 for the heights, characters and
  weights, and §13, (13.10), printed pp. 73–74, PDF pp. 85–86 for the relative sum. Literature ID
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
  `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.
- J. Arthur, *A trace formula for reductive groups I* (1978), §5 Lemma 5.1, printed p. 936,
  for the full finiteness input of the shifted-parameter argument. Literature ID
  `arthur-1978-trace-formula-reductive-groups-I`, SHA-256
  `80ec482ea894e3af960e79cc1316ac2c2e806ad466f92c106650a59a0b2f17cc`.
