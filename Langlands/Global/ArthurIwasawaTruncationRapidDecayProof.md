# Arthur's restricted rapid decay for every compact Iwasawa subgroup

`iwasawaTruncationRapidDecay` proves `IwasawaTruncationRapidDecayStatement`
for every compact subgroup `K` with `P₀(𝔸)K = G(𝔸)`, given reflection data
and bijective restriction of real character parameters from the minimal
parabolic to the maximal split torus. The statement takes a closed matrix
representation of positive size and a smooth structure. It gives a
regularity threshold `c` such that, when `β(T) > c` for every simple
root `β`, the truncation `Λᵀ f` decays by every inverse power of the
adelic source norm on the ambient norm-one part of each Siegel set
of `K`. The input `f` is a finite plot-smooth left `G(F)`-invariant
function on the full adelic group, with one moderate growth exponent
for all its enveloping-algebra derivatives.

`iwasawaSiegelCovering` supplies covering data for the given `K`.
`arthurTruncationSigmaExpansion` uses those data and
`iwasawaSiegelReduction` to choose the regularity threshold before
the truncation parameter, input function and testing Siegel set.
The proof inserts the relative partition (8.1) in the truncation sum
and expands the chamber product using (8.2). This gives the regrouping
displayed before (13.7) in Arthur 2005, a finite sum over pairs of
nested parabolics of sums over rational cosets. The cutoff has finite
support on each coset space for a given evaluation point.

`exists_sigmaCoset_representatives_with_bound` chooses a rational
representative in each supported coset whose translate of the
evaluation point lies in the truncated lower Siegel set. The sigma
factor and the alternating constant term are invariant under this
change of representative. At that translate, vanishing of the maximal
constant terms at the active roots and invariance under the outer
radical give an inverse root scale per derivative order by repeated
oscillation in the upper Levi. The truncated sigma geometry controls
the adelic height using the maximum of zero and the active root
logarithms. This yields an arbitrary inverse height power for each
supported summand.

Distinct cosets give distinct chosen rational representatives.
With normalized height \(H\), norm minimality on the testing Siegel
set gives \(H(x)\le C H(\gamma x)\). Submultiplicativity and inversion
invariance give \(H(\gamma)\le H(\gamma x)H(x)\). If \(d\) is a
summable inverse-power exponent for the rational heights, the
termwise estimate of order \(2d+n\) therefore bounds the summands
weighted by \(H(x)^n\) by a fixed multiple of \(H(\gamma)^{-d}\).
The proof adds the resulting coset bounds over the finite set of
parabolic pairs and uses \(H\) to dominate the adelic source norm.

Sources are Arthur 1978, §6, Lemma 6.4, Arthur 1980, Lemma 1.4, and Arthur
2005, §8 and §13, especially pp. 70–72 and equation (13.7).
