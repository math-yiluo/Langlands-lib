# A uniform bound for `c_M` of an exponential family near the imaginary axis

Module `Langlands.LinearAlgebra.GMFamilyExponentialBound` bounds the function
`c_M` of the `(G, M)`-family `c_S(λ) = e^{λ(y_S)}` at the spectral parameters
`λ = i(Λ + sμ)` with `Λ`, `μ` real functionals, `Re s = 0` and `|Im s| ≤ 1`,
at the points where all linear factors `Λ(v) + sμ(v)` are nonzero, uniformly
in `Λ`. The points `y_S` are assumed to give a `(G, M)`-family and the
direction `μ` to be nonzero on the simple roots of every chamber. This
replaces, in the proof of
Lapid's Lemma 8, the uniform bound that Lapid obtains from the convex-hull
formula for `c_M`.

## Definitions

For `Λ, μ ∈ StrongDual ℝ a` and `s ∈ ℂ` (the parameter `λ = i(Λ + sμ)`):

- `thetaShift a S Λ μ s = gram(S)⁻¹ ∏_{v ∈ simpleRoots a S} i(Λ(v) + s μ(v))`,
  that is `θ_S(Λ + sμ)` (`thetaShift_ofReal` for real `s`);
- `expShift R a y Λ μ s = ∑_S e^{i(Λ(y_S) + s μ(y_S))} · thetaShift a S Λ μ s⁻¹`,
  the raw sum. Where all linear factors `Λ(v) + sμ(v)` are nonzero it is
  `c_M(Λ + sμ)` of the exponential family; for real `s` it is the Library's
  `cM` at `Λ + sμ` (`expShift_ofReal`). At a point where some factor
  vanishes, the vanishing denominators are inverted to `0`, and the raw sum
  need not agree with the entire extension used in the proof below (it need
  not even be bounded on the walls);
- `expShiftBound R a y μ = ∑_S e^{|μ(y_S)|} · gram(S) · ∏_{v} |μ(v)|⁻¹`,
  where `gram(S)` is the Gram volume of the simple roots of `S`. It is the
  bound of `norm_expShift_le` only under that theorem's hypotheses (family
  property, `μ(v) ≠ 0` on all simple roots): the inverse `|μ(v)|⁻¹` is `0`
  where `μ(v) = 0`, so a chamber having a simple root on which `μ` vanishes
  contributes `0` to the sum.

## Results

- `exists_entire_of_real_poles` (removable singularities): if `g : ℂ → ℂ` is
  holomorphic off a finite set `P` of real points, meromorphic at them, and
  agrees on `ℝ ∖ P` with a continuous function `f`, then `g` agrees off `P`
  with an entire function. At each `p ∈ P` the order of `g` is nonnegative,
  since a pole would make `g(σ) → ∞` as real `σ → p`
  (`tendsto_cobounded_of_meromorphicOrderAt_neg`), while `g(σ) = f(σ) → f(p)`.
- `differentiable_thetaShift`, `thetaShift_ne_zero`, `norm_factor_ge`: the
  denominators are entire, nonzero where all linear factors are nonzero, and on
  the boundary of the rectangle `|Re z| ≤ A`, `|Im z| ≤ 1` with
  `A ≥ 1 + |Λ(v)|/|μ(v)|` each factor satisfies `|Λ(v) + z μ(v)| ≥ |μ(v)|`.
- `norm_expShift_le`: let `y` give a `(G, M)`-family of exponentials and let
  `μ(v) ≠ 0` for all simple roots `v` of all chambers. Then for every `Λ` and
  every `s` with `Re s = 0`, `|Im s| ≤ 1` at which all linear factors are
  nonzero, `‖expShift R a y Λ μ s‖ ≤ expShiftBound R a y μ`.

## Proof of `norm_expShift_le`

Let `P` be the finite set of real points `−Λ(v)/μ(v)`; off `P` all linear
factors are nonzero. As a function of `s`, the raw sum `expShift` is
holomorphic off `P` and meromorphic at the points of `P`. At real `σ ∉ P` it
is `c_M(Λ + σμ)`, which agrees with the smooth extension `smoothExtension`
(Arthur's Lemma 17.1, in the Library module `GMFamilySmoothExtension`) along
the line, a continuous function of `σ`. By `exists_entire_of_real_poles` there
is an entire function `G` with `G = expShift` off `P`. Take
`A ≥ 1 + |Λ(v)|/|μ(v)|` for all `v`; then the boundary of the rectangle
`|Re z| ≤ A`, `|Im z| ≤ 1` avoids `P`, so `G = expShift` there, and
`|e^{i(Λ(y_S) + z μ(y_S))}| = e^{−Im z · μ(y_S)} ≤ e^{|μ(y_S)|}` and
`|thetaShift a S Λ μ z|⁻¹ ≤ gram(S) ∏ |μ(v)|⁻¹` by `norm_factor_ge`, so
`|G| ≤ expShiftBound` on the boundary. The maximum modulus principle
(`Complex.norm_le_of_forall_mem_frontier_norm_le`) extends the bound for `G`
to the closed rectangle. The point `s` lies in the rectangle and, by
hypothesis, not in `P`, so `expShift(s) = G(s)` satisfies the bound.

## Provenance

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), §7, proof of Lemma 8,
pp. 326–327 (`lapid-2011-asymptotic-inner-product-truncated-eisenstein`,
volume PDF SHA-256
`760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`), bounds
`c_M^{Q₁}(T; μ)` by writing it as the Fourier transform of the characteristic
function of a convex hull (Arthur, *An introduction to the trace formula*,
§17, (17.3) and Lemma 17.2, p. 95, in
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`). The
argument here is different: it uses only the smoothness of `c_M` (removable
singularities) and the maximum modulus principle, and gives an explicit bound
depending on `μ` and the points `y_S`.
