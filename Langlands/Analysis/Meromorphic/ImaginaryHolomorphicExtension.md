# Holomorphy near the imaginary subspace from an isometry identity

Module `Langlands.Analysis.Meromorphic.ImaginaryHolomorphicExtension` proves,
in one chart `ℂⁿ`, the step of Mœglin–Waldspurger IV.3.12 that passes from
"`M(w, λ)` is unitary at the imaginary points where it is holomorphic" to
"`M(w, λ)` is holomorphic at every imaginary point", for a finite expansion
`∑ i, coeff i s • ψ i` with meromorphic coefficients. Worker 106 wrote it for
Task 5682 (target `Langlands.Global.IntertwiningImaginaryUnitarityStatement`).
It uses the meromorphy predicates `IsMeromorphicOn` and
`IsMeromorphicInCoordinatesOn` of `Langlands.Analysis.Meromorphic.AnalyticSystems`
and `.LinearCoordinates`, and the division lemma of
`Langlands.Analysis.Meromorphic.ImaginaryHyperplaneDivision`. Public
declarations are in the namespace
`Langlands.Analysis.Meromorphic.ImaginaryHyperplane`.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
  series* (1995), registered as `moeglin-waldspurger-1995-spectral-decomposition`,
  IV.3.12, p.161: "If `M(w, .)` was not holomorphic in `λ`, we could find `φ`
  such that `⟨φ, φ⟩ = 1` and a sequence `(λ_n)` of points of `Im X_M^G` such
  that `lim λ_n = λ` and `lim ⟨M(w, λ_n)φ, M(w, λ_n)φ⟩ = ∞`. This would
  contradict the above relation." The "above relation" is the isometry at the
  imaginary points of holomorphy.
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series* (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, pp.328–329: for
  singularities along real hyperplanes, boundedness near the real subspace
  forces holomorphy (the statement's Markdown recalls why boundedness alone
  does not suffice for general meromorphic functions).

The formal argument (provenance: derived) follows MW's: a bound on the
imaginary subspace from the isometry, then holomorphy from the hyperplane
structure of the singularities. It works with coordinates in a basis of the
span of the `ψ i` and with a maximal holomorphic extension, which the sources
leave implicit.

## Main theorem

`exists_holomorphic_on_imaginary_of_isometry`. Data: `ψ : Fin m → Γ → ℂ`
(`Γ : Type`), a matrix `Gm`, coefficients `coeff i : ℂⁿ → ℂ` with
`IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) (coeff i) D` for all `i`, and `K₀ : ℂ`.
With `gramForm Gm x = ∑ i, ∑ i', x i * conj (x i') * Gm i i'`, assume:

- (`hgram`) for all `x`, `0 ≤ gramForm Gm x` in the order of `ℂ`, and
  `gramForm Gm x = 0 ↔ ∑ i, x i • ψ i = 0`;
- (`hiso`) for every family `c` meromorphic on a common domain `D'` with
  `∑ i, c i s * ψ i g = ∑ i, coeff i s * ψ i g` for `s ∈ D ∩ D'` and all `g`,
  `gramForm Gm (c s) = K₀` at every imaginary `s ∈ D'`;
- (`hRH`) for every imaginary `s₀` there are finitely many linear forms
  `ℓ k`, real and not identically zero on `ℝⁿ`, and an open `W ∋ s₀` such that
  for every `g` some `h`, holomorphic on `W`, equals
  `(∏ k, ℓ k (s − s₀)) · ∑ i, coeff i s * ψ i g` for `s ∈ W ∩ D`.

Conclusion: there are `c` and `D'` with `iℝⁿ ⊆ D'`, every `c i` meromorphic
on `D'`, and `∑ i, c i s * ψ i g = ∑ i, coeff i s * ψ i g` for `s ∈ D ∩ D'`.

## Proof

The case `m = 0` is trivial (`D' = ℂⁿ`). Otherwise `D` is open and dense.

1. *Coordinates.* `exists_linearIndependent'` gives a subfamily `ψ ∘ a`,
   `a : κ → Fin m` injective, linearly independent with the same span.
   `exists_eval_leftInverse` (after Worker 979's
   `exists_continuousLinearMap_leftInverse` in the Task 5501 draft) gives
   finitely many points `pts j` and a linear `Λ` recovering the coordinates of
   `∑ k, y k • ψ (a k)` from its values at the `pts j`. The coordinate
   functions `d k s = Λ (j ↦ ∑ i, coeff i s * ψ i (pts j)) k` are linear
   combinations of the `coeff i` with constant coefficients, hence
   meromorphic on `D`, and `∑ i, coeff i s • ψ i = ∑ k, d k s • ψ (a k)` for
   every `s`.
2. *Maximal holomorphic extension.* `extensionDomain f D` is the set of
   points near which `f` agrees on `D` with a holomorphic function, and
   `maximalExtension f D s = limUnder (𝓝[D] s) f`. Then
   (`isMeromorphicOn_maximalExtension`) the extension equals `f` on `D`, agrees
   with every local holomorphic extension, and is meromorphic with domain
   `extensionDomain f D`; local presentations pass from `f` because both sides
   are continuous on the larger domain and agree on its dense subset `D`.
   Let `Ω` be the intersection of the extension domains of the `d k` and
   `c i = ∑_{k, a k = i} maximalExtension (d k) D` (`fiberSum`). The family
   `c` is meromorphic on `Ω` and agrees with `coeff` on `D ∩ Ω`
   (`sum_fiberSum_mul`).
3. *Bound.* By `hiso`, `gramForm Gm (c s) = K₀` at imaginary `s ∈ Ω`. By
   `hgram` and linear independence the form `y ↦ (gramForm Gm (fiberSum a y)).re`
   is positive on the unit sphere of `κ → ℂ`, so by compactness
   (`exists_coercive`) it is at least `ε ‖y‖²`. Hence the extended
   coordinates are bounded by `Cb = √(Re K₀ / ε)` on the imaginary points of
   `Ω`.
4. *Every imaginary point is in `Ω`.* At an imaginary `s₀`, `hRH` gives `ℓ`,
   `W` and holomorphic `h g`. The functions
   `H k = ∑ j, h (pts j) * Λ (e_j) k` are holomorphic on `W` and equal
   `L · d k` on `W ∩ D`, with `L s = ∏ ℓ k (s − s₀)`. So `H k / L` is a local
   holomorphic extension of `d k` on `W ∩ {L ≠ 0}`, which therefore lies in
   `Ω`, and there `‖H k‖ ≤ Cb ‖L‖` at imaginary points. The division lemma
   `exists_differentiableOn_mul_eq_of_norm_le_on_imaginary` gives `c'`,
   holomorphic near `s₀`, with `L c' = H k`. Since `{L ≠ 0}` is dense
   (`dense_setOf_prod_ne_zero`), `c' = d k` on a neighbourhood of `s₀`
   intersected with `D`, so `s₀` is in the extension domain of `d k`.
5. The conclusion holds with `D' = Ω`.

## Other declarations

- `isMeromorphicOn_comp_continuousLinearEquiv`: meromorphy is preserved by
  composition with a continuous linear isomorphism of normed spaces.
- `isMeromorphicInCoordinatesOn_of_chart`: a function meromorphic in one
  chart `e₀ : ℂⁿ ≃ X` is meromorphic in linear coordinates on `X`
  (`φ ∘ e₀.symm` with domain `e₀.symm ⁻¹' D'`).
- `isMeromorphicOn_restrict`: restriction to a smaller open dense domain.
- `gramForm_smul`, `fiberSum_smul`: homogeneity used in `exists_coercive`.
- Private helper lemmas on scalar meromorphic functions (holomorphy as
  complex differentiability, identity theorem, local presentations, sums,
  products, constants, restriction) are copies of lemmas written by Worker 587
  (Task 5502 draft) and reproduced by Worker 86 in the staged cocycle
  reduction of Task 5503; `IsMeromorphicOn.mul_const` is new.

## Scope

The module is about functions of the form `∑ i, coeff i s • ψ i` on `ℂⁿ`; it
does not mention intertwining operators. The isometry identity, the Gram
positivity and the hyperplane factorisation are hypotheses.
