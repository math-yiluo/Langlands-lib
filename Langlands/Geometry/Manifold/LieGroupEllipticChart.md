# Left-invariant word derivatives in a Euclidean chart at the identity

Let `H` be a Lie group modelled on a finite-dimensional real normed space `E`, and let
`X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H` be tangent vectors at the identity. This module
expresses the word derivatives `lieWordDerivative X w` in a Euclidean coordinate chart at the
identity. The chart takes values in `F = EuclideanSpace ℝ (Fin (finrank ℝ E))`. Derivatives are
written as ordered coordinate derivatives with smooth coefficients. This is an internal step of
the Lie group interior estimate; it has no literature source.

## Results

- `exists_lieGroupChartFrame X` gives:
  - an open set `S ⊆ F`;
  - a map `ψ : F → H`, `C^∞` on `S`, and a point `x₀ ∈ S` with `ψ x₀ = 1`;
  - vector fields `V i : F → F`, `C^∞` on `S`, with `V i x₀ = toEuclidean (X i)`.

  For every smooth `f : H → ℂ`, every `i` and every `x ∈ S`,
  `groupDirectionalValue (X i) f (ψ x) = fderiv ℝ (f ∘ ψ) x (V i x)`.
  - **Construction.** Let `e = extChartAt 𝓘(ℝ, E) 1` and `L = toEuclidean`. Set
    `S = L.symm ⁻¹' e.target`, `ψ = e.symm ∘ L.symm` and `x₀ = L (e 1)`.
  - The coordinate expression `m (x, z) = L (e (ψ x * e.symm z))` of the group multiplication
    is `C^∞` on an open set containing every `(x, e 1)` with `x ∈ S`, because the group is a Lie
    group. Also `m (x, e 1) = x`.
  - Define `V i x` as the derivative of `m` at `(x, e 1)` in the second variable, applied to
    `X i`. Then `V i` is `C^∞` on `S`. Near `e 1`, `m (x₀, z) = L z`, so `V i x₀ = L (X i)`.
  - **Chain rule.** Near `1`, `h ↦ f (ψ x * h)` equals `a ∘ e`, where `a z = (f ∘ ψ) (m (x, z))`.
    The manifold derivative of `e` at `1` is the identity (`mfderiv_extChartAt_self`). So
    `groupDirectionalValue (X i) f (ψ x)` is the derivative of `a` at `e 1` along `X i`. By the
    chain rule this is `fderiv ℝ (f ∘ ψ) x (V i x)`.
- `lieWordDerivative_ofList_cons` and `lieWordDerivative_ofList_nil`: the word `i :: w` acts by
  `groupDirectionalValue (X i)` after the word `w`, and the empty word acts as the identity.
  This follows from the definition of `lieWordDerivative` through `FreeMonoid.lift`.
- `contMDiff_lieWordDerivative_ofList`: word derivatives of smooth functions are smooth. Proof by
  induction with the Library lemma `contMDiff_groupDirectionalValue`.
- `lieWordDerivative_chart_expansion`: in a chart frame as above, for a smooth `φ`, a word `w` of
  length at most `N` and `x ∈ S`, `lieWordDerivative X w φ (ψ x)` is the sum over `k ≤ N` and
  `W : Fin k → Fin (finrank ℝ E)` of
  `vectorFieldWordCoeff V w k W x * iteratedFDeriv ℝ k (φ ∘ ψ) x (e ∘ W)`.
  - **Proof.** Apply `vectorFieldWord_expansion` to `G w y = lieWordDerivative X w φ (ψ y)`. The
    recursion hypothesis is the chain-rule identity of `exists_lieGroupChartFrame` for the
    smooth function `lieWordDerivative X w φ`.
