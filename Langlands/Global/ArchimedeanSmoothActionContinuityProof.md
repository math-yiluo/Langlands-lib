# Joint continuity of the actual smooth right action

Author: Worker 348.

The theorem `Langlands.Global.ArchimedeanGL.smoothRightActionContinuity` in
`Langlands.Global.ArchimedeanSmoothActionContinuityProof` proves the exact
published `SmoothRightActionContinuityStatement` for every `K : Type u` with
`[Field K] [NumberField K]` and every natural rank `n`, including zero.
It uses the existing completion-based group and the derivative compact-open
topology on `DerivativeSmoothFunctions K n`. The action is the published
positive right translation `R(g)f(x) = f(x * g)`, transported by
`DerivativeSmoothFunctions.toSmooth` as specified in the statement.

This is an internal derived proof from the published differential covariance,
finite continuous coefficient expansion, and derivative topology. It does not
claim to reproduce a literature proof or specialize an entire reductive-group
theorem. The imported results are `envelopingRightCovariance` from
`ArchimedeanCovarianceProof` and `envelopingConjugationCoefficients` from
`ArchimedeanAdjointCoefficientsProof`. Local compactness of the actual group is
reused from `ArchimedeanConvolution`.

For a fixed enveloping operator `a`, the first private lemma applies covariance
to `Ad(g⁻¹)a` and cancels the mutually inverse conjugations. This gives

```text
D(a) R(g) f = R(g) D(Ad(g⁻¹)a) f.
```

The coefficient theorem supplies a fixed finite family `b_i` and globally
continuous complex coefficient functions `c_i` such that
`Ad(h)a = ∑ i, c_i(h) • b_i` for every group element `h`. The second private
lemma uses linearity of the actual enveloping action and evaluation to expand
that sum. Consequently the derivative coordinate of the translated function,
evaluated at `x`, is

```text
∑ i, c_i(g⁻¹) * (D(b_i)f)(x * g).
```

Each summand is jointly continuous in `(g, f, x)`. Inversion and the coefficient
functions give continuity of its first factor. The published continuous linear
map `DerivativeSmoothFunctions.derivativeCLM K n (b_i)` sends `f` to its
continuous derivative function. Multiplication gives the continuous point
`x * g`, and compact-open evaluation is jointly continuous because the group is
locally compact. The Lean proof combines these maps with `continuous_eval`,
`Continuous.mul`, and `continuous_finsetSum`.

`ContinuousMap.continuous_of_continuous_uncurry` then yields continuity into the
compact-open continuous-function space for each fixed derivative coordinate.
The topology on `DerivativeSmoothFunctions` is induced by the full family of
these coordinates, so `continuous_pi` and `continuous_induced_rng` conclude
joint continuity into that same derivative topology. The canonical equivalence
in the target is handled by the existing coordinate definitions; the proof
assumes no continuity of that equivalence to the original smooth carrier.

All prerequisites are supplied by imported proofs, and the theorem has no
additional hypotheses. The final example checks its complete parameter order
and arbitrary universe. The argument uses no connectedness or positive-rank
assumption. It establishes joint continuity; differentiability of orbit maps,
integration, approximation, reproduction, and automorphic differential growth
remain separate obligations.
