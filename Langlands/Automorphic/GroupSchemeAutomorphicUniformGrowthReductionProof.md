# Uniform growth of adelic automorphic forms from an elliptic estimate and a Casimir element: proof

`Langlands.Automorphic.GroupSchemeFunctions.adelicAutomorphicUniformGrowthReduction` proves the
published implication `AdelicAutomorphicUniformGrowthReductionStatement.{u}`:

`LieGroupEllipticInteriorEstimateStatement.{u, u} → AdelicAdaptedCasimirStatement.{u} →
AdelicAutomorphicUniformGrowthStatement.{u}`.

Neither premise is proved here. Lean reports the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Auxiliary results

### Word operators on a Lie group (`Langlands.Geometry.Manifold`)

- `lieWordDerivative_one`, `lieWordDerivative_of_mul`: the empty word acts as the identity. The
  word `of i * w` acts by `groupDirectionalValue (X i)` after `w`.
- `lieWordDerivative_leftTranslation`, `lieWordAction_leftTranslation`: word derivatives and word
  combinations commute with left translation `φ ↦ (x ↦ φ (a * x))`. The proof is induction on
  the word, using the Library's `groupDirectionalValue_leftTranslation`. No smoothness is needed.
- `lieWordAction_zero`, `lieWordAction_add`, `lieWordAction_single`: `lieWordAction X P φ` is
  additive in `P`, and `lieWordAction X (single w c) φ = c • (word derivative of w applied to φ)`.

### Homogeneous word combinations (`Langlands.Automorphic.UniformGrowthReduction`)

- `IsHomogeneous a s`: every word in the support of `a.coeff` has length `s`. `IsLower a r`:
  every word there has length less than `r`.
- `isHomogeneous_one`, `IsHomogeneous.mul` (via `MonoidAlgebra.support_coeff_mul_subset` and
  `FreeMonoid.length_mul`), `IsHomogeneous.pow`, `IsHomogeneous.smul`, `isLower_sum`,
  `IsHomogeneous.isLower`.

### Three finite-dimensional lemmas (same namespace)

- `mem_of_hasDerivAt`: let `ev : V →ₗ[ℂ] (X → ℂ)` be injective, `W` a finite-dimensional
  subspace and `c : ℝ → V` a curve in `W`. If for every point `p` the function
  `t ↦ ev (c t) p` has derivative `ev u p` at `0`, then `u ∈ W`. Proof: the image of `W` is a
  finite-dimensional, hence closed, subspace of the product space `X → ℂ`
  (`Submodule.closed_of_finiteDimensional`). The difference quotients
  `t⁻¹ • (ev (c t) - ev (c 0))` lie in it and converge pointwise to `ev u`
  (`hasDerivAt_iff_tendsto_slope`, `tendsto_pi_nhds`). Injectivity returns to `V`.
- `restrict_aeval_apply` and `exists_monic_aeval_eq_zero`: a vector in a finite-dimensional
  `T`-stable subspace `U` is killed by the monic polynomial `minpoly ℂ (T.restrict hU)` evaluated
  at `T`.
- `exists_stable_finite`: let `W` be finite-dimensional and let every vector of `W` be finite for
  a monoid action `ρ`. Let `D` be a family of operators that preserve `W` and commute with `ρ`.
  Then some finite-dimensional `U ⊇ W` is stable under `ρ` and under `D`. Here `U` is the sum of
  the `ρ`-orbit spans of a basis of `W`.

### The actual infinite adelic points (`Langlands.Automorphic.GroupSchemeFunctions`)

All with the published local instances (`completionRCLike`, `smoothChartedSpace F G hsmooth`,
`smoothLieGroup F G hsmooth`, and the derived `minSmoothness ℝ 3` Lie group structure).

- `wordHom F G hsmooth X` is the algebra homomorphism
  `MonoidAlgebra ℂ (FreeMonoid (Fin n)) →ₐ[ℂ] AdelicEnvelopingAlgebra F G hsmooth` sending the
  letter `i` to `ι (1 ⊗ X i)` (`MonoidAlgebra.lift` of `FreeMonoid.lift`). `wordHom_of` records
  this.
- `slice_wordHom_single`, `slice_wordHom`: the infinite slice at a finite point `b` of
  `adelicEnvelopingAction (wordHom X P) f` is `lieWordAction X P` applied to the slice of `f`.
  For a word, by induction: `finitePlotSmoothEnvelopingAction_real_generator` identifies
  `ι (1 ⊗ X i)` with `finitePlotSmoothDifferentialAction (X i)`, and
  `finitePlotSmoothSlice_differentialAction` with `plotSmoothDifferential_apply` turn its slice
  into `groupDirectionalValue (X i)`. General `P` follows by `MonoidAlgebra.induction_linear`.
- `wordHom_surjective`: if the `X i` span the real tangent space, `wordHom X` is surjective.
  Every `ι (z ⊗ Y)` is an image, by span induction on `Y`. Every enveloping element is a tensor
  algebra element modulo the defining relation (`RingCon.mkₐ_surjective`), handled by
  `TensorAlgebra.induction`.
- `differentialAction_mem_orbitSpan`: let `X` be the velocity at `0` of a smooth curve `c`
  through `1` in `Kinf`. Then `finitePlotSmoothDifferentialAction X` maps the finite-dimensional
  `Kinf`-orbit span of `f` into itself. Apply `mem_of_hasDerivAt` to `ev g = (p ↦ evaluate g p)`
  (injective by `finitePlotSmoothSlice_injective`) and the curve `t ↦ R(c t) w`. At
  `p = pair a b`, the function `t ↦ w(pair (a · c t) b)` is the composite of the smooth slice
  `h ↦ w(pair (a h) b)` with `c`. Its derivative at `0` is `mvfderiv` of the slice applied to
  `mfderiv c 0 1 = X` (`mvfderiv_comp_apply_of_eq`, `mvfderiv_eq_fderiv`). By
  `evaluate_finitePlotSmoothDifferentialAction` this is the value of the derivative at `p`.

## The elliptic equation and the growth estimate

`exists_elliptic_slice_annihilator` starts with the adapted Casimir and a compact-finite and centre-finite form `f`. It uses the commutator proof supplied for the specified atlas and the original enveloping action.

1. Let `W` be the finite-dimensional compact orbit span. Each compact translate of `f` is centre-finite by `IsAdelicCenterFinite.infiniteRightAction`, so every vector of `W` is centre-finite. The compact derivatives `D_{X j}` preserve `W` and commute with the centre. `exists_stable_finite` then gives a finite-dimensional space `U` containing `W` and stable under the centre and these derivatives.
2. The sum of squares `Ω = ∑ i, ι(1 ⊗ X i)^2` preserves `U` because it is the sum of the central Casimir and twice the compact sum of squares. The restricted endomorphism has a monic annihilating polynomial. Multiplying it by `X` makes its degree positive while preserving annihilation. For the resulting polynomial `p`, `p(Ω) f = 0`.
3. Write `wsq = ∑ i, [i, i]` and `m = p.natDegree`. The top word operator is `wsq ^ m`, and its lower part is `∑_{k < m} p.coeff k • wsq ^ k`. Their sum maps to `p(Ω)` under `wordHom`. The top symbol at a real covector `ξ` is `(∑ i, ξ(X i)^2)^m`, which is nonzero for `ξ ≠ 0` because the `X i` span. The common equation on the slices follows from `slice_wordHom`.

`adelicAutomorphicUniformGrowthReduction` then uses the interior estimate for this word equation. For an enveloping element `a`, choose `Q` with `wordHom X Q = a` and obtain the compact set `V` and constant for `Q`. The moderate-growth hypothesis bounds `‖f(g)‖` by `Cf * adelicHeight(g)^e`. Let `B' ≥ 1` bound `adelicHeight ∘ ofInfinite` on `V`. Writing `g = pair a' b`, the function `φ(y) = f(pair (a' * y) b)` is smooth and satisfies the equation by left translation. The height inequality gives `‖φ(y)‖ ≤ Cf * B'^e * adelicHeight(g)^e` on `V`, and the interior estimate gives the bound on `lieWordAction X Q φ 1`, which is the value of the derivative at `g`. The exponent `e` is independent of `a`, as required by `hasAdelicUniformModerateGrowth_iff`.

## Provenance

The route is Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995), I.2.17
(printed pp. 37–39), together with Harish-Chandra, *Two theorems on semi-simple Lie groups*
(1966), §17, Lemma 33 (printed pp. 108–109): a `K`-finite, centre-finite function is killed by a
monic polynomial in the elliptic element `u = ω + 2ω_𝔨`. The reproducing-kernel step (MW I.2.5
and Harish-Chandra's reproduction lemma) is replaced by the interior estimate. The formal
arguments above are internal.
