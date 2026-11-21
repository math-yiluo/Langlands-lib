# Assembling an adapted Casimir element from matrix data

Module `Langlands.Geometry.Manifold.AdaptedCasimirAssembly` (namespace
`Langlands.Geometry.Manifold.AdaptedCasimirAssembly`). Internal supporting result: it derives the
conclusion of Harish-Chandra's adapted Casimir element (*Two theorems on semi-simple Lie groups*,
1966, proof of Lemma 33: `ω = ω_𝔭 - ω_𝔨` for a Cartan decomposition and an invariant form
positive on `𝔭` and negative on `𝔨`) for an abstract Lie group from explicit matrix data. The
invariant form is a real trace form of matrix representations, not the Killing form.

## Setting

`E` is a finite-dimensional real normed space (complete), `G` a group with a `C^∞` Lie group
structure modelled on `𝓘(ℝ, E)`. For a finite index type `ι`, each `v : ι` carries an `RCLike`
field `𝕜' v`, a finite index type `N' v`, and a monoid homomorphism
`φ v : G →* Matrix (N' v) (N' v) (𝕜' v)` with `C^∞` entries. `D v` denotes
`MatrixCoefficientLie.matrixDifferential 𝓘(ℝ, E) (φ v)`, the entrywise differential at `1`.

## Declarations

- `hasMFDerivAt_finset_sum`: a finite sum of functions with manifold derivatives has the sum
  derivative (induction on the finset, `HasMFDerivAt.add`, `hasMFDerivAt_const`).
- `mvfderiv_comp_theta`: for smooth `θ : G → G` with `θ 1 = 1`, the entry derivative of
  `g ↦ φ (θ g)` at `1` is `D (dθ X)`, where `dθ = mfderiv θ 1` (chain rule).
- `matrixDifferential_theta`: if moreover `φ (θ g) * (φ g)ᴴ = 1` for all `g`, then
  `D (dθ X) = -(D X)ᴴ`. *Proof.* Entry `(a, b)` of `φ (θ g) * (φ g)ᴴ` is
  `∑ c, φ (θ g) a c * star (φ g b c)`, a constant function. Its derivative at `1`, by the
  product rule `HasMFDerivAt.mul` and the sum rule, is
  `∑ c, (1 a c * star (D X b c) + 1 b c * D (dθ X) a c) = star (D X b a) + D (dθ X) a b`
  (the derivative of `star ∘ φ_{bc}` is computed with `RCLike.conjCLE` and
  `MatrixCoefficientLie.mvfderiv_clm_comp`). It vanishes by uniqueness of derivatives.
- `re_trace_mul_conjTranspose`: `re (trace (A * Aᴴ)) = ∑ a, ∑ b, ‖A a b‖ ^ 2`; and
  `re_trace_mul_conjTranspose_pos`: this is positive when `A ≠ 0`.
- `traceForm φ`: the real bilinear form `B X Y = ∑ v, re (trace (D v X * D v Y))` on
  `GroupLieAlgebra 𝓘(ℝ, E) G`, with `traceForm_apply`.
- `exists_adapted_casimir` (main result). Assume in addition a `C^∞` map `θ : G → G` with
  `θ (θ g) = g`, `θ 1 = 1` and `φ v (θ g) * (φ v g)ᴴ = 1` for all `v, g`; joint injectivity: if
  `D v X = 0` for every `v` then `X = 0`; and a set `K ⊆ G` containing every fixed point of `θ`.
  Then, with the Lie algebra structure on `GroupLieAlgebra` given by
  `LieGroup.of_le (n := ∞)` exactly as in the adapted Casimir statement, there are `n`,
  `X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) G` and `J : Finset (Fin n)` such that the `X i` span, each
  `X j` with `j ∈ J` is `mfderiv 𝓘(ℝ) 𝓘(ℝ, E) c 0 1` for a `C^∞` curve `c : ℝ → G` with `c 0 = 1`
  and values in `K`, and `∑ i, ι(1 ⊗ X i)^2 - 2 • ∑ j ∈ J, ι(1 ⊗ X j)^2` lies in the centre of
  `UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, E) G)`.

## Proof of `exists_adapted_casimir`

1. `dθ (dθ X) = X`: by `matrixDifferential_theta` twice, `D v (dθ (dθ X)) = D v X` for all `v`;
   joint injectivity applied to the difference gives the claim. Put `s = -dθ`, so `s (s X) = X`
   and `D v (s X) = (D v X)ᴴ`.
2. `B` is symmetric (`Matrix.trace_mul_comm`) and invariant:
   `MatrixCoefficientLie.matrixDifferential_lie` turns brackets into commutators, and
   `trace (A (B C - C B)) = trace ((A B - B A) C)` by associativity and cyclicity of the trace.
3. `B (s X) (s Y) = B X Y`: `re trace (Aᴴ Bᴴ) = re star (trace (B A)) = re trace (A B)`.
4. `0 < B X (s X)` for `X ≠ 0`: `B X (s X) = ∑ v, re trace (D v X (D v X)ᴴ)`, a sum of nonnegative
   terms, one of which is positive because some `D v X ≠ 0` by joint injectivity.
5. `Langlands.Algebra.SignedCartanCasimir.exists_signed_casimir` gives `n`, `X`, `J` with the
   spanning and centrality conclusions and `s (X j) = -X j`, i.e. `dθ (X j) = X j`, for
   `j ∈ J`.
6. For `j ∈ J`, `Langlands.Geometry.Manifold.InvolutionFixedCurve.exists_contMDiff_curve_fixed`
   applied to `θ` at the fixed point `1` gives a `C^∞` curve of fixed points of `θ` through `1`
   with velocity `X j`; its values lie in `K` by hypothesis.
