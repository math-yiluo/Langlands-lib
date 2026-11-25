# Right derivatives on smooth functions on `GL_n(ℝ)`, translations and `Ad(g)`

Module `Langlands.Representation.Archimedean.RealSmoothRightAction`, namespace
`Langlands.Archimedean.SmoothRightAction`.

Notation: `G = GL_n(ℝ)` (`Langlands.GeneralLinear n ℝ`), `𝔤 = ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`, `U = U(𝔤)`,
`R(X)` the Library right derivative `rightDerivative (matrixModel ℝ n) X`, and `ρ(g) f = f(· g)`
right translation (`Whittaker.rightTranslation`). Smooth means
`ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞`.

## Definitions

* `smoothFunctions n`: the smooth functions `G → ℂ`, as a complex subspace of all functions.
* For a subspace `V` of smooth functions stable under every `R(X)` (hypotheses `hV`, `hVX`):
  `derivative V hV hVX X` is `R(X)` on `V`, `realDerivative` is `X ↦ R(X)` as a real-linear map,
  `linear` is its complex-linear extension `z ⊗ X ↦ z R(X)` to `𝔤`, and `lie V hV hVX` is the same
  map as a Lie algebra map `𝔤 → End(V)`. This is the Library construction `kFiniteLie`
  (module `PrincipalSeriesGKModule`) without the restriction to `K`-finite functions.
* `smoothLie`: `lie` for `V = smoothFunctions n`.
* `conjAlgHom g`: `X ↦ g X g⁻¹` as a real algebra endomorphism of the real `n × n` matrices.
  `adAlg g = id ⊗ conjAlgHom g` is the induced complex algebra endomorphism of `𝔤`, and `adLie g` is
  the same map as a Lie algebra endomorphism. `adU g` is the induced algebra endomorphism of `U`
  (`UniversalEnvelopingAlgebra.lift` of `ι ∘ adLie g`).
* `rightTranslate g`: right translation by `g` as a linear map of `smoothFunctions n`.

## Results

* `mem_smoothFunctions`, `rightDerivative_mem_smoothFunctions`: smooth functions are stable
  under `R(X)`.
* `derivative_apply_coe`, `linear_tmul`, `derivative_commutator`, `lie_tmul`,
  `lie_one_tmul_apply_coe`: `lie V hV hVX (z ⊗ X) = z R(X)`, and `R(X) R(Y) - R(Y) R(X) =
  R(XY - YX)` on `V`.
* `envelopingAction_intertwine_of_tmul`: a linear map `B` from a `𝔤`-module into `V` that
  intertwines the actions of the elements `1 ⊗ X` intertwines the actions of all of `U`.
* `envelopingAction_inclusion_coe`: for `W ≤ V`, both stable under right derivatives, the action
  of `u ∈ U` on `f ∈ W` is the action of `u` on `f` viewed in `V`.
* `realStandardLie_coe`: for the `O(n)`-finite functions of a real standard module, the action
  `envelopingAction (realStandardLie n ds) u h` is, as a function on `G`, the action of `u` on `h`
  through `smoothLie`.
* `rightDerivative_comp_mul_left`: for smooth `f` and `a ∈ G`,
  `R(X)(x ↦ f(a x))(g) = (R(X) f)(a g)`. Right derivatives commute with left translations.
* `conjAlgHom_apply`, `adAlg_tmul`, `adLie_apply`, `adU_ι`: `adU g (ι(z ⊗ X)) = ι(z ⊗ g X g⁻¹)`.
* `envelopingAction_comp_adLie`: `envelopingAction (π ∘ adLie g) u = envelopingAction π (adU g u)`.
* `rightTranslate_apply`; `rightTranslate_envelopingAction` (**equivariance**): on the smooth
  functions, `ρ(g)(u · f) = (adU g u) · (ρ(g) f)`.

## Provenance

Internal infrastructure for the proof of `RealLeftPolynomialGrowthStatement` (module
`RealLeftPolynomialGrowth`). These are standard facts about the right regular action of a Lie
group on smooth functions. Right derivatives form a representation of the Lie algebra, they
commute with left translations, and `ρ(g) R(X) = R(Ad(g) X) ρ(g)`. The module states no result from
the literature.

## Proofs

* `smoothFunctions`: closure under sums is `ContMDiff.add`. Closure under scalars composes with
  the smooth map `z ↦ c z`, as in the Library's `principalSeries`.
* The construction of `lie` and its bracket identity copy `kFiniteLie`. The bracket on pure tensors
  is `LieAlgebra.ExtendScalars.bracket_tmul`, the commutator of right derivatives is the Library
  `rightDerivative_commutator`, and the general case is tensor induction.
* `envelopingAction_intertwine_of_tmul`: apply the Library `envelopingAction_intertwine`. Its
  hypothesis for `Y ∈ 𝔤` follows by tensor induction, using `z ⊗ X = z • (1 ⊗ X)`.
* `envelopingAction_inclusion_coe` and `realStandardLie_coe`: apply the previous result to the
  inclusion map. On `1 ⊗ X` both actions are `R(X)` (`lie_one_tmul_apply_coe`,
  `kFiniteLie_one_tmul_apply_coe`).
* `rightDerivative_comp_mul_left`: by the Library `rightDerivative_eq_fderiv_mul_left`, both sides
  are derivatives at `1` of `y ↦ f̃(g y)` and `y ↦ f̃(a g y)`, where `f̃ = unitsExtension f` extends
  `f` by `0` to all matrices. These two functions of `y` agree. If `g y` is invertible, both are
  `f(a (g y))`. If not, `a g y` is not invertible either, and both are `0`.
* `conjAlgHom` is an algebra map because `g⁻¹ g = 1`. `adLie` preserves brackets because the
  bracket of `𝔤` is the ring commutator (Library `Kostant.realGL_bracket_eq`) and `adAlg g` is
  multiplicative.
* `envelopingAction_comp_adLie`: both sides are algebra maps `U → End` that agree on `ι(𝔤)`
  (`UniversalEnvelopingAlgebra.hom_ext`).
* `rightTranslate_envelopingAction`: rewrite the right side with `envelopingAction_comp_adLie` and
  apply `envelopingAction_intertwine` to `B = ρ(g)`. On a pure tensor `z ⊗ X` the required identity
  `ρ(g)(z R(X) f) = z R(g X g⁻¹)(ρ(g) f)` is the Library `rightTranslation_rightDerivative`, which
  holds for every `g ∈ G`.
