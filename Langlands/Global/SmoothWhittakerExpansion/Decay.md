# Band bounds for smooth cuspidal functions on `GL_n`

Module `Langlands.Global.SmoothWhittakerExpansion.Decay`, namespace
`Langlands.Global.SmoothWhittakerExpansion`. This helper module belongs to the proof of
`Langlands.Global.WhittakerExpansionStatement` (Getz–Hahn, Theorem 11.3.6). It is internal to
that proof and has no separate literature statement.

## Setting

`F` is a number field and `n` a natural number. `f : FiniteSmoothRationalFunctions F n` is a
Library finite-smooth function on `GL_n(F) \ GL_n(𝔸)`. It is left invariant under the rational
points, right invariant under an open subgroup of `GL_n(𝔸_f)`, and smooth in the archimedean
variable. `finiteSmoothEnvelopingAction F n u f` is the Library action of an element `u` of the
archimedean enveloping algebra `ArchimedeanGL.EnvelopingAlgebra F n`. `evaluate F n` reads a
function as a function on `AdelicGL F n = GL_n(𝔸)`. `torInf F n x` is the archimedean torus
element `diag(e^{x_1}, …, e^{x_n})`, inserted equally at every infinite place.
`absDet F n g` is the adelic absolute value of `det g`.

The file sets `backward.isDefEq.respectTransparency false` and declares local `AddCommGroup`
instances (`Submodule.addCommGroup`) on the Library function spaces. These are elaboration
settings and change no statement.

## Results

* `exists_common_level f`: one open subgroup `L` of `GL_n(𝔸_f)` fixes every enveloping
  derivative `u · f` under right translation. Proof: `L` is the level of `f`, and the Library
  lemma `finiteSmoothEnvelopingAction_preserves_level` shows that the action of `u` preserves
  this level.
* `slice_data f u y`: the archimedean slice `g ↦ (u · f)(g · y)` at a finite point `y` is a
  smooth function on `GL_n(F_∞)`. Its left-invariant derivative along the `k`-th Lie basis
  direction is the slice of `(X_k u) · f`, where `X_k` is
  `OperatorRealization.basisGenerator F n k`. Proof: the Library slice lemmas
  `finiteSmoothSlice_apply` and `finiteSmoothSlice_envelopingAction`, the generator identity
  `ArchimedeanGL.envelopingAction_real_generator`, and multiplicativity of the action.
* `norm_le_of_constantTerm_eq_zero`: let `f` have vanishing constant term
  `constantTerm F n h f g` along the block `(a, b)` at `g`. If every translate of `g` by the
  block unipotent `blockUnipotent h Y` changes the value of `f` by at most `M`, then
  `‖f(g)‖ ≤ M`. Proof: the vanishing constant term writes `f(g)` as the integral of
  `f(g) - f(n g)` over the compact block quotient, whose Haar measure `matrixQuotientHaar`
  has total mass one.

The remaining results assume `[CompactSpace (AdeleQuotient F)]`. Their two common hypotheses
are:

* `hcusp`: every derivative `u · f` is cuspidal (`IsCuspidal`);
* `hgrowth`: for one rate `c`, every derivative `u · f` and every compact `Q ⊆ GL_n(𝔸)` admit a
  constant `C` with `‖(u · f)(torInf x · q)‖ ≤ C · exp (c ∑ |x_i|)` for all `x` and `q ∈ Q`.

* `exists_blockDecay`: let `(a, b)` be a maximal block with `a, b > 0`, `N` a natural number
  and `Q` compact. Then for some `C`, on the region where every across-the-block gap
  `x_r - x_p` is at most `-ℓ ≤ 0`, `‖(u · f)(torInf x · q)‖ ≤ C · exp (-N ℓ) · exp (c ∑ |x_i|)`.
  Proof: the Library's abstract rapid-decay theorem `blockDecay_of_cuspidal` (module
  `CuspidalL2.Decay`). It applies to the family `u ↦ u · f`, which is closed under the basis
  derivatives `u ↦ X_k u`. The inputs are rational invariance (`evaluate_rational`), the
  common level, the slice data, the mean-value form of cuspidality, and the weight
  `x ↦ exp (c ∑ |x_i|)` in place of a power of the height.
* `exists_chamber_bound`: let `x` lie in a Siegel chamber `Chamber K x` with
  `|∑ x_i| ≤ R`. Then every `u · f` is bounded on `torInf x · Q`. Proof: the Library's
  `chamber_alternative` gives two cases. In the first, `∑ |x_i|` is bounded and `hgrowth`
  bounds the value. In the second, some block gap is at most `-ℓ`, while `∑ |x_i|` grows at
  most linearly in `ℓ`. Then `exists_blockDecay` with `N = ⌈n³ c⌉` absorbs the growth factor.
* `exists_band_bound` (main result): for `0 < lo`, every derivative `u · f` is bounded on the
  determinant band `lo ≤ absDet g ≤ hi`. Proof: the Library's Siegel decomposition
  `exists_siegelDecomposition` writes `g = γ · torInf y · q` with `γ` rational, `y` in a
  chamber and `q` in a fixed compact set. Then `abs_sum_le_of_absDet` bounds `|∑ y_i|` by the
  band and by `log |det|` on that compact set. Rational invariance removes `γ`, and
  `exists_chamber_bound` concludes.

The argument is the Library's rapid-decay and Siegel-cover argument for operator realizations
(modules `CuspidalL2.Decay` and `CuspidalL2.SiegelCover`). Here it is applied to the cyclic
family of enveloping derivatives of one smooth function, with an exponential weight. It is the
standard rapid decay of smooth cusp forms of moderate growth on Siegel sets, in the weak form
of boundedness on determinant bands. That boundedness is what the Library's Whittaker expansion
core needs.
