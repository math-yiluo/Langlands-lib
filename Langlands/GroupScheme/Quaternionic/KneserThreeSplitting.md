# A quaternion-type algebra split as `L ⊕ jL`, and its base changes as presentations

Module `Langlands.GroupScheme.Quaternionic.KneserThreeSplitting`, namespace
`Langlands.GroupScheme.KneserThree`. This is internal support for the explicit A₃ = D₃
comparison used to prove `KneserThreeSpinSubgroupStatement` (Kneser's argument as summarized in
Tits, Bourbaki 505, 1977, no. 1.1.6). It makes no literature claim beyond the identities proved
here. It gives the coefficient rings to which the matrix algebra of `KneserThreePresentation`
and `KneserThreeCore` is applied.

## The data

`QuatData K D`, for a field `K` and a `K`-algebra `D` (all in one universe), consists of

* scalars `c δ : K` and elements `x j : D` with `x * x = c` (`x_mul_x`), `j * j = δ`
  (`j_mul_j`) and `j * x = -(x * j)` (`j_mul_x`), where scalars mean their images under
  `algebraMap K D`;
* a `K`-basis `basis : Module.Basis (Fin 4) K D` that equals `![1, x, j, j * x]` (`basis_eq`);
* proofs that `X² - c` (`QuadField.poly c`) is irreducible (`irreducible`) and that
  `L = QuadField.field c = K[X]/(X² - c)` is separable over `K` (`separable`). Both are registered
  as instances for `Q : QuatData K D`.

The structure records the data only. It does not require `D` to be a division algebra, and it
does not construct the data from a quaternion algebra.

## The splitting over `K`

* `ι = QuadField.embed x x_mul_x : L →ₐ[K] D` sends the root to `x` (`ι_root`, `ι_linear`).
* `fst snd : D →ₗ[K] L` read off the basis coordinates: `fst d = d₀ + d₁ root` and
  `snd d = d₂ + d₃ root`, where `d = d₀ + d₁ x + d₂ j + d₃ j x`.
* `decompose`: `ι (fst d) + j * ι (snd d) = d`. Conversely `fst_mk` and `snd_mk` say that
  `fst (ι a + j ι a') = a` and `snd (ι a + j ι a') = a'`. The special cases are `fst_ι`, `snd_ι`,
  `fst_j_mul` and `snd_j_mul`.
* `j_mul_ι`: `j * ι a = ι ā * j`, where `ā = SU3Root.conjugation K L a` is the Library's
  conjugation. It holds because `ā` sends the root to its negative and `j x = -x j`.

## Base change to a commutative `K`-algebra `R`

* `tensorInvolution R` is the Library's involution `SU3Root.unitaryTensorInvolution K L R` of
  `L ⊗[K] R`. It acts as `a ⊗ r ↦ ā ⊗ r` (`tensorInvolution_tmul`).
* `ιR R : L ⊗[K] R →ₐ[K] R ⊗[K] D`, `a ⊗ r ↦ r ⊗ ι a` (`ιR_tmul`). It is defined with
  `Algebra.TensorProduct.lift`: the images of `L` and `R` commute because `R` is central in
  `R ⊗[K] D`.
* `jR R = 1 ⊗ j` and `δR R = algebraMap K (L ⊗[K] R) δ`. They satisfy `bar_δR` (`δ` is fixed by
  the involution), `jR_mul` (`jR * ιR a = ιR ā * jR`) and `jR_mul_self` (`jR * jR = ιR δR`).
* `fstR R` and `sndR R : R ⊗[K] D →ₗ[K] L ⊗[K] R` are `fst` and `snd` on the second tensor
  factor, followed by the swap of factors (`fstR_tmul`, `sndR_tmul`). The base-changed identities
  `decomposeR`, `fstR_ιR`, `sndR_ιR`, `fstR_jR_mul` and `sndR_jR_mul` are proved by induction on
  tensors.
* `presentation R : Presentation (L ⊗[K] R) (R ⊗[K] D)` bundles these data: involution
  `tensorInvolution R`, embedding `ιR R`, element `jR R`, scalar `δR R` and coordinates
  `fstR R`, `sndR R`. Its simp lemmas are `presentation_ι`, `presentation_j` and
  `presentation_c`.

## Naturality in `R`

For a `K`-algebra map `φ : R →ₐ[K] R'`, let `mapA φ = id ⊗ φ : L ⊗[K] R → L ⊗[K] R'` and
`mapB φ = φ ⊗ id : R ⊗[K] D → R' ⊗[K] D`. Then

* `mapB_ιR`: `mapB φ (ιR R a) = ιR R' (mapA φ a)`;
* `mapB_jR`: `mapB φ (jR R) = jR R'`;
* `mapA_bar`: `mapA φ` commutes with the two tensor involutions;
* `mapA_δR`: `mapA φ (δR R) = δR R'`.

So the presentations of `R ⊗[K] D` are compatible with every change of coefficients.
