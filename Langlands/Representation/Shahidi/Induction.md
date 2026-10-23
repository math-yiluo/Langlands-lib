# Shahidi's two-block induced representations `I(s, π₁ ⊗ π₂)` and `I(-s, π₂ ⊗ π₁)`

This construction unit defines the induced representations of Shahidi,
*Fourier transforms of intertwining operators and Plancherel measures for
GL(n)*, Amer. J. Math. 106 (1984). The registered source is
`shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
The relevant passages are on printed pages 67 (the display defining `I(s, π)`),
70–71 (§0: the field `F`, `|ϖ| = q⁻¹`, the parabolic `P` with Levi
`G_m × G_n` and upper radical `U`), 72 (the same display, the Weyl element
`w_{m,n}`, the operator `A(s, π, w_{m,n})` of (0.1), and `I(-s, π')` with
`π' = π₂ ⊗ π₁` in (0.3)) and 84 (Lemma 2.2). Pages 73 and 85–87 continue the
intertwining and Whittaker-functional computations; nothing on them is
formalized here.

The source does not repeat the defining display for `I(-s, π')`. This unit
reads it as the same construction for the ordered pair `(n, m)` and parameter
`-s`, the reading under which `A(s, π, w_{m,n})` of (0.1) maps `I(s, π)` to
`I(-s, π')`.

For positive ranks `m, n`, a complex number `s`, and representations `π₁` of
`GL_m(F)` and `π₂` of `GL_n(F)`, the unit builds

- `I(s, π₁ ⊗ π₂)`: the Library's normalized induction, from the standard upper
  parabolic of `GL_(m+n)(F)` with Levi `GL_m × GL_n`, of the block tensor
  `π₁ |det|^(s/2) ⊗ π₂ |det|^(-s/2)`;
- `I(-s, π₂ ⊗ π₁)`: the Library's normalized induction, on the same group
  `GL_(m+n)(F)`, from the standard upper parabolic with Levi `GL_n × GL_m`, of
  `π₂ |det|^(-s/2) ⊗ π₁ |det|^(s/2)`.

Both are given for an explicit general field layer and for the Library's
`PadicField` realizations. The exponent `s` is an arbitrary complex number.
`π₁` and `π₂` are arbitrary `ℂ`-linear representations on arbitrary complex
vector spaces. They need not be smooth, admissible, irreducible,
finite-dimensional or normed.

## Use of the published normalized induction

The unit introduces no induction of its own and no induction predicate. With
`B` a block shape, `χ` a smooth Levi character and `σ i` the block
representations, the Library defines

- `B.productInducedOf χ σ = B.normalizedInducedOf χ (B.blockTensor σ)`
  (`Langlands.Representation.Induction.BlockFactors`);
- `B.normalizedInducedOf χ σ`: smooth induction by right translation of
  `χ ⊗ σ`, inflated through the actual Levi projection of `B.parabolic F`
  (`Langlands.Representation.Induction.Parabolic`);
- for a p-adic realization `T`,
  `T.normalizedProductInduced B σ = T.normalizedParabolicInduced B (B.blockTensor σ)`,
  where `T.normalizedParabolicInduced B σ` is `B.normalizedInducedOf
  (T.leviHalfCharacter B) σ` and `T.leviHalfCharacter B` is the positive square
  root of the Library's explicit block modulus `T.leviModulus B`.

`Shahidi.source` and `Shahidi.target` are literally `productInducedOf` with the
general character `leviHalfCharacter B hopen` described below.
`TopologicalData.shahidiSource` and `TopologicalData.shahidiTarget` are
literally `T.normalizedProductInduced`. The `_eq` lemmas record the unfolding to
`normalizedInducedOf` and `normalizedParabolicInduced`; each holds by `rfl`.
The covariance proofs use only the Library's covariance lemmas
`BlockShape.productInducedOf_covariant` and
`TopologicalData.normalizedProductInduced_covariant`, followed by an exact
scalar computation. Smoothness is the Library's `isSmooth_productInducedOf` or
`isSmooth_normalizedProductInduced`.

Shahidi's display uses `GL_r(O)`-finite functions. Following the task, this
unit uses the Library's smooth induction instead. It does not prove the
comparison of the two descriptions.

## The induction-exponent display (pages 67 and 72)

On pages 67 and 72 Shahidi defines `I(s, π)` by
`f(diag(g₁, g₂) u g) = |det g₁|^{1/2(s+n/2)} / |det g₂|^{1/2(s+m/2)}
π₁(g₁) ⊗ π₂(g₂) f(g)`. Read literally, the exponents are `s/2 + n/4` and
`-(s/2 + m/4)`. The positive half of the standard modulus
`δ_P(diag(g₁, g₂)) = |det g₁|^n / |det g₂|^m`, combined with the twists `s/2` and
`-s/2`, gives `(s + n)/2` and `-(s + m)/2` instead.

Lemma 2.2 on page 84 supports the normalized reading. Take equal ranks `m = n`.
There `A(s, π, w₀) f(g) = lim ∫_G π₁(-a) ⊗ π₂(a⁻¹) |det a|^{s-n} f(v_a g) ψ_m(a) da`.
The proof combines Lemma 2.1, whose integrand carries `|det a|^{-n} d*a`, with
the factorization of `w₀ (1, a⁻¹; 0, 1)` displayed there. Since
`d*a = |det a|^{-n} da` on `GL_n`, that factor is `|det a|^{-2n} da`. The diagonal
factor `diag(-a, a⁻¹)` contributes `|det a|^{(s+n)/2 + (s+n)/2} = |det a|^{s+n}`
under the normalized exponents. The total is the lemma's `|det a|^{s-n}`. The
literal exponents would give `|det a|^{s-3n/2}`.

This unit therefore implements the normalized exponents `(s + n)/2` and
`-(s + m)/2`. This interpretation is inferred from the source's computations.
It is not a known published erratum. For the target `I(-s, π₂ ⊗ π₁)`, the same
normalization with blocks `(n, m)` and parameter `-s` gives `(m - s)/2` on the
`GL_n` block and `(s - n)/2` on the `GL_m` block. The author of this unit read
printed pages 67, 70–73 and 84–87 of the registered scan directly.

## Complex powers of positive characters

All declarations in this and the next four sections lie in `Langlands.Shahidi`.

- `complexPower δ t` sends `h` to the unit `((δ h : ℝ) : ℂ) ^ t` for a positive
  character `δ : H →* ℝ≥0ˣ` and any complex `t`. It uses Mathlib's complex
  power of a positive real number, and `complexPower_apply` records the value.
  Multiplicativity in `h` comes from `Complex.mul_cpow_ofReal_nonneg`.
- `complexPower_zero`, `complexPower_add`, `complexPower_neg`,
  `complexPower_mul`, `complexPower_inv` and `complexPower_pow` give the
  exponent and character laws.
- `complexPower_half` shows that exponent `1/2` gives the Library's
  `Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ)`.
  `complexPower_ofReal` shows that real exponents give the Library's
  `realPowerCharacter`.
- `ker_le_ker_complexPower`: the kernel of `δ` lies in the kernel of each
  complex power.
- `sqrt_mul_cpow_mul_cpow` is the scalar identity behind both covariance laws:
  for positive units `x, y`,
  `√(x^b / y^a) · (x^t₁ · y^t₂) = x^(t₁ + b/2) · y^(t₂ - a/2)`.

## Absolute values, determinant twists and smoothness

Let `F` be a field and `abv : AbsoluteValue F ℝ` a Mathlib absolute value.

- `absUnits abv : Fˣ →* ℝ≥0ˣ` restricts `abv` to the units.
- `determinantAbs abv n : GL_n(F) →* ℝ≥0ˣ` sends `g` to `|det g|`, composing
  with the Library's actual `GeneralLinear.determinant`.
- `determinantPower abv n t` is the determinant twist `g ↦ |det g|^t`
  (`determinantPower_apply`, with `_add`, `_neg` and `_zero`).

With a topology on `F`:

- `IsOpenNormOne abv` is the precise smoothness hypothesis of the general layer:
  the norm-one units of `abv` form an open subset of `Fˣ`.
- If `F` is also a topological ring, `isOpen_ker_determinantAbs` and
  `isOpen_ker_determinantPower` show that `|det|` and every `|det|^t` have open
  kernels. The proof pulls back through the Library's continuous determinant.
  `determinantPowerCharacter` packages `|det|^t` as a Library
  `Induction.SmoothCharacter`.
- `isOpenNormOne_of_valuation` covers fields with a `ValuativeRel` and a
  valuative topology. There, an absolute value equal to `1` on valuation units
  satisfies `IsOpenNormOne`. This is exactly the field `abv_unit` of the
  Library's Jacquet normalization data `IsJacquetNormalization`. The proof
  uses Mathlib's openness of the valuation sphere of radius one.

## The block modulus and its positive half

For any block shape `B` and absolute value `abv`:

- `blockDeterminantAbs abv B i` is `m ↦ |det m_i|` on the actual Levi `B.Levi F`.
- `leviModulus abv B` is the explicit formula
  `∏_{i<j} |det m_i|^(n_j) / |det m_j|^(n_i)` (`leviModulus_apply`). It has the
  same shape as the Library's p-adic `TopologicalData.leviModulus`.
- `leviHalfModulus abv B` is its positive complex square root `δ_P^(1/2)`
  (`leviHalfModulus_apply`, `leviHalfModulus_eq_complexPower`). It equals one
  exactly where the modulus does (`leviHalfModulus_eq_one`).
- `isOpen_ker_leviModulus` and `isOpen_ker_leviHalfModulus` hold under
  `IsOpenNormOne abv`. The kernel contains the finite intersection of the open
  block-determinant kernels.
- `leviHalfCharacter B hopen` is the normalizing smooth character used by the
  general induction (`leviHalfCharacter_toMonoidHom`).

Thus the general layer uses actual determinant characters and the explicit
block-modulus formula built from the given absolute value. It never takes an
unconstrained character. The unit does not prove the Haar-measure meaning of
this formula, the Library's separately stated `GLBlockModulusHaarStatement`.
No proof here depends on it.

## The two shapes and `swapRank`

The source uses the published `twoBlocks m n hm hn : BlockShape (m+n)` from
`Langlands.Representation.Shahidi.TwoBlocks`.

- `swappedTwoBlocks m n hm hn : BlockShape (m+n)` is a reducible shape with two
  blocks of sizes `![n, m]` on the same ambient rank `m + n`.
  `swappedTwoBlocks_eq_rankCast` proves by `rfl` that it is the Library rank
  transport `(twoBlocks n m hn hm).rankCast (Nat.add_comm n m)`.
  `swappedTwoBlocks_size_zero` and `_size_one` give the sizes.
- `leviModulus_twoBlocks` and `leviModulus_swappedTwoBlocks` (general layer)
  evaluate the modulus as `|det g₀|^n / |det g₁|^m` and `|det g₀|^m / |det g₁|^n`.

The relation between `Fin (n+m)` and `Fin (m+n)` is explicit and proved. It
uses the Library's `swapRank m n R : GL_(n+m)(R) ≃* GL_(m+n)(R)`, which is
`GeneralLinear.reindex (finCongr (Nat.add_comm n m))`. Over any commutative
ring `R`:

- `swappedTwoBlocks_index`: the consecutive coordinates of the swapped shape are
  the `Fin.cast` of those of `twoBlocks n m`.
- `swapRank_mem_swappedTwoBlocks_parabolic_iff`: `swapRank` carries the
  `(n, m)` parabolic of `GL_(n+m)` exactly onto the parabolic of
  `swappedTwoBlocks`.
- `swappedParabolicEquiv` is the resulting group isomorphism of the two
  parabolics. Its value is `swapRank` (`swappedParabolicEquiv_coe`).
- `leviProjection_swappedParabolicEquiv`: the Levi projections agree, and both
  Levi groups are literally `GL_n × GL_m`.
- `swappedTwoBlocks_leviEmbedding`: the Levi embedding of the swapped shape is
  `swapRank (GeneralLinear.blockSum (l 0, l 1))`. The proof combines the
  published `twoBlocks_leviEmbedding` with an entrywise identity.

## Two-factor carriers and twists

- `pairCarrier V₁ V₂ : Fin 2 → Type uV` is the family `![V₁, V₂]`. It has
  instance-level `AddCommGroup` and `Module` structures. The block tensor
  carrier is `PiTensorProduct ℂ (pairCarrier V₁ V₂)`, which is `V₁ ⊗ V₂` as a
  `PiTensorProduct`.
- `pairVector v₁ v₂` and `pairTensor v₁ v₂` give the family and the pure tensor
  `v₁ ⊗ v₂`.
- `pairFamily ρ₁ ρ₂` assigns the representations of the two diagonal blocks
  (`pairFamily_zero`, `pairFamily_one`).
- `blockTensor_pairTensor`: the Library block tensor acts by
  `π₁(g 0) v₁ ⊗ π₂(g 1) v₂` on pure tensors.
- `blockTensor_pairFamily_twist`: twisting the factors by characters `χ₁, χ₂`
  multiplies the block tensor by the scalar `χ₁(g 0) χ₂(g 1)`. The proof uses
  multilinearity of `PiTensorProduct.tprod`.
- `twistedPair abv t ρ₁ ρ₂` is the inducing pair
  `ρ₁ |det|^(t/2), ρ₂ |det|^(-t/2)`. Each factor is the Library twist
  `Langlands.twist` of the representation by `determinantPower`.

The two representation carriers share one universe `uV`. This is the documented
common representation universe. The field universe `uF` is independent, and
the induced carriers live in `Type (max uF uV)`.

## The general induced representations

Let `F` be a topological field and a topological ring with an absolute value
`abv`, and let `hopen : IsOpenNormOne abv`. Assume `0 < m`, `0 < n` and `s : ℂ`.

- `SourceSpace abv hopen hm hn s π₁ π₂` is the Library's carrier
  `Induction.SmoothFunctions`. Its elements are functions on `GL_(m+n)(F)` with
  values in `V₁ ⊗ V₂`, covariant for the `(m, n)` parabolic, each fixed under
  right translation by some open subgroup.
- `source abv hopen hm hn s π₁ π₂` is `I(s, π₁ ⊗ π₂)`, namely
  `(twoBlocks m n hm hn).productInducedOf (leviHalfCharacter _ hopen)
  (twistedPair abv s π₁ π₂)`.
- `sourceEval f g ∈ V₁ ⊗ V₂` is the value of `f` at `g`. `sourceFunction` is the
  linear map to underlying functions (`sourceFunction_apply`).
- `source_eq`: by `rfl`, this is `normalizedInducedOf` of the block tensor.
- `source_apply`: the group acts by right translation,
  `(I(s)(g) f)(x) = f(x g)`.
- `isSmooth_source`: the representation is smooth.
- `source_covariant`: let `p` lie in the `(m, n)` parabolic with Levi blocks
  `g₁ = leviProjection p 0 ∈ GL_m` and `g₂ = leviProjection p 1 ∈ GL_n`. Then
  `f(p g) = |det g₁|^((s+n)/2) · |det g₂|^(-(s+m)/2) · (π₁ ⊗ π₂)(g₁, g₂) f(g)`.
  Here each `|det gᵢ|` is the complex number
  `abv (det gᵢ)`, and the action is the Library block tensor of
  `pairFamily π₁ π₂`.

Similarly, `TargetSpace`, `target`, `targetEval`, `targetFunction`,
`targetFunction_apply`, `target_eq`, `target_apply` and `isSmooth_target`
describe `I(-s, π₂ ⊗ π₁)`. This is
`(swappedTwoBlocks m n hm hn).productInducedOf (leviHalfCharacter _ hopen)
(twistedPair abv (-s) π₂ π₁)`, with values in `V₂ ⊗ V₁`.

- `target_covariant`: let `p` lie in the parabolic of `swappedTwoBlocks`, with
  `g₁ ∈ GL_n` and `g₂ ∈ GL_m`. Then
  `f(p g) = |det g₁|^((m-s)/2) · |det g₂|^((s-n)/2) · (π₂ ⊗ π₁)(g₁, g₂) f(g)`.
- `target_covariant_swapRank`: the same law holds for
  `p ∈ (twoBlocks n m hn hm).parabolic F` acting by `swapRank m n F p`. The Levi
  blocks are those of `twoBlocks n m`. This is the form used by the
  intertwining operator from `I(s)` to `I(-s)`.

**Field scope.** The general layer needs exactly a field `F` with a topology
making it a topological ring, an explicit real absolute value `abv`, and
`IsOpenNormOne abv`. Shahidi's normalization takes the normalized absolute
value of a non-archimedean local field, with `|ϖ| = q⁻¹` and value one on
units. Its unit condition gives `IsOpenNormOne` by
`isOpenNormOne_of_valuation`. The covariance laws hold for every admissible
`abv`. They use no uniformizer normalization, so this unit asserts nothing
that depends on it. The hypothesis fails for the usual absolute values of
`ℝ` and `ℂ`, so this layer does not model the archimedean case. It is stated for
all fields, including those of positive characteristic. For these, the
identification of `leviModulus` with a Haar modulus is not proved here, just
as in the p-adic case.

## The p-adic specialization

These declarations lie in `Langlands.PadicField.TopologicalData`, for
`F : PadicField p` and a supplied realization `T : F.TopologicalData`.

- `residueCardinality_real_pos`: `0 < q` as a real number.
- `shahidiAbsoluteValue` is the Library's residue-normalized absolute value
  `T.normalizedAbs`, with `|ϖ| = q⁻¹`, packaged as a Mathlib `AbsoluteValue`
  (`shahidiAbsoluteValue_apply`). The triangle inequality follows from the
  Library's ultrametric inequality.
- Comparison, for any `abv` with `∀ x, abv x = T.normalizedAbs x`:
  - `absUnits_eq_normalizedAbsUnits`;
  - `determinantAbs_eq_determinantNorm`;
  - `isOpenNormOne_of_eq_normalizedAbs`, so the general smoothness hypothesis
    holds;
  - `leviModulus_eq_leviModulus` and `leviHalfModulus_eq_leviHalfModulus`:
    the general modulus and its half are the Library's `T.leviModulus` and
    `T.leviHalfModulus`;
  - `leviHalfCharacter_eq_leviHalfCharacter`: the general normalizing
    character is `T.leviHalfCharacter`.
- `determinantComplexPower n t` is the Library character
  `T.determinantUnramifiedCharacter n` at the nonzero complex parameter
  `LocalFactor.spectralParameter q _ t = exp(-t log q) = q^(-t)`
  (`determinantComplexPower_def`). The task text calls this character
  `T.unramifiedDeterminantCharacter`; its Library name is
  `T.determinantUnramifiedCharacter`.
- `determinantComplexPower_apply` gives agreement with the positive normalized
  determinant absolute value:
  `T.determinantComplexPower n t g = ((T.determinantNorm n g : ℝ) : ℂ) ^ t`.
  The proof expands `(q^(-t))^(ord det g)` and uses the Library's
  `determinantNorm_eq_residue_pow`. Consequences include
  `determinantComplexPower_eq_complexPower`,
  `determinantPower_eq_determinantComplexPower` (for `abv` as above),
  `_add`, `_neg`, `_zero`, `_ofReal` (real exponents give
  `realPowerCharacter`), and `isOpen_ker_determinantComplexPower`. The last is
  the Library's open-kernel result for unramified determinant characters.
- `leviModulus_swappedTwoBlocks`:
  `T.leviModulus (swappedTwoBlocks m n hm hn) g =
  T.determinantNorm n (g 0)^m / T.determinantNorm m (g 1)^n`. The companion
  `T.leviModulus_twoBlocks` is published in `TwoBlocks`.
- `shahidiTwistedPair T t ρ₁ ρ₂` is the inducing pair built with
  `determinantComplexPower`. `twistedPair_eq_shahidiTwistedPair` proves it
  equal to the general `twistedPair` for any `abv` agreeing with
  `T.normalizedAbs`.
- `ShahidiSourceSpace`, `shahidiSource`, `shahidiSourceEval`,
  `shahidiSourceFunction`, `shahidiSourceFunction_apply`, `shahidiSource_eq`,
  `shahidiSource_apply` and `isSmooth_shahidiSource` give the p-adic
  `I(s, π₁ ⊗ π₂)`. It equals
  `T.normalizedProductInduced (twoBlocks m n hm hn) (T.shahidiTwistedPair s π₁ π₂)`,
  and `shahidiSource_eq` identifies it by `rfl` with `T.normalizedParabolicInduced`
  of the block tensor.
- `shahidiSource_covariant` is the p-adic covariance with exponents
  `(s+n)/2` and `-(s+m)/2`, written with `T.normalizedAbs (det gᵢ)`.
- `ShahidiTargetSpace`, `shahidiTarget`, `shahidiTargetEval`,
  `shahidiTargetFunction`, `shahidiTargetFunction_apply`, `shahidiTarget_eq`,
  `shahidiTarget_apply`, `isSmooth_shahidiTarget`, `shahidiTarget_covariant`
  (exponents `(m-s)/2`, `(s-n)/2`) and `shahidiTarget_covariant_swapRank`
  give the p-adic `I(-s, π₂ ⊗ π₁)` on `GL_(m+n)(F)`. It equals
  `T.normalizedProductInduced (swappedTwoBlocks m n hm hn)
  (T.shahidiTwistedPair (-s) π₂ π₁)`.

The two layers are compared character by character: the modulus, its half,
the normalizing character and the inducing pair. The carriers are not
identified by a type equality. For `abv` agreeing with `T.normalizedAbs`, the
general carrier is built from `leviHalfCharacter B hopen` and `twistedPair`,
the p-adic one from `T.leviHalfCharacter B` and `shahidiTwistedPair`. These
data are proved equal, not definitionally identified.

In `Langlands.PadicField`, the canonical aliases `canonicalShahidiSourceSpace`,
`canonicalShahidiSource`, `canonicalShahidiTargetSpace` and
`canonicalShahidiTarget` specialize the construction to
`F.canonicalTopologicalData`.

The p-adic layer covers exactly the Library's `PadicField p`, a field with a
specified finite-dimensional algebra structure over Mathlib's `Padic p`. It makes no claim about
positive-characteristic local fields; those are covered only by the general
layer above.

## Not included

This unit constructs only the twists, the two shapes and the induced
representations. It does not formalize the Weyl element, the intertwining
integral `A(s, π, w_{m,n})`, its convergence or continuation, Whittaker or
Jacquet functionals, the local coefficient `C(s)`, or the comparison with
gamma factors. These belong to later units of the parent task. The
identification of `V₁ ⊗ V₂` with a two-factor `TensorProduct` and the
tensor flip `V₁ ⊗ V₂ ≃ V₂ ⊗ V₁` are not constructed here. No analytic
compatibility statement is assumed.
