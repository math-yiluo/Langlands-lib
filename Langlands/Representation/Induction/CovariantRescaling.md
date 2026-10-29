# Rescaling smooth induced functions by covariant scalars

Author: Worker 1023.

This module realizes a real-parameter family of smoothly induced
representations on one function space. It is a helper for the adjacent
two-supercuspidal reducibility argument of Zelevinsky 1980, Proposition 1.11,
but its declarations are stated for an arbitrary topological group `G`, a
subgroup `P` and a complex representation `σ` of `P` on `V`. Nothing here is
specific to `GL_n`, and no unitarity, irreducibility or reducibility statement is
proved.

## Covariant scalars and the rescaled induction

`CovariantScalar P χ`, for a character `χ : P →* ℂˣ`, is a structure with
a function `toFun : G → ℂˣ`, a proof of left covariance
`toFun (q x) = χ q * toFun x` for `q ∈ P`, an open subgroup `stabilizer`,
and a proof that `toFun (x k) = toFun x` for `k` in that subgroup.

`rescaleEquiv c σ` is the complex linear equivalence
`SmoothFunctions P σ ≃ₗ[ℂ] SmoothFunctions P (twist χ σ)` given by
pointwise multiplication by `c.toFun`. Its inverse multiplies by the pointwise
inverse unit. The simp lemmas `rescaleEquiv_eval` and `rescaleEquiv_symm_eval`
record these values: `(c x) • f x` and `(c x)⁻¹ • f x`. Right smoothness of the
product uses the intersection of the function's stabilizer with
`c.stabilizer`. `eval_smoothInduced` records that
`smoothInduced P σ g f` evaluates at `x` to `f (x g)`.

`rescaledInduced c σ` is the representation of `G` on
`SmoothFunctions P σ` obtained by conjugating `smoothInduced P (twist χ σ)` by
`rescaleEquiv c σ`. `rescaledInducedEquiv c σ` is the equivalence of
representations, with linear part `rescaleEquiv c σ`, from it to
`smoothInduced P (twist χ σ)`. `eval_rescaledInduced` gives its values:
`(rescaledInduced c σ g f) x = ((c x)⁻¹ c (x g)) • f (x g)`.

## Heights and the family

`IwasawaHeight P` is a structure with a compact open subgroup
`compactSubgroup` (call it `K`), the factorization field
`factor : ∀ g, ∃ q ∈ P, ∃ k ∈ K, g = q k`, a character
`modulus : P →* ℝ≥0ˣ` (call it `N`), and `modulus_eq_one`, saying `N q = 1`
when `q ∈ P ∩ K`.

`positivePower s` is the monoid homomorphism `ℝ≥0ˣ →* ℂˣ`,
`r ↦ r ^ s`, built from `NNReal.rpowMonoidHom s` and the Library's
`positiveUnitsToComplex`. `coe_positivePower` gives its complex value, and
`positivePower_comp` says that composing it with `N` is, by definition, the
Library's `realPowerCharacter N s`.

For `H : IwasawaHeight P` the following are defined.

- `H.height x` is `N q` for the factorization `x = q k` chosen by
  `Classical.choose`. `height_mul_of_mem` shows that `H.height (q k) = N q`
  for every `q ∈ P` and `k ∈ K`, so the choice does not matter. This uses
  `modulus_eq_one` on `q'⁻¹ q ∈ P ∩ K`. Consequently `height_mul_left`
  gives `H.height (q x) = N q * H.height x`, and `height_mul_right` gives
  `H.height (x k) = H.height x` for `k ∈ K`.
- `H.heightScalar s` is the covariant scalar `x ↦ (H.height x) ^ s` for the
  character `realPowerCharacter N s`, with stabilizer `K`.
- `H.family σ s` is `rescaledInduced (H.heightScalar s) σ`, a representation
  of `G` on the fixed space `SmoothFunctions P σ` for every real `s`.
- `H.familyEquiv σ s` is an equivalence of `H.family σ s` with
  `smoothInduced P (realPowerTwist N s σ)`, the smooth induction of `σ`
  twisted by `N ^ s`.

## Properties of the family

- `H.ratio g x` is `(H.height x)⁻¹ * H.height (x g)`. `ratio_mul_left`
  shows that it is left `P`-invariant in `x`. `eval_family` gives
  `(H.family σ s g f) x = (H.ratio g x) ^ s • f (x g)`.
- `family_apply_of_mem` shows that `H.family σ s k = smoothInduced P σ k` for
  every `s` and every `k ∈ K`. `family_apply_eq_of_mem` deduces
  `H.family σ s k = H.family σ t k` for `k ∈ K`.
- `inner_eval_family_neg` takes `b : InnerProductSpace.Core ℂ V` (no
  invariance under `σ` is assumed). It shows that, for all `s`, `g`, `f`,
  `h` and `x`,
  `b.inner ((H.family σ s g f) x) ((H.family σ (-s) g h) x)
  = b.inner (f (x g)) (h (x g))`. The two scalar factors are the real numbers
  `r ^ s` and `r ^ (-s)` for the same positive `r`, and their product is 1.
- `H.ratioStabilizer g` is the open subgroup `K ∩ g K g⁻¹`. `ratio_mul_right`
  shows `H.ratio g (x k) = H.ratio g x` for `k` in it.
  `ratio_isLocallyConstant` follows.
- `ratio_range_finite` shows that `H.ratio g` takes finitely many values. The
  ratio is left `P`-invariant, `G = P K`, and a locally constant function on
  the compact space `K` has finite range.
- `invariantMul σ φ hφ K' hK' f` is the function `x ↦ φ x • f x`, for a
  complex function `φ` on `G` that is left `P`-invariant (`hφ`) and right
  invariant under an open subgroup `K'` (`hK'`). It is again an element of
  `SmoothFunctions P σ`.
- `family_eq_sum` writes `H.family σ s g f` as a finite sum. The sum runs over
  the values `r` of `H.ratio g`, and the term for `r` is `r ^ s` times
  `invariantMul` of the indicator of `{x | H.ratio g x = r}` applied to
  `smoothInduced P σ g f`. Only the coefficients `r ^ s` depend on `s`.
- `continuous_family_apply` shows that, for every `g`, every
  `f : SmoothFunctions P σ` and every linear functional
  `ℓ : Module.Dual ℂ (SmoothFunctions P σ)`, the map `s ↦ ℓ (H.family σ s g f)`
  is continuous on `ℝ`. This follows from `family_eq_sum`, since each
  `s ↦ r ^ s` with `r > 0` is continuous.

## Provenance

The construction is derived; no source contains these exact declarations. It
implements the step in the proof of Zelevinsky 1980, Proposition 1.11 (printed
p.175, PDF p.12), literature ID `zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. There
Zelevinsky writes: "Using the restriction of pi_s to the maximal compact
subgroup of G_2k, one can realize all pi_s on the same space E."

The source realizes the family by restricting functions to the maximal compact
subgroup. This module instead keeps the untwisted space of `P`-covariant
functions. It transports each twisted induction there by multiplication with the
power `height ^ s` of a height function defined from `G = P K`. The two models
agree on `K`, which `family_apply_of_mem` records. The finite-sum formula
`family_eq_sum` and the weak continuity `continuous_family_apply` stand in for
the source's analytic dependence on `s`. `inner_eval_family_neg` is the
pointwise identity that later gives a pairing between the members at `s` and
`-s` that is invariant under both. The module does not construct that pairing.
The source file is
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.
The module was compiled against pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
