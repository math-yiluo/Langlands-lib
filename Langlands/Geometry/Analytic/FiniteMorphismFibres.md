# Finite fibres of finite bounded algebra maps

Author: Worker 36.

This module proves that a bounded algebra map which is finite as a ring map
has finite fibres on spectra. The proof uses the completed residue fields of
spectrum points and the uniqueness of absolute values extending a complete
ultrametric norm to an algebraic extension. That uniqueness is proved here
also for trivially normed fields.

## Original source and derived provenance

The source is Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields* (1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
PDF SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
Corollary 2.1.16, printed p.27 / PDF p.41, states: "Let `ℬ` be a finite
Banach algebra over a k-affinoid algebra `𝒜`, and suppose the canonical
homomorphism `𝒜 → ℬ` is injective. Then the map `𝓜(ℬ) → 𝓜(𝒜)` is surjective
and has finite fibres." The finite fibres of finite morphisms are also used,
without proof, in Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`: the proof
of Lemma 3.1.2, printed p.54 / PDF p.51, writes `φ⁻¹(x) = {y = y₁, …, yₙ}`.

`BoundedAlgHom.finite_fibre` proves the finite-fibre half of Corollary 2.1.16
in greater generality. It needs neither injectivity nor admissibility of the
finite module structure. The algebras need not be affinoid, and the ground
field need not be complete or nontrivially valued. It requires only an
ultrametric ground field and ring-theoretic finiteness. Surjectivity is not
treated. The proof is derived.

The uniqueness of extensions of absolute values is classical. For
nontrivially normed fields the module uses Mathlib's spectral norm theorem
`spectralNorm_unique_field_norm_ext`. The trivially normed case is proved
directly below. This part is internal, without a source passage.

## Absolute values on algebraic extensions

Let `F` be a normed field and `E` a field which is an `F`-algebra.

- `absoluteValue_le_one_of_trivial`: suppose every nonzero element of `F` has
  norm `1`, and `f` is a nonarchimedean absolute value on `E` extending the
  norm of `F`. Then `f x ≤ 1` for every `x` integral over `F`. If `f x > 1`,
  write the monic minimal polynomial of `x` of degree `n ≥ 1` as
  `xⁿ = -∑_{i<n} aᵢ xⁱ`. The strong triangle inequality gives
  `f(x)ⁿ ≤ f(aᵢ) f(x)ⁱ ≤ f(x)ⁱ` for some `i < n`, which is impossible.
- `absoluteValue_eq_one_of_trivial`: under the same hypotheses, `f x = 1` for
  every nonzero algebraic `x`. Apply the preceding bound to `x` and to `x⁻¹`.
- `absoluteValue_eq_of_extends`: let `F` be complete and ultrametric and `E`
  algebraic over `F`. Two nonarchimedean absolute values on `E` that both
  extend the norm of `F` are equal. If some nonzero element of `F` has norm
  different from `1`, `F` is nontrivially normed (Mathlib's
  `NontriviallyNormedField.ofNormNeOne`). Both absolute values then equal the
  spectral norm. Otherwise both are `1` on every nonzero element.

## Finitely many norm-distinguished maps

`pullbackAbsoluteValue φ` is the absolute value `q ↦ ‖φ q‖` on a field `Q`,
for a ring map `φ` from `Q` to a normed field. Such a map is injective.

`finite_of_isometric_family` is the counting step. Let `H` be a complete
ultrametric normed field and `T` a finite `H`-algebra. Let `Φ i : T → L i`
(`i : ι`) be ring maps to ultrametric normed fields that are isometric on `H`.
Suppose two indices with `‖Φ i b‖ = ‖Φ j b‖` for all `b` are equal. Then `ι`
is finite.

1. `T` is an Artinian ring, so its prime spectrum is finite. The kernel of
   each `Φ i` is prime, since `L i` is a field.
2. Suppose `Φ i` and `Φ j` have the same kernel `I`. `I` is maximal, `T ⧸ I`
   is a field, and it is finite, hence algebraic, over `H`. Both maps descend
   to `T ⧸ I`, and the pulled-back absolute values are nonarchimedean and
   extend the norm of `H`. By the uniqueness theorem they are equal. So
   `‖Φ i b‖ = ‖Φ j b‖` for every `b`, and `i = j`.
3. Hence `i ↦ ker (Φ i)` is injective into a finite set.

## Points over a point

Let `K` be an ultrametric normed field, `R` and `S` normed commutative
`K`-algebras with `S` an `R`-algebra, and `t` a point of the spectrum of `R`.

- `ResidueOver K R x` is the Library's completed residue field
  `CompletedResidueField K x` of a point `x` of an `R`-algebra `A`. It is a
  type synonym that carries the `R`-algebra structure given by the residue
  map `ResidueOver.residue` composed with `algebraMap R A`.
  `ResidueOver.norm_residue` records `‖residue a‖ = x a`. The synonym keeps
  this structure apart from the canonical `K`-algebra structure of the
  completion.
- `fibreResidueEmbedding t s hs`: for a point `s` with
  `s (algebraMap R S a) = t a` for all `a`, the Library's
  `completedResidueLiftRingHom` extends `a ↦ residue_s (algebraMap R S a)` to
  an `R`-algebra map from `ResidueOver K R t` to `ResidueOver K R s`. It is an
  isometry (`isometry_fibreResidueEmbedding`).
- `residueAlgHom s` is the residue map of `s` as an `R`-algebra map.
- `fibreTensorMap t s hs` is Mathlib's `Algebra.TensorProduct.productMap` of
  these two maps, from `ResidueOver K R t ⊗[R] S` to `ResidueOver K R s`.

`finite_setOf_over K t`: if `S` is a finite `R`-module, the set of points `s`
with `s (algebraMap R S a) = t a` for all `a` is finite. Apply
`finite_of_isometric_family` with `H = ResidueOver K R t` and the finite
`H`-algebra `H ⊗[R] S` (Mathlib's base change of a finite module). On
`c ⊗ 1` the map is the isometric embedding. On `1 ⊗ a` its norm is
`‖residue_s a‖ = s a`, so equal norms force equal points.

## Fibres of bounded algebra maps

For `f : BoundedAlgHom K R S` and a point `t` of the spectrum of `R`:

- `BoundedAlgHom.fibre f t` is the set of points `s` with
  `BanachSpectrum.comap f s = t`.
- `isClosed_fibre`: fibres are closed, as preimages of points under the
  continuous spectrum map into a Hausdorff space.
- `finite_fibre`: if `f` is finite as a ring map, every fibre is finite.
  Make `S` an `R`-algebra through `f` and apply `finite_setOf_over`.

## Scope

Surjectivity of spectrum maps of injective finite maps, completed tensor
products `ℬ ⊗̂ ℋ(x)` and the analytic-space fibres of Berkovich 1990 §3.1 are
not treated. The result is the first input to Berkovich 1993 Lemma 3.1.2.
That lemma, the small neighborhoods in finiteness at a point, is not proved
here.
