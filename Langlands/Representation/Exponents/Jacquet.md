# Exponents of normalized Jacquet modules along the split centre

Author: Worker 23.

This module defines the exponents of a representation of `GL_n(F)` along a
standard block parabolic, and the real parts of characters of `(F^×)^r`. These
are the inputs of Casselman's square-integrability criterion and of the tempered
criterion. The criteria themselves are separate theorems.

## Generic layer

`A` is a monoid, `R` a commutative ring and `π` a representation of `A` on an
`R`-module `V`. A character is a monoid homomorphism `χ : A →* Rˣ`.

- `characterSpace π χ k` is the submodule of vectors killed by
  `(π(a) - χ(a))^k` for every `a ∈ A`. It is the intersection of Mathlib's
  generalized eigenspaces `genEigenspace (π a) (χ a) k`. `mem_characterSpace`
  states membership explicitly.
- `IsGeneralizedEigencharacter π χ` holds when some `characterSpace π χ k` is
  nonzero: some nonzero vector `v` and a single exponent `k` satisfy
  `(π(a) - χ(a))^k v = 0` for all `a`. `isGeneralizedEigencharacter_iff` gives
  this explicit form. `isGeneralizedEigencharacter_of_eigenvector` treats the
  case of an actual eigenvector.

The exponent `k` is uniform in `a`, as in the published uniform central-character
spaces of `Exponents/Central`. No commutativity is needed for the definition. The
GL application uses the commutative group `(F^×)^r`. Unlike `Exponents/Central`,
the character is defined directly on the acting group, with no coercion through a
centre.

## Split centre

For an ordered block shape `B = (n_1, …, n_r)` of `n` and a commutative ring `F`:

- The published `B.blockScalarLevi F : (Fin r → F^×) →* B.Levi F` from
  `Group/GL/BlockIwahoriDefinitions` sends `a` to the block-scalar family
  `(a_1 1_{n_1}, …, a_r 1_{n_r})`, using `GeneralLinear.scalar` in each block
  (`blockScalarLevi_apply`). This module reuses that map.
- `blockScalarLevi_mem_center` proves that block scalars are central in the block
  Levi. That they exhaust the centre is not needed here and is not stated.

## Exponents along a standard block parabolic

For a p-adic field `F`, a realization `T` and a complex representation `ρ` of
`GL_n(F)`:

- `T.splitCentreJacquet B ρ` is the published normalized Jacquet module
  `T.normalizedJacquet B ρ` of `Jacquet/Parabolic`, restricted along
  `B.blockScalarLevi`. It is a representation of `(F^×)^r` on the actual Jacquet
  module `B.JacquetModule ρ`. The normalization is the published one:
  `δ_P^(-1/2)` for the standard upper block parabolic and the full explicit block
  modulus. `splitCentreJacquet_mk` displays it on classes of vectors:
  `a · [v] = δ_P(a)^(-1/2) [ρ(a) v]`.
- `T.IsJacquetExponent B ρ χ` holds when `χ : (F^×)^r →* ℂ^×` has open kernel for
  the topology of `T` (a smooth character) and is a generalized eigencharacter of
  `T.splitCentreJacquet B ρ`.

## Real parts

- `T.IsRealPartOf χ x`, for `x : Fin r → ℝ`, states
  `‖χ(a)‖ = ∏_i |a_i|^(x_i)` for all `a ∈ (F^×)^r`. Here `|·|` is the published
  residue-normalized absolute value `T.normalizedAbs` (`|ϖ| = q⁻¹`), and the
  powers are real powers.
- `IsRealPartOf.eq` proves that the real part is unique. The proof evaluates at
  `a = (1, …, ϖ, …, 1)` with the published uniformizer `T.uniformizer`, and uses
  `|ϖ| = q⁻¹` with `q > 1`, so that the logarithm of `|ϖ|` is nonzero.

Existence of a real part is not asserted. It holds for every character of
`(F^×)^r` with open kernel. Such a character maps the compact group of integral
units onto a finite group, so `|χ|` is trivial there and is determined by its
values on the uniformizer in each coordinate. That is a theorem not stated here.

## Source correspondence

- Casselman (1995), printed pages 44--45 (PDF pages 44--45), before Theorem
  4.4.6: "If P is a parabolic subgroup of G and (π, V) an admissible
  representation of G, then according to 3.3.1 the representation (π_N, V_N) is
  admissible as well. By 2.1.9 this representation is a direct sum of
  subrepresentations (V_N)_{χ,∞}, χ ranging over a set of characters of the
  center of M. I call the restriction to A of the characters χ such that
  (V_N)_{χ,∞} ≠ 0 the central characters of π with respect to P. (These are what
  Harish-Chandra calls exponents in [20].)"
  - Theorem 4.4.6 then tests `|χ δ^(-1/2)(a)| < 1`.
  - Here the generalized eigenspace condition is imposed directly on the split
    centre `A`, which for a block Levi of `GL_n` is the group of block scalars.
  - The Jacquet module is the normalized one, so the twist by `δ^(-1/2)` that
    Casselman applies in the criterion is built into the exponent.
  - The direct-sum decomposition of 2.1.9 is a theorem and is not used.

Registered source:

- `casselman-1995-admissible-representations`, SHA256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`, printed
  pages 44--45.

## Derivations

- **Normalization.** The exponent is defined for the normalized Jacquet module
  with `δ_P^(-1/2)` and the standard upper parabolic. With this convention the
  Steinberg representation of `GL_2` should have real part `(1/2, -1/2)` along
  the Borel. That is a theorem not proved here. The tempered criterion then
  reads: every partial sum `x_1 + ⋯ + x_j` is nonnegative and the total is zero.
- **Smoothness.** The open-kernel condition records that exponents of smooth
  representations are smooth characters. Casselman's characters arise from an
  admissible representation and are smooth automatically, by a theorem.
- **Domain.** `ρ` is arbitrary, with no admissibility hypothesis. For
  non-admissible `ρ` the set of exponents need not be finite and the Jacquet
  module need not decompose. Admissibility is a hypothesis of the criteria, not
  of the definition.

## Not claimed

The module proves none of the following, which are separate theorem obligations:

- finiteness of the set of exponents, or the decomposition of the Jacquet module
  into generalized eigenspaces;
- existence of real parts for characters with open kernel;
- that the block scalars are the whole centre of the Levi;
- the identification of the explicit block modulus with the Haar modulus;
- Casselman's square-integrability criterion, or the tempered exponent
  criterion.
