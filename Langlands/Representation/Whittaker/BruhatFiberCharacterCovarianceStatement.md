# Character covariance of the product average under Shalika's fiber action

Authors: Worker 884 and Worker 634. Worker 634 designed the exact Lean proposition
(a private type-checked design, diagnostic `0636c997-161a-4277-8190-c1f3fcfec77b`).
Worker 884 placed it, unchanged, in this module under its final namespace, added the
documentation comments, compiled it, checked the sign against the source and wrote this
Markdown.

`Langlands.Whittaker.BruhatFiberCharacterCovarianceStatement.{uF}` is the following
proposition. This module defines the proposition and supplies no proof. Its proof,
`Langlands.Whittaker.bruhatFiberCharacterCovariance`, whose type is exactly this
proposition at the same universe, is in the companion module
`Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceProof`. Its
universe `uF`, the universe of the p-adic field, is the only parameter of the
definition. It imports these published modules, all used unchanged:

- `Langlands.Representation.Whittaker.BruhatFiberAverage`, for Shalika's fiber action
  `bruhatFiberAct` and its homeomorphism `bruhatFiberActHomeomorph`;
- `Langlands.Representation.Whittaker.CompatibleTorus`, for `compatibilityDefect`;
- `Langlands.HarmonicAnalysis.Distribution.CharacterAverage`, for
  `SchwartzBruhat.characterAverage`.

The groups, the permutation matrix, the diagonal map, the character, the test-function
space and the pullback come from the modules these import. No new group, action,
character, measure or test-function space is defined.

## Statement

Everything below is universally quantified inside the proposition, in this order.

- `p : ℕ` is a natural number and `_hp : Fact p.Prime` says it is prime. Every prime is
  allowed.
- `F : PadicField.{uF} p` is a p-adic field: a field `F.Carrier`, in an arbitrary
  universe `uF`, with a specified finite-dimensional algebra structure over Mathlib's
  `Padic p`.
- `letI := F.canonicalNormedField` installs on `F.Carrier` the published
  nontrivially normed field structure of `F`, Mathlib's spectral norm extending the
  norm of `ℚ_p`. Every topology below is derived from this norm. Nothing else about
  `F` is assumed.
- `n : ℕ` is arbitrary, including `n = 0`. All matrices have size `n + 1`.
- `ψ : UnitaryAdditiveCharacter F.Carrier` is a continuous, unitary, nontrivial
  additive character of `F.Carrier`.
- `w : Equiv.Perm (Fin (n + 1))` is an arbitrary permutation.
- The following names are local abbreviations (`let`), not hypotheses:
  - `U := upperUnipotent (n + 1) F.Carrier`, the upper unipotent subgroup of the
    published group `Langlands.GeneralLinear (n + 1) F.Carrier` of invertible
    matrices;
  - `P := permutationUnipotentPlus (n + 1) F.Carrier w`, the subgroup
    `U_w⁺ = U ∩ w⁻¹ U w`, consisting of the `g ∈ U` with `p_w * g * p_w⁻¹ ∈ U`;
  - `H := Fin (n + 1) → F.Carrierˣ`, the diagonal parameters;
  - `M := U × (H × U)`, the coordinate space of the cell.
- `letI := borel U` gives `U` its Borel σ-algebra, and
  `letI : BorelSpace U := ⟨rfl⟩` records that this σ-algebra is the Borel one.
- `μ : Measure U` is a measure on `U` (not on `P`) that is s-finite (`SFinite μ`),
  finite on compact sets (`IsFiniteMeasureOnCompacts μ`), left invariant
  (`μ.IsMulLeftInvariant`) and right invariant (`μ.IsMulRightInvariant`). The two
  invariance hypotheses are separate; neither is derived from the other. No Haar
  hypothesis is imposed.
- `α : SchwartzBruhat M` is a test function on `M`, `u : P` is an element of `U_w⁺`,
  and `d : H` is a diagonal parameter.

Write `χ = standardCharacterContinuous ψ n` and
`ι = Subgroup.inclusion (permutationUnipotentPlus_le_upperUnipotent (n + 1) F.Carrier w)`,
the actual inclusion homomorphism `P → U`. The proposition asserts the equality of
complex numbers

    SchwartzBruhat.characterAverage χ μ
        (Hecke.TestFunction.pullback (bruhatFiberActHomeomorph (n + 1) F.Carrier w u) α) d
      = (compatibilityDefect ψ n w (ι u) d)⁻¹ *
          SchwartzBruhat.characterAverage χ μ α d.

Both averages are evaluated at the same point `d`, and the multiplier is the inverse
of the published compatibility defect. Because the multiplier depends on `d`, the
statement is pointwise in `d`, not an equality of test functions up to a scalar.

Written out with the evaluation laws of the imported definitions, the equality says

    ∫ z : U × U, α (bruhatFiberAct (n + 1) F.Carrier w u (z.1, (d, z.2))) *
          ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ)
      = (compatibilityDefect ψ n w (ι u) d)⁻¹ *
          ∫ z : U × U, α (z.1, (d, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ).

By the conventions below, the point `bruhatFiberAct (n + 1) F.Carrier w u (z.1, (d, z.2))`
is `(z.1 * g, (d, ι u * z.2))`, where `g ∈ U` is the element with underlying matrix
`s * u⁻¹ * s⁻¹` for `s = p_w * h(d)`. This expanded form describes what the statement
means; it is not a separate declaration.

## Exact meaning of the imported objects

- `SchwartzBruhat X`, from `Langlands.HarmonicAnalysis.Basic`, is the complex vector
  space of locally constant, compactly supported functions `X → ℂ`.
- `standardCharacterContinuous ψ n`, from
  `Langlands.Representation.Whittaker.GeneralLinear`, is the published standard
  character `standardCharacter ψ n` bundled as a continuous homomorphism `U → ℂˣ`.
  Its value at `g` is `ψ` applied to `∑ i : Fin n, g i.castSucc i.succ`, the sum of the
  first-superdiagonal entries of `g`, viewed in `ℂ`. For `n = 0` the sum is empty and
  the character is trivial.
- `SchwartzBruhat.characterAverage χ μ`, from
  `Langlands.HarmonicAnalysis.Distribution.CharacterAverage`, is the published complex
  linear map `SchwartzBruhat (U × (H × U)) →ₗ[ℂ] SchwartzBruhat H`. By
  `characterAverage_apply`,

      characterAverage χ μ β y =
        ∫ z : U × U, β (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ).

  The integral is over two copies of `U` with the product measure `μ.prod μ`, and the
  weight is the inverse of both character values.
- `bruhatFiberActHomeomorph (n + 1) F.Carrier w u`, from
  `Langlands.Representation.Whittaker.BruhatFiberAverage`, is the homeomorphism
  `M ≃ₜ M` given by `m ↦ bruhatFiberAct (n + 1) F.Carrier w u m`
  (`bruhatFiberActHomeomorph_apply`).
- `Hecke.TestFunction.pullback e`, from `Langlands.Representation.Hecke.TestFunction`,
  is the published complex linear equivalence attached to a homeomorphism `e`. By
  `pullback_apply` it evaluates as `pullback e β x = β (e x)`, not `β (e.symm x)`. So
  the pulled-back function is `m ↦ α (u • m)`, which is Shalika's `α^u`.
- `compatibilityDefect ψ n w v d`, from
  `Langlands.Representation.Whittaker.CompatibleTorus`, is defined for every `v : U`
  as

      ψ.complex (∑ i : Fin n, (s * v.val * s⁻¹) i.castSucc i.succ) * (χ v : ℂ)⁻¹,

  with `s = p_w * h(d)`. Its argument here is `ι u`, the image of `u` under the actual
  inclusion, not an arbitrary element of `U`. Because `u ∈ P`, the published
  `compatibilityDefect_eq_div` applies and rewrites the defect as the quotient
  `χ(s u s⁻¹) / χ(u)` of two actual character values.

## Conventions

**Products.** Lean's product is right-associated: a point of `M` is
`m = (u₁, (d, u₂))`, with `m.1 = u₁`, `m.2.1 = d` and `m.2.2 = u₂`. It corresponds to
Shalika's point `(u₁, h, u₂)` of `M₁ = U × H × U`.

**Matrices.** `p_w = GeneralLinear.permutation (n + 1) F.Carrier w` is the published
permutation matrix sending `e_j` to `e_(w j)`; it is Shalika's matrix `w`.
`h(d) = GeneralLinear.Iwasawa.diagonalUnits d` is the diagonal matrix with entries
`d i`. The diagonal factor stands to the right of the permutation matrix:
`s = p_w * h(d)` is Shalika's `w h`, and the cell map is
`(u₁, d, u₂) ↦ u₁ * p_w * h(d) * u₂`.

**Action.** `bruhatFiberAct (n + 1) F.Carrier w u` sends `(u₁, (d, u₂))` to

    (u₁ * p_w * h(d) * u⁻¹ * h(d)⁻¹ * p_w⁻¹, (d, ι u * u₂)).

The first component is a product in `Langlands.GeneralLinear (n + 1) F.Carrier`,
bundled in `U` by the published membership lemma; it equals `u₁ * g` with `g` the
element of `U` whose matrix is `s * u⁻¹ * s⁻¹`. The middle coordinate is unchanged.
The last component is the product in `U` of `ι u` and `u₂`. This is Shalika's action
`u * m = (u₁ w h u⁻¹ h⁻¹ w⁻¹, h, u u₂)`. So the action translates the first `U` factor
on the RIGHT by a `d`-dependent monomial conjugate of `u⁻¹`, and the last `U` factor on
the LEFT by `u`.

**Topologies and measure.** `F.Carrier` carries the topology of the installed norm,
`Langlands.GeneralLinear (n + 1) F.Carrier` the topology of the units of the matrix
ring, `U` and `P` the subspace topology, `F.Carrierˣ` the units topology, `H` the
product topology and `M` the product topology. `U` carries its Borel σ-algebra, and `μ`
lives on `U`. No measure on `P` enters: unlike Shalika's formula (1.11), this statement
does not integrate over the orbit.

## The sign

The following explains the stated multiplier. It is not a Lean proof; the proof
`bruhatFiberCharacterCovariance` in the companion module establishes the multiplier.

Shalika computes, in the proof of Proposition 1.13 (printed p.177), for `h ∈ H` and
`u ∈ U_w⁺`,

    β_{α^u}(h) = ∫_{U×U} α(u₁ w h u⁻¹ h⁻¹ w⁻¹, h, u u₂) χ̄(u₁u₂) du₁ du₂
               = χ(w h u⁻¹ h⁻¹ w⁻¹) χ(u) β_α(h),

and calls the multiplier `δ(h) = χ(w h u⁻¹ h⁻¹ w⁻¹) χ(u)`. With `s = p_w * h(d)` this is
`χ(s u⁻¹ s⁻¹) χ(u)`. The published defect is `χ(s u s⁻¹) / χ(u)` on `U_w⁺`. Since `χ`
is a homomorphism, `χ(s u⁻¹ s⁻¹) = χ(s u s⁻¹)⁻¹`, so

    χ(s u⁻¹ s⁻¹) χ(u) = (χ(s u s⁻¹) / χ(u))⁻¹ = (compatibilityDefect ψ n w (ι u) d)⁻¹.

Thus the multiplier of the proposition is exactly Shalika's `δ`, and it is the INVERSE
of the defect, not the defect itself. For the unitary character `χ`, Shalika's
`χ̄(u₁u₂)` is the weight `(χ u₁ * χ u₂)⁻¹` of `characterAverage`.

## Proof route (proved in the companion module)

The following route was recorded with the statement to explain the hypotheses. It is
not carried out in this module. The proof `bruhatFiberCharacterCovariance` in the
companion module follows it; its Markdown, `BruhatFiberCharacterCovarianceProof.md`,
describes the implemented argument.

Fix `d` and let `g ∈ U` have matrix `s * u⁻¹ * s⁻¹`. The left side is the integral of
`α (z.1 * g, (d, ι u * z.2)) * (χ z.1 * χ z.2)⁻¹` over `z ∈ U × U`. Make two changes of
variables in the outer `U` integrals:

1. `v₁ = z.1 * g` in the first factor, a right translation. It preserves `μ` by right
   invariance.
2. `v₂ = ι u * z.2` in the last factor, a left translation. It preserves `μ` by left
   invariance.

The map `(z.1, z.2) ↦ (z.1 * g, ι u * z.2)` then preserves `μ.prod μ`, because a product
of measure-preserving maps preserves the product of s-finite measures. Translations are
measurable because `U` is a topological group with its Borel σ-algebra. Since
`z.1 = v₁ * g⁻¹` and `z.2 = (ι u)⁻¹ * v₂`, multiplicativity of `χ` in the commutative
field `ℂ` gives

    (χ z.1 * χ z.2)⁻¹ = χ g * χ (ι u) * (χ v₁ * χ v₂)⁻¹.

The constant `χ g * χ (ι u) = χ(s u⁻¹ s⁻¹) χ(u)` is the inverted defect computed above,
and the remaining integral is `characterAverage χ μ α d`. The proof uses the Mathlib
tools `measurePreserving_mul_right`, `measurePreserving_mul_left`,
`MeasurePreserving.prod` and `MeasurePreserving.integral_comp'`, with
`compatibilityDefect_eq_div` for the multiplier.

This uses each invariance once and on a different factor than the generic
covariance proposition `Langlands.HarmonicAnalysis.SchwartzBruhat.CharacterAverageCovarianceStatement`
(proved by the published `characterAverageCovariance`), which translates the first
factor on the left and the last factor on the right by constants. The present action
translates the first factor on the right by a `d`-dependent element. Neither this
statement nor its proof assumes or uses that generic result.

## Hypotheses: internal derived generality

Shalika integrates against a Haar measure on the unimodular group `U`. The hypotheses
on `μ` here are instead the explicit, independent conditions that the proof's change
of variables uses: s-finiteness (for the product measure and its change of variables),
finiteness on compact sets (required by the imported `characterAverage`), left
invariance and right invariance. This choice is internal derived generality, not part
of the source. Later proofs that apply the proposition to an actual p-adic Haar measure
on `U` must discharge these hypotheses for that measure and for the topology installed
here; this unit does not do so, and the final Shalika statement is not to contain
them.

No Haar, local compactness, countability or unimodularity hypothesis appears. No
covariance, invariance, support, geometry or distribution-classification statement is
a premise.

## Scope

This module is a statement only. It proves no covariance: the equality above is the
conclusion of the proposition, which is proved by `bruhatFiberCharacterCovariance` in
the companion module. This module also states and proves nothing about:

- the support of `τ` or of any distribution (Shalika's Proposition 1.13 itself);
- orbital descent from `M` to the cell, or the function `f_α` of Lemma 1.10 and (1.11);
- surjectivity of `α ↦ characterAverage χ μ α`;
- factorization of a distribution through `characterAverage` (Proposition 1.12);
- invariance of distributions on a single cell or on the whole group (Proposition 1.8,
  Theorem 1.6), or multiplicity one.

## Provenance

The source is J. A. Shalika, *The multiplicity one theorem for GL_n*, Ann. of Math. (2)
**100** (1974), 171–193, registered as `shalika-1974-multiplicity-one` (central file
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`,
SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`). Printed
pp.176–177 are one-based PDF pages 7–8.

- **Printed p.176 (PDF page 7).** The space `M₁ = U × H × U`, the map
  `π(u₁, h, u₂) = u₁ w h u₂`, and the action
  `u * m = (u₁ w h u⁻¹ h⁻¹ w⁻¹, h, u u₂)` of `U_w⁺`, followed by formula (1.11).
- **Printed p.177 (PDF page 8).** Proposition 1.12 defines
  `β_α(h) = ∫_{U×U} α(u₁, h, u₂) χ̄(u₁u₂) du₁ du₂`. In the proof of Proposition 1.13
  Shalika sets `α^u(m) = α(u * m)` and derives the displayed formula for `β_{α^u}(h)`
  with multiplier `χ(w h u⁻¹ h⁻¹ w⁻¹) χ(u)`. Worker 884 checked this page visually.

The present proposition is that computation, with `β_α` the published
`characterAverage`, `α^u` the published pullback along the published fiber action, and
the multiplier expressed through the published defect. The exact Lean form, with an
arbitrary measure under explicit hypotheses and the defect in place of Shalika's `δ`,
is internal derived content and not a verbatim statement of the paper. The project's
literature notes record no errata for this paper, and none was found for these pages.

## Consumers

The proposition is an intermediate target for the exact Shalika distribution-invariance
work (task `f79ca82c-d050-4ffa-821b-c347b60e36e0`, Worker 634) and, through it, the
Whittaker multiplicity-one work (task `209cde88-bab8-4a85-8a9d-72b8864b6fa0`). It
proves neither. Its proof `bruhatFiberCharacterCovariance` is used by the published
proof `Langlands.Whittaker.bruhatCompatibleSupport` of
`BruhatCompatibleSupportStatement`.
