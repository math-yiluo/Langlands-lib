# Translation covariance of character-weighted product averaging

`Langlands.HarmonicAnalysis.SchwartzBruhat.CharacterAverageCovarianceStatement.{uG, uY}`
is the following unproved proposition. This module defines the proposition and
supplies no proof. Its only import is the published module
`Langlands.HarmonicAnalysis.Distribution.CharacterAverage`, used unchanged.

## Statement

Everything below is universally quantified inside the proposition. The two
universes `uG` and `uY` are independent and arbitrary, and they are the only
parameters of the definition.

- `G : Type uG` is a group (`Group G`) with a topology (`TopologicalSpace G`)
  making it a topological group (`IsTopologicalGroup G`). It carries a
  measurable structure `[MeasurableSpace G]` that is its Borel σ-algebra
  (`[BorelSpace G]`).
- `Y : Type uY` is a topological space (`TopologicalSpace Y`). No measurable
  structure on `Y` is used.
- `χ : ContinuousMonoidHom G ℂˣ` is a continuous character with values in the
  units of `ℂ`. It need not be unitary.
- `μ : Measure G` is s-finite (`SFinite μ`), finite on compact sets
  (`IsFiniteMeasureOnCompacts μ`), left invariant (`μ.IsMulLeftInvariant`) and
  right invariant (`μ.IsMulRightInvariant`). Both invariance hypotheses are
  assumed separately; neither is derived from the other.
- `a b : G` are arbitrary, and `α : SchwartzBruhat (G × (Y × G))` is an
  arbitrary test function on the right-associated triple product.

Let `e` be the homeomorphism of `G × (Y × G)` given by

    e = (Homeomorph.mulLeft a).prodCongr
          ((Homeomorph.refl Y).prodCongr (Homeomorph.mulRight b)),

so `e (g₁, (y, g₂)) = (a * g₁, (y, g₂ * b))`. The proposition asserts the
equality of test functions on `Y`

    SchwartzBruhat.characterAverage χ μ (Hecke.TestFunction.pullback e α) =
      ((χ a : ℂ) * (χ b : ℂ)) • SchwartzBruhat.characterAverage χ μ α.

The scalar on the right is the product of the character values `χ a` and
`χ b`, neither of them inverted. `•` is the complex scalar multiplication of
`SchwartzBruhat Y`, so the equality means that, for every `y : Y`,

    ∫ z : G × G, α (a * z.1, (y, z.2 * b)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ)
      = (χ a : ℂ) * (χ b : ℂ) *
          ∫ z : G × G, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ).

## Exact meaning of the imported objects

- `SchwartzBruhat X`, from `Langlands.HarmonicAnalysis.Basic`, is the complex
  vector space of locally constant, compactly supported functions `X → ℂ`.
- `SchwartzBruhat.characterAverage χ μ`, from
  `Langlands.HarmonicAnalysis.Distribution.CharacterAverage`, is the published
  complex linear map `SchwartzBruhat (G × (Y × G)) →ₗ[ℂ] SchwartzBruhat Y`. Its
  evaluation law `characterAverage_apply` is

      characterAverage χ μ α y =
        ∫ z : G × G, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ).

  The integrand keeps the inverse of both character values. The map needs a
  monoid `G` with a topology, a measurable structure in which open sets are
  measurable, and `[SFinite μ] [IsFiniteMeasureOnCompacts μ]`. The Borel
  structure assumed here supplies the open-set measurability.
- `Hecke.TestFunction.pullback e`, from
  `Langlands.Representation.Hecke.TestFunction`, is the published complex
  linear equivalence `SchwartzBruhat Y' ≃ₗ[ℂ] SchwartzBruhat X'` attached to a
  homeomorphism `e : X' ≃ₜ Y'`. By `pullback_apply` it evaluates as
  `pullback e f x = f (e x)`, not `f (e.symm x)`. Here `X' = Y' = G × (Y × G)`.
- `Homeomorph.mulLeft a` is `g ↦ a * g`, `Homeomorph.mulRight b` is
  `g ↦ g * b`, `Homeomorph.refl Y` is the identity, and `Homeomorph.prodCongr`
  acts coordinatewise. So the pulled-back function is
  `(g₁, (y, g₂)) ↦ α (a * g₁, (y, g₂ * b))`: a left translation in the first
  factor, a right translation in the last factor, and nothing in the middle.

The translation is written out with these Mathlib homeomorphisms and the
published pullback; no abstract action data, helper abbreviation or
substitute test-function space is introduced.

## The sign from the change of variables

The following explains why the stated scalar is `χ a * χ b`; it is not proved
here. Fix `y`. The left side is the integral of
`α (a * g₁, (y, g₂ * b)) * (χ g₁ * χ g₂)⁻¹` over `(g₁, g₂)`. Substitute
`h₁ = a * g₁` and `h₂ = g₂ * b`, that is `g₁ = a⁻¹ * h₁` and `g₂ = h₂ * b⁻¹`.
Because `χ` is multiplicative,

    χ g₁ = (χ a)⁻¹ * χ h₁   and   χ g₂ = χ h₂ * (χ b)⁻¹,

so the inverse weight becomes

    (χ g₁ * χ g₂)⁻¹ = χ a * χ b * (χ h₁ * χ h₂)⁻¹

in the commutative field `ℂ`. The inverse in the weight turns the inverted
translation parameters `a⁻¹` and `b⁻¹` back into the plain values `χ a` and
`χ b`. Neither factor ends up inverted.

The substitution leaves the measure unchanged. The map
`(g₁, g₂) ↦ (a * g₁, g₂ * b)` preserves `μ.prod μ`, because left translation
by `a` preserves `μ` (left invariance, used on the first factor only) and right
translation by `b` preserves `μ` (right invariance, used on the second factor
only). A product of measure-preserving maps preserves the product measure for
s-finite measures; this is one use of `SFinite μ`. The Borel structure makes
both translations measurable. After the substitution the integral is
`χ a * χ b` times the integral defining `characterAverage χ μ α y`. A private
check confirmed that the proposition is provable along exactly this route, by
Mathlib's `measurePreserving_mul_left`, `measurePreserving_mul_right`,
`MeasurePreserving.prod` and `MeasurePreserving.integral_comp'`; that proof is
not part of this unit.

The sign agrees with the published convention for bi-equivariant
distributions. Shalika's condition (see Provenance) is
`T(L_{u₁⁻¹} R_{u₂} f) = χ(u₁u₂) T(f)` with `(L_x f)(m) = f(x⁻¹ m)` and
`(R_x f)(m) = f(m x)`. Thus `L_{u₁⁻¹} R_{u₂} α` is
`(v₁, h, v₂) ↦ α (u₁ v₁, h, v₂ u₂)`, which is `pullback e α` for `a = u₁` and
`b = u₂`. The present proposition says that the average transforms by the
same factor `χ(u₁) χ(u₂) = χ(u₁ u₂)`.

## Hypotheses that are deliberately absent

- No Haar measure hypothesis, local compactness, Hausdorff property,
  countability (second countability or σ-compactness), total disconnectedness
  or non-archimedean field appears. Besides the topological group structure and
  Borel σ-algebra of `G`, only the invariance, s-finiteness and finiteness on
  compact sets of `μ` are assumed.
- Right invariance is an explicit hypothesis. It is never inferred from left
  invariance, since a nonzero left Haar measure on a non-unimodular group is
  not right invariant.
- `G` is not assumed commutative, and `χ` is not assumed unitary.
- Neither the desired equality nor any invariance property of distributions
  is assumed.

## The upper-unipotent p-adic application

The intended application, which this unit does not carry out, is the published
specialization `standardCharacterAverage F n ψ μ` of the imported module. There
`F : PadicField p` is an actual p-adic field with carrier `K = F.Carrier` and
its canonical topological data, `G` is the upper unipotent subgroup
`upperUnipotent (n + 1) K` of `GL_{n+1}(K)` with the Borel structure
`borel (upperUnipotent (n + 1) K)`, `Y = Fin (n + 1) → Kˣ`, and the character
is the continuous standard character `standardCharacterContinuous ψ n`; the
specialization is by definition
`characterAverage (standardCharacterContinuous ψ n) μ`. The natural measure is
`μ = Langlands.RankinSelberg.unipotentHaar K n`, with the instances of `K`
installed from `F.canonicalTopologicalData`. It meets the hypotheses for these
reasons.

- **Left invariance and finiteness on compact sets.** `unipotentHaar K n`
  (module `Langlands.Representation.RankinSelberg.Measures`) is a left Haar
  measure normalized on the integral unipotent subgroup. The published instance
  `unipotentHaar_isHaar` makes it a Haar measure, and every Haar measure is left
  invariant and finite on compact sets.
- **Right invariance.** The published instance
  `unipotentHaar_isMulRightInvariant`, in
  `Langlands.Representation.RankinSelberg.UnipotentUnimodularity`, supplies
  `IsMulRightInvariant (unipotentHaar K n)`. Its proof
  `unipotentHaar_rightInvariant` is intrinsic to the unipotent group: every
  element lies in a compact open subgroup, and right translation by an element
  of a compact open subgroup preserves the measure. This is a theorem about this
  particular group, not a generic consequence of left invariance.
- **s-finiteness.** For the actual p-adic topologies, the second countability
  and σ-compactness of `GL_{n+1}(K)` are published in
  `Langlands.Group.GL.CountabilityProof` (the certificates
  `TopologicalData.generalLinearSecondCountableTopology` and
  `TopologicalData.generalLinearSigmaCompactSpace`, collected in
  `Langlands.PadicField.matrixGroupCountability`). Library proofs pass second
  countability to the subgroup with
  `TopologicalSpace.Subtype.secondCountableTopology`. The subgroup is closed,
  hence locally compact (`GeneralLinear.UpperUnipotent.locallyCompactSpace`),
  and a locally compact second-countable space is σ-compact. A measure that is
  finite on compact sets of a σ-compact space is σ-finite, hence s-finite.

## Scope

This is a statement only. It proves no covariance: the equality above is the
conclusion of an unproved proposition, whose proof is a separate task. The unit
also states and proves nothing about:

- surjectivity of the averaging map `α ↦ characterAverage χ μ α`;
- factorization of a bi-equivariant distribution on `G × (Y × G)` through
  `characterAverage`, or the uniqueness of the factoring distribution on `Y`;
- descent from Bruhat cells or any support statement for distributions;
- Shalika's distribution invariance (Theorem 1.6, Propositions 1.8 and 1.12),
  or multiplicity one.

The specialization of the proposition to the upper unipotent group is not
stated in Lean here either.

## Provenance

The generic formulation, with an arbitrary topological group `G`, an arbitrary
space `Y`, a not necessarily unitary character and an explicitly left- and
right-invariant s-finite measure, is internal derived content. It records the
elementary change of variables underlying the averaging map, and its precise
hypotheses come from that change of variables, not from a source statement.
It is not a transcription of a statement of Shalika.

The motivating source is J. A. Shalika, *The multiplicity one theorem for
GL_n*, Ann. of Math. (2) **100** (1974), 171–193, registered as
`shalika-1974-multiplicity-one` (central file
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`,
SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`).
No errata for these pages are recorded in the project's notes.

- **Printed p.174 (PDF page 5).** The translation conventions
  `(L_x f)(y) = f(x⁻¹y)` and `(R_x f)(y) = f(yx)`.
- **Printed p.175 (PDF page 6), Proposition 1.8.** The bi-equivariance
  condition `T(L_{u₁⁻¹} R_{u₂} f) = χ(u₁u₂) T(f)` for distributions on a cell.
- **Printed p.177 (PDF page 8), Proposition 1.12.** For `T*` on
  `M₁ = U × H × U` with `T*(L_{u₁⁻¹} R_{u₂} α) = χ(u₁u₂) T*(α)`, Shalika defines
  `β_α(h) = ∫ α(u₁, h, u₂) χ̄(u₁u₂) du₁ du₂`, asserts that `α ↦ β_α` is
  surjective, and asserts that `T* = τ ∘ β` for a unique distribution `τ` on
  `H`. The action on `M₁` is `(u₁, u₂) ∘ m = u₁ m u₂⁻¹`, and the proof is
  omitted there.

The correspondence is that of the imported module: `G`, `Y` and `μ` play the
roles of `U`, `H` and Haar measure on `U`, the point `(z.1, (y, z.2))` is
`(u₁, h, u₂)`, and `characterAverage χ μ α` is `β_α`. For a unitary character
the inverse weight `(χ z.1 * χ z.2)⁻¹` is Shalika's `χ̄(u₁u₂)`. Shalika does not
state the transformation law of `β_α` under these translations. It is the
property that makes a factorization `T* = τ ∘ β` compatible with the
equivariance of `T*`: if `β` multiplies by `χ(u₁u₂)`, then so does `τ ∘ β`.
The present proposition isolates that property. On a unipotent group Haar
measure is both left and right invariant, which is why the source can use a
single Haar measure on each factor.

## Consumers

The proposition is intended for the exact Shalika distribution-invariance work
(task `f79ca82c-d050-4ffa-821b-c347b60e36e0`) and, through it, the Whittaker
multiplicity-one work (task `209cde88-bab8-4a85-8a9d-72b8864b6fa0`). A separate
proof task for this proposition follows its publication.
