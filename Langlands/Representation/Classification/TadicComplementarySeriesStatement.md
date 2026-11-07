# Complementary series of `GL_n`: unitarity and length bounds

Author: Worker 1809. This pair states Tadic 1986 Propositions 2.9, 2.10(i)
and 2.10(ii) as Prop-valued definitions. **None of these assertions is proved
here.** The module has no axioms, no `sorry`, and no structure field assuming
the existence of anything. Its one theorem,
`SpehDatum.complementaryInduced_eq_complementaryProduct`, holds by `rfl`. It
only identifies two constructions and is not a source assertion.

All new names lie in `Langlands.Classification`, in module
`Langlands.Representation.Classification.TadicComplementarySeriesStatement`.

## Sources

- **Tadic 1986** (`tadic-1986-unitary`), Ann. Sci. ENS (4) 19, 335–382;
  PDF page = printed page − 333.
  - Proposition 2.9: §2.9, printed p.350 (PDF p.17).
  - Proposition 2.10(i): §2.10, p.350 (PDF p.17).
  - Proposition 2.10(ii): §2.10, pp.350–351 (PDF pp.17–18).
  - Conventions: §1.1 p.340 (`×` is the induction functor
    `(π₁, π₂) ↦ π₁ × π₂`); §1.2 p.340 (`G̃_n` is the set of irreducible smooth
    classes, `Ĝ_n` the unitarizable ones); §1.3 p.341 (`ν = |det|_F`,
    `|ϖ|_F = q⁻¹`); §1.6 p.342 (`π_α = ν^α π`); §2.1 p.345 (`π⁺`, the
    Hermitian contragredient).
- **Bernstein 1984** (`bernstein-1984-p-invariant`), LNM 1041, pp.50–102;
  PDF page = printed page − 49. Proposition 8.3 and its Remark, printed
  pp.89–90 (PDF pp.40–41). Tadic derives both propositions from these.

## Parameters and conventions

The parameters are an arbitrary prime `p` with `[Fact p.Prime]`,
`F : PadicField.{uF} p` and `T : F.TopologicalData`. The field universe `uF`
and the representation universe `uV` are independent. Every representation is
an actual smooth complex representation
`SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)`, with
`letI := T.topology`. This is the carrier universe of
`TadicUnitaryDualExhaustion`. No admissibility or finite-dimensionality
condition is imposed.

- *Irreducible* is Mathlib's `Representation.IsIrreducible`: the lattice of
  subrepresentations is simple, so the representation is nonzero and has no
  proper nonzero subrepresentation.
- *Unitarizable* is the Library's `IsUnitarizable`: some positive definite
  Hermitian form on the carrier is preserved by the actual action (Tadic §1.2:
  "possesses a `G_n`-invariant inner product").
- A *composition factor* of `π` is an irreducible `τ` with the published
  `SmoothRep.IsSubquotient τ π`. This means `τ` is isomorphic to `S / S'` for
  an actual subrepresentation `S` of `π` and an actual subrepresentation `S'`
  of `S`. The statements quantify over every such `τ` in the same carrier
  universe. They do not assert that `π` has finite length.

## The complementary product `complementaryProduct F T hn σ α`

For `n` with `hn : 0 < n`, a representation `σ` of `GL_n(F)` and `α : ℝ`,
`complementaryProduct F T hn σ α` is the representation of `GL_(2n)(F)`

```
T.twistedProductInduced (GeneralLinear.BlockShape.uniform 2 n hn) (fun _ => σ)
  (fun i => if (i : ℕ) = 0 then α else -α)
```

This is `π(σ, α) = ν^α σ × ν^(-α) σ`. It is normalized parabolic induction
from the standard upper block parabolic with two diagonal blocks of size `n`,
applied to the block family `(ν^α σ, ν^(-α) σ)` in that order. The twist
`ν^s σ = σ ⊗ |det|_F^s` is the published `T.segmentFactor`. Both blocks use
the very same `σ`, not an independently chosen isomorphic copy or a
contragredient. In Tadic's notation this is `σ_α × σ_(-α)`.

The construction is exactly `SpehDatum.complementaryInduced` of
`Classification.TadicUnitaryStatement`, but for an arbitrary `σ`. The theorem
`SpehDatum.complementaryInduced_eq_complementaryProduct` records this by
`rfl`. For a datum `d`, `d.complementaryInduced S α` equals
`complementaryProduct F T (Nat.mul_pos d.length_pos d.rank_pos) S α`.

## Proposition 2.9: `ComplementarySeriesUnitarity F T`

Tadic p.350: "Let `σ ∈ Ĝ_n`. Suppose that `σ_α × σ_(-α)` is irreducible for
`α ∈ (−α₀, α₀)`, `α₀ > 0`. Then `σ_α × σ_(-α)` is unitarizable for
`α ∈ (−α₀, α₀)` and all composition factors of `σ_(α₀) × σ_(−α₀)` are
unitarizable." Tadic proves it from Bernstein's Proposition 8.3, Tadic
Theorem 2.7 and Lemma 2.8.

Lean: take `n`, `hn : 0 < n`, `σ` and `α₀ : ℝ` with `σ` irreducible and
unitarizable and `0 < α₀`. Suppose `complementaryProduct F T hn σ α` is
irreducible for every `α ∈ Set.Ioo (-α₀) α₀`. Then:

- it is unitarizable for every such `α`;
- every irreducible `τ` of `GL_(2n)(F)` with
  `SmoothRep.IsSubquotient τ (complementaryProduct F T hn σ α₀)` is
  unitarizable.

## Proposition 2.10(i): `ComplementarySeriesIrreducibilityNearZero F T`

Tadic p.350: "If `σ ∈ Ĝ_n` then there exists `α₀ > 0` such that
`σ_α × σ_(-α)` is irreducible for `α ∈ (−α₀, α₀)`."

Lean: for every `n`, `hn : 0 < n` and irreducible unitarizable `σ`, there is
`α₀ : ℝ` with `0 < α₀` such that `complementaryProduct F T hn σ α` is
irreducible for every `α ∈ Set.Ioo (-α₀) α₀`.

## Proposition 2.10(ii): `ComplementarySeriesLengthBound F T`

Tadic pp.350–351: "Let `σ ∈ G̃_n` with `n ≥ 1`. Suppose that
`σ_α × (σ⁺)_(−α)` is unitarizable and irreducible for `α ∈ (β, γ)`,
`β < γ`. Then `γ − β ≤ 1`. If `γ − β = 1` then `σ_β × (σ⁺)_(−β)` and
`σ_γ × (σ⁺)_(−γ)` reduce." Tadic proves the bound from Bernstein's
Proposition 8.3 and its Remark. He proves the reducibility from Proposition
2.9, the first part of (ii), and the closedness of the set of `α` at which
`σ_α × (σ⁺)_(−α)` is reducible.

Lean: take `n`, `hn : 0 < n`, an irreducible unitarizable `σ` and reals
`β < γ`. Suppose `complementaryProduct F T hn σ α` is irreducible and
unitarizable for every `α ∈ Set.Ioo β γ`. Then `γ - β ≤ 1`. If `γ - β = 1`,
then neither `complementaryProduct F T hn σ β` nor
`complementaryProduct F T hn σ γ` is irreducible. Here "reduces" means "is not
irreducible".

**Why `σ` appears in both factors.** In Tadic's §2.1 (p.345), `σ⁺` is the
Hermitian contragredient: the complex conjugate of the contragredient of `σ`.
Tadic notes there that every unitarizable admissible representation is
Hermitian, `σ⁺ ≅ σ`. For an irreducible unitarizable `σ` (irreducible smooth
representations are admissible, §1.2) this gives `(σ⁺)_(−α) ≅ σ_(−α)` for
every `α`. Normalized induction of isomorphic block families gives isomorphic
representations (the Library's `twistedProductInducedIso`). So
`σ_α × (σ⁺)_(−α) ≅ σ_α × σ_(−α)`, and irreducibility and unitarizability are
invariant under isomorphism. Every hypothesis and conclusion of Tadic's
2.10(ii) for such `σ` is therefore the corresponding clause with `σ` in both
blocks, which is what the Lean states.

This is only the **unitarizable case** of Tadic's 2.10(ii). The source allows
any `σ ∈ G̃_n`, so this statement is weaker than the source in that respect.
This is the case the task asks for. Bernstein's Proposition 8.3 (p.89) uses the same product,
`π(σ, α) = ν^α σ × ν^(−α) σ⁺ = (ν^α σ) × (ν^α σ)⁺`, for irreducible `σ`. His
proposition says that `π(σ, α)` is irreducible and unitarizable on the
interval `I(σ)` and reducible on its boundary. The Remark (p.90) bounds the
length of `I(σ)` by 1 when `σ` is not the trivial representation of `G_0`.
The hypothesis `0 < n` corresponds to Tadic's `n ≥ 1` and excludes that case.
It is also needed to form `BlockShape.uniform 2 n hn`.

## Conjunctions

- `TadicComplementarySeriesStatements F T` is the conjunction of the three
  statements above for the fixed `F` and `T`.
- `PadicTadicComplementarySeriesStatements.{uF, uV}` quantifies that
  conjunction over every prime `p`, every `F : PadicField.{uF} p` and every
  `T : F.TopologicalData`.

## Scope

- Nothing is proved here. Each statement is a separate target for a later
  proof task.
- 2.9 and 2.10(i) take `0 < n` because the two-block shape needs positive
  block size. For `n = 0` the source assertions are trivial.
- 2.10(ii) for irreducible `σ` that are not unitarizable, with `σ⁺` in the
  second block, is not stated.
- No finite-length, admissibility, or Grothendieck-group assertion about
  `π(σ, α)` is made. Composition factors are only the irreducible actual
  subquotients described above.
